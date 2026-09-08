#!/usr/bin/env python3
"""Derive and verify the Lean audit payload modules from the legacy shell heredocs.

Before commit ``LEGACY_REF`` the audit scripts
``scripts/{axiom,root_import,semantic_surface,completion}_audit.sh`` carried their Lean
check payloads inside ``<<'EOF'`` heredocs that were re-elaborated on every run.  The
refactored layout keeps those payloads as checked-in Lean modules under
``audit/PoincareAudit`` (a non-default ``lean_lib``), so ``lake build PoincareAudit``
elaborates them once and caches the result.

This tool is the lossless-extraction proof:

* ``--write`` regenerates the modules from the heredocs of a git revision (heredoc
  ranges are located by their ``<<'EOF'`` / ``EOF`` markers, never by hand);
* ``--check`` (default) re-extracts the same heredocs and asserts that the ordered
  sequence of checked declarations/ascriptions in each module is exactly the legacy
  sequence, that the module header (``import``/``open``/``set_option``/``universe``
  lines) is the legacy header, and that the module contains nothing else.

Conversion rules (one line per legacy command, so diffs stay one-name-per-line):

* ``#check X``           -> ``#guard_msgs (drop info, drop warning) in #check X``
  (fails the build iff ``#check X`` reports an error, exactly the legacy
  ``lake env lean`` exit-code contract; info replay is suppressed);
* ``#print axioms X``    -> ``#std_axioms X`` (``audit/PoincareAudit/Guard.lean``: errors
  unless the axiom closure is within ``{propext, Classical.choice, Quot.sound}``).

Only ``git``, ``python3`` and the standard library are required.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEGACY_REF = "b2b96fc28248c2a72cb2e08b4fda946d3b26e6d5"

GUARD_PREFIX = "#guard_msgs (drop info, drop warning) in "
LEGACY_SCRIPTS = ("axiom_audit", "root_import_audit", "semantic_surface_audit", "completion_audit")

# (script, heredoc index within the script) -> logical block name.
BLOCKS = {
    ("axiom_audit", 0): "axiom.routes",
    ("axiom_audit", 1): "axiom.main",
    ("root_import_audit", 0): "root.main",
    ("semantic_surface_audit", 0): "semantic.routes",
    ("semantic_surface_audit", 1): "semantic.main",
    ("completion_audit", 0): "completion.routes",
    ("completion_audit", 1): "completion.root",
    ("completion_audit", 2): "completion.dependency",
    ("completion_audit", 3): "completion.reserved",
}

# Module path (relative to audit/) -> ordered list of legacy blocks it holds.
MODULES = {
    "PoincareAudit/Axiom/Footprint.lean": ["axiom.main", "axiom.routes"],
    "PoincareAudit/Root/Contracts.lean": ["root.main"],
    "PoincareAudit/Semantic/Surface.lean": ["semantic.main"],
    "PoincareAudit/Semantic/CertificateRoutes.lean": ["semantic.routes"],
    "PoincareAudit/Completion/RootContract.lean": ["completion.root"],
    "PoincareAudit/Completion/DependencyContract.lean": ["completion.dependency"],
    "PoincareAudit/Completion/CertificateRoutes.lean": ["completion.routes"],
}

MODULE_DOC = {
    "PoincareAudit/Axiom/Footprint.lean": (
        "Axiom footprint surface (legacy `scripts/axiom_audit.sh` heredocs: main block then\n"
        "the canonical certificate-route block).  Every `#std_axioms` line fails the build\n"
        "unless the declaration exists and its axiom closure is within\n"
        "{propext, Classical.choice, Quot.sound}."
    ),
    "PoincareAudit/Root/Contracts.lean": (
        "Root import contract surface (legacy `scripts/root_import_audit.sh` heredoc)."
    ),
    "PoincareAudit/Semantic/Surface.lean": (
        "Semantic surface contract checks (legacy `scripts/semantic_surface_audit.sh` main heredoc)."
    ),
    "PoincareAudit/Semantic/CertificateRoutes.lean": (
        "Certificate route projection checks required by the semantic surface audit\n"
        "(legacy `append_certificate_route_projection_contract_checks` in\n"
        "`scripts/semantic_surface_audit.sh`)."
    ),
    "PoincareAudit/Completion/RootContract.lean": (
        "Completion audit root-module contract checks (legacy `scripts/completion_audit.sh`\n"
        "`root_contract_check` heredoc)."
    ),
    "PoincareAudit/Completion/DependencyContract.lean": (
        "Completion audit dependency contract checks (legacy `scripts/completion_audit.sh`\n"
        "`dependency_contract_check` heredoc)."
    ),
    "PoincareAudit/Completion/CertificateRoutes.lean": (
        "Certificate route projection checks required by the completion audit\n"
        "(legacy `append_certificate_route_projection_contract_checks` in\n"
        "`scripts/completion_audit.sh`)."
    ),
}

# The reserved-endpoint probe stays a live `lake env lean` check (it is expected to fail
# while the reserved theorem is absent, so it cannot live in a Lake-built module).
RESERVED_PROBE = [
    "import Poincare",
    "",
    "#check (Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement)",
]

HEREDOC_START = re.compile(r"<<'EOF'$")


def git_show(ref: str, path: str) -> str:
    result = subprocess.run(
        ["git", "show", f"{ref}:{path}"], cwd=ROOT, text=True, capture_output=True,
        check=False, encoding="utf-8",
    )
    if result.returncode != 0:
        raise RuntimeError(f"cannot read {path} at {ref}: {result.stderr.strip()}")
    return result.stdout


def heredoc_bodies(text: str) -> list[list[str]]:
    """Return the body lines of every ``<<'EOF'`` heredoc, in file order."""
    lines = text.split("\n")
    bodies: list[list[str]] = []
    index = 0
    while index < len(lines):
        if HEREDOC_START.search(lines[index]):
            body: list[str] = []
            index += 1
            while index < len(lines) and lines[index] != "EOF":
                body.append(lines[index])
                index += 1
            if index >= len(lines):
                raise RuntimeError("unterminated heredoc")
            bodies.append(body)
        index += 1
    return bodies


def legacy_blocks(ref: str) -> dict[str, list[str]]:
    blocks: dict[str, list[str]] = {}
    for script in LEGACY_SCRIPTS:
        bodies = heredoc_bodies(git_show(ref, f"scripts/{script}.sh"))
        for position, body in enumerate(bodies):
            name = BLOCKS.get((script, position))
            if name is None:
                raise RuntimeError(f"unexpected heredoc #{position} in scripts/{script}.sh")
            blocks[name] = body
    missing = set(BLOCKS.values()) - set(blocks)
    if missing:
        raise RuntimeError(f"missing legacy heredocs: {sorted(missing)}")
    return blocks


def convert_line(line: str) -> str:
    """Rewrite one legacy payload line into its checked-in module form."""
    if line.startswith("#check"):
        return GUARD_PREFIX + line
    if line.startswith("#print axioms "):
        return "#std_axioms " + line[len("#print axioms "):]
    return line


def module_text(module: str, blocks: dict[str, list[str]]) -> str:
    out: list[str] = [
        "/-!",
        MODULE_DOC[module],
        "",
        "Generated by `scripts/audit_payload_equivalence.py --write`; verified against the",
        "legacy heredocs by `scripts/audit_payload_equivalence.py --check`.  Keep one",
        "declaration per line.",
        "-/",
    ]
    first = True
    for block_name in MODULES[module]:
        body = blocks[block_name]
        if first:
            if module.startswith("PoincareAudit/Axiom/"):
                out.append("import PoincareAudit.Guard")
            if not (body and body[0] == "import Poincare"):
                out.extend(["import Poincare", ""])
            first = False
        out.extend(convert_line(line) for line in body)
    text = "\n".join(out)
    if not text.endswith("\n"):
        text += "\n"
    return text


def split_items(lines: list[str], *, module_form: bool) -> tuple[list[str], list[str]]:
    """Split payload lines into (checked items in legacy form, header lines).

    ``module_form`` accepts the converted spellings and maps them back to the legacy
    ones so both sides can be compared verbatim.
    """
    items: list[str] = []
    header: list[str] = []
    current: list[str] | None = None
    in_doc = False
    for line in lines:
        if module_form:
            if line == "/-!":
                in_doc = True
                continue
            if in_doc:
                if line == "-/":
                    in_doc = False
                continue
        starts_item = False
        if module_form:
            if line.startswith(GUARD_PREFIX):
                line = line[len(GUARD_PREFIX):]
                starts_item = True
            elif line.startswith("#std_axioms "):
                line = "#print axioms " + line[len("#std_axioms "):]
                starts_item = True
            elif line.startswith(("#check", "#print axioms ")):
                raise RuntimeError(f"unconverted legacy command in module: {line[:80]}")
        elif line.startswith("#check") or line.startswith("#print axioms "):
            starts_item = True
        if starts_item:
            if current is not None:
                items.append("\n".join(current))
            current = [line]
        elif line.startswith((" ", "\t")) and current is not None:
            current.append(line)
        else:
            if current is not None:
                items.append("\n".join(current))
                current = None
            if line.strip() and not line.startswith("--"):
                header.append(line)
    if current is not None:
        items.append("\n".join(current))
    return items, header


def checked_names(items: list[str]) -> set[str]:
    names = set()
    for item in items:
        match = re.match(
            r"#(?:check|print axioms)\s*\(?\s*(?:show\s+)?([A-Za-z0-9_.']+)", item.replace("\n", " ")
        )
        if match:
            names.add(match.group(1))
    return names


def check(ref: str, audit_dir: Path, *, out=sys.stdout) -> list[str]:
    blocks = legacy_blocks(ref)
    problems: list[str] = []
    for module, block_names in MODULES.items():
        path = audit_dir / module
        if not path.is_file():
            problems.append(f"{module}: missing")
            continue
        legacy_items: list[str] = []
        legacy_header: list[str] = []
        for block_name in block_names:
            items, header = split_items(blocks[block_name], module_form=False)
            legacy_items.extend(items)
            legacy_header.extend(header)
        try:
            module_items, module_header = split_items(
                path.read_text(encoding="utf-8").split("\n"), module_form=True
            )
        except RuntimeError as error:
            problems.append(f"{module}: {error}")
            continue
        expected_header = set(legacy_header) | {"import Poincare"}
        if module.startswith("PoincareAudit/Axiom/"):
            expected_header.add("import PoincareAudit.Guard")
        if set(module_header) != expected_header:
            problems.append(f"{module}: header mismatch {sorted(set(module_header) ^ expected_header)}")
        if module_items != legacy_items:
            legacy_set, module_set = set(legacy_items), set(module_items)
            problems.append(
                f"{module}: {len(module_items)} items vs {len(legacy_items)} legacy items; "
                f"only-legacy={len(legacy_set - module_set)} only-module={len(module_set - legacy_set)}"
            )
        else:
            names = checked_names(module_items)
            print(
                f"OK: {module}: {len(module_items)} checks ({len(names)} unique names) "
                "match the legacy heredocs", file=out,
            )
    reserved = blocks["completion.reserved"]
    if reserved != RESERVED_PROBE:
        problems.append(f"completion.reserved heredoc changed: {reserved}")
    else:
        print("OK: completion reserved-endpoint probe matches the legacy heredoc", file=out)
    return problems


def write(ref: str, audit_dir: Path) -> None:
    blocks = legacy_blocks(ref)
    for module in MODULES:
        path = audit_dir / module
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(module_text(module, blocks), encoding="utf-8")
        print(f"wrote {path}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--ref", default=LEGACY_REF, help="git revision holding the legacy heredoc scripts")
    parser.add_argument("--audit-dir", default=str(ROOT / "audit"), help="directory holding the PoincareAudit modules")
    parser.add_argument("--write", action="store_true", help="regenerate the modules instead of checking them")
    parser.add_argument("--check", action="store_true", help="verify the modules against the heredocs (default)")
    args = parser.parse_args(argv)
    audit_dir = Path(args.audit_dir)
    if args.write:
        write(args.ref, audit_dir)
        return 0
    problems = check(args.ref, audit_dir)
    for problem in problems:
        print(f"FAIL: {problem}")
    if problems:
        return 1
    print("PAYLOADS: audit modules are a lossless extraction of the legacy heredocs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
