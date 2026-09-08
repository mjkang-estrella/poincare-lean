#!/usr/bin/env python3
"""Derive the audit manifests from the legacy shell audit scripts.

The legacy scripts (``scripts/*_audit.sh`` before ``LEGACY_REF``) mixed data (route
suffix families, declaration patterns, occurrence counts, predicate names) with the
shell loops that consumed them.  ``scripts/audit_driver.py`` now implements the loops
once and reads the data from ``scripts/audit/manifests``.  This tool derives those
manifests *mechanically* from the legacy text so that nothing is transcribed by hand:

* route-rule call sequences are obtained by executing the relevant legacy regions with
  ``sh`` under recording stubs (the shell performs its own quoting/expansion);
* the 7,896 ``check_decl`` invocations of the completion audit are recorded the same way;
* fixed-shape blocks (interface predicates, ``check_present``/``check_file_contains``
  lists, ``rg -q`` conjunction chains, semantic source-count checks) are parsed by
  regular expressions that must consume every line of their region (an unrecognised
  line is a hard error, so nothing is silently dropped);
* comment-only ``#check`` lines that the legacy self-referential coverage scans relied on
  are copied verbatim into token manifests.

``--write`` regenerates ``scripts/audit/manifests``; ``--check`` (default) re-derives
everything and compares it with the checked-in files.  Only ``git``, ``sh`` and the
standard library are needed.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST_DIR = ROOT / "scripts" / "audit" / "manifests"
LEGACY_REF = "b2b96fc28248c2a72cb2e08b4fda946d3b26e6d5"
SEP = "\x1f"

RECORDED_FUNCTIONS = [
    "check_route_counterpart",
    "check_route_base_endpoint",
    "check_route_base_endpoint_for_prefix",
    "check_route_suffix_counterpart",
    "check_route_suffix_clique_counterparts",
    "check_payload_route_parity",
    "check_boundary_payload_route_parity",
    "check_constructor_endpoint_family",
    "check_boundary_constructor_endpoint_family",
    "check_boundary_constructor_payload_eq_family",
    "check_route_counterpart_family",
    "check_route_base_endpoint_family",
    "check_route_base_endpoint_prefix",
    "check_completion_certificate_constructor_endpoint_family",
    "check_decl",
    "__awk_topology_derivation_check",
]

FUNCTION_DEF = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*\(\) \{$")


def git_show(ref: str, path: str) -> str:
    result = subprocess.run(
        ["git", "show", f"{ref}:{path}"], cwd=ROOT, text=True, capture_output=True,
        check=False, encoding="utf-8",
    )
    if result.returncode != 0:
        raise RuntimeError(f"cannot read {path} at {ref}: {result.stderr.strip()}")
    return result.stdout


def strip_heredocs(lines: list[str]) -> list[str]:
    """Replace every ``<<'EOF'`` heredoc body with nothing (keeps line structure)."""
    out: list[str] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        out.append(line)
        if line.endswith("<<'EOF'"):
            index += 1
            while index < len(lines) and lines[index] != "EOF":
                index += 1
            out.append("EOF")
        index += 1
    return out


def strip_function_defs(lines: list[str]) -> list[str]:
    """Drop top-level ``name() {`` ... ``}`` blocks (functions are re-implemented in Python)."""
    out: list[str] = []
    depth = 0
    for line in lines:
        if depth == 0 and FUNCTION_DEF.match(line):
            depth = 1
            continue
        if depth > 0:
            if line == "}":
                depth = 0
            continue
        out.append(line)
    return out


def find_line(lines: list[str], pattern: str, start: int = 0) -> int:
    regex = re.compile(pattern)
    for index in range(start, len(lines)):
        if regex.search(lines[index]):
            return index
    raise RuntimeError(f"anchor not found: {pattern!r}")


def run_recorded(region: list[str], *, allow_echo: bool = True) -> list[dict]:
    """Execute a pure-shell legacy region with recording stubs and return the records."""
    stubs = [f"{name}() {{ __rec call {name} \"$@\"; }}" for name in RECORDED_FUNCTIONS]
    if allow_echo:
        stubs.append('echo() { __rec echo "$@"; }')
    script = "\n".join(
        ["set -eu", "__rec() { printf '%s\\037' \"$@\"; printf '\\n'; }", *stubs, 'status=0', *region, ""]
    )
    with tempfile.NamedTemporaryFile("w", suffix=".sh", delete=False, encoding="utf-8") as handle:
        handle.write(script)
        path = handle.name
    try:
        result = subprocess.run(["sh", path], text=True, capture_output=True, check=False, encoding="utf-8")
    finally:
        Path(path).unlink()
    if result.returncode != 0:
        raise RuntimeError(f"legacy region did not execute cleanly: {result.stderr[-2000:]}")
    records: list[dict] = []
    for raw in result.stdout.split("\n"):
        if not raw:
            continue
        fields = raw.split(SEP)
        if fields[-1] != "":
            raise RuntimeError(f"malformed record: {raw!r}")
        fields = fields[:-1]
        if fields[0] == "call":
            records.append({"call": fields[1], "args": fields[2:]})
        elif fields[0] == "echo":
            records.append({"echo": " ".join(fields[1:])})
        else:
            raise RuntimeError(f"unknown record kind: {fields[0]!r}")
    return records


ALLOWED_REGION_LINE = re.compile(
    r"^\s*(?:$|(?:" + "|".join(RECORDED_FUNCTIONS) + r")\b|echo \"|for [a-z_]+ in|do$|done$|"
    r"[A-Za-z0-9_]+ \\$|[A-Za-z0-9_]+$|\"[^\"]*\"(?: \\)?$|'[^']*'(?: \\)?$|"
    r"(?:_[a-z_]+ )+_?[a-z_]+$|"
    r"if \[ |fi$|case |\*\)$|[A-Za-z0-9_]+\)$|;;$|esac$)"
)


def check_region_purity(region: list[str]) -> None:
    """A recorded region may only contain calls, echoes, loops and simple conditionals."""
    for line in region:
        if not ALLOWED_REGION_LINE.match(line):
            raise RuntimeError(f"unexpected statement in recorded region: {line!r}")


def region(lines: list[str], start_pattern: str, end_pattern: str, *, start_at: int = 0,
           include_end: bool = False) -> tuple[list[str], int]:
    start = find_line(lines, start_pattern, start_at)
    end = find_line(lines, end_pattern, start + 1)
    return lines[start:end + (1 if include_end else 0)], end


# ---------------------------------------------------------------------------
# interface audit


def interface_steps(text: str) -> list[dict]:
    lines = text.split("\n")
    start = find_line(lines, r'^check_no_constructors "')
    end = find_line(lines, r'^if \[ "\$status" -eq 0 \]; then')
    steps: list[dict] = []
    index = start
    predicate = re.compile(r'^check_no_constructors "([A-Za-z0-9_]+)" "([A-Za-z0-9_/.]+)"$')
    while index < end:
        line = lines[index]
        if line.strip() == "":
            index += 1
            continue
        match = predicate.match(line)
        if match:
            steps.append({"kind": "predicate", "name": match.group(1), "path": match.group(2)})
            index += 1
            continue
        if line.startswith("if rg -q "):
            block, index = parse_conjunction_chain(lines, index)
            steps.append(block)
            continue
        raise RuntimeError(f"unrecognised interface audit line {index + 1}: {line!r}")
    return steps


CHAIN_HEAD = re.compile(r"^if rg -q '([^']*)' ([A-Za-z0-9_/.]+) &&$")
CHAIN_MID = re.compile(r"^    rg -q '([^']*)' ([A-Za-z0-9_/.]+) &&$")
CHAIN_TAIL = re.compile(r"^    rg -q '([^']*)' ([A-Za-z0-9_/.]+); then$")


def parse_conjunction_chain(lines: list[str], index: int) -> tuple[dict, int]:
    """Parse ``if rg -q 'p' f && ... rg -q 'p' f; then echo PASS else echo FAIL; status=1 fi``."""
    match = CHAIN_HEAD.match(lines[index])
    if not match:
        raise RuntimeError(f"bad chain head at line {index + 1}: {lines[index]!r}")
    checks = [{"pattern": match.group(1), "path": match.group(2)}]
    index += 1
    while True:
        line = lines[index]
        match = CHAIN_MID.match(line)
        if match:
            checks.append({"pattern": match.group(1), "path": match.group(2)})
            index += 1
            continue
        match = CHAIN_TAIL.match(line)
        if match:
            checks.append({"pattern": match.group(1), "path": match.group(2)})
            index += 1
            break
        raise RuntimeError(f"bad chain line {index + 1}: {line!r}")
    expected = [
        re.compile(r'^  echo "(PASS: .*)"$'), re.compile(r"^else$"), re.compile(r'^  echo "(FAIL: .*)"$'),
        re.compile(r"^  status=1$"), re.compile(r"^fi$"),
    ]
    values = []
    for regex in expected:
        match = regex.match(lines[index])
        if not match:
            raise RuntimeError(f"bad chain tail at line {index + 1}: {lines[index]!r}")
        values.append(match.group(1) if match.groups() else None)
        index += 1
    return {"kind": "all_patterns", "checks": checks, "pass": values[0], "fail": values[2]}, index


# ---------------------------------------------------------------------------
# axiom / root import audits


def naming_steps(text: str) -> dict:
    lines = strip_heredocs(text.split("\n"))
    routes, _ = region(lines, r'^check_route_counterpart "', r"^payload_route_parity_dir=")
    routes = strip_function_defs(routes)
    check_region_purity(routes)
    parity, _ = region(lines, r"^for payload_family in literal ", r"^done$", include_end=True)
    check_region_purity(parity)
    families, end = region(
        lines, r'^\s*check_constructor_endpoint_family "poincare_conjecture_of_completion_certificate_of_"',
        r"^\s*done$", include_end=True,
    )
    check_region_purity(families)
    boundary, end = region(lines, r"^\s*for endpoint_family in \\$", r"^\s*done$", start_at=end, include_end=True)
    check_region_purity(boundary)
    boundary_eq, _ = region(lines, r"^\s*for payload_family in theoremName ", r"^\s*done$", start_at=end, include_end=True)
    check_region_purity(boundary_eq)
    return {
        "routes": run_recorded(routes),
        "parity": run_recorded(parity),
        "constructor_families": run_recorded(families),
        "boundary_constructor_families": run_recorded(boundary),
        "boundary_constructor_payload_eq_families": run_recorded(boundary_eq),
    }


# ---------------------------------------------------------------------------
# semantic surface audit


COUNT_BLOCK = re.compile(
    r"^(?P<var>[a-z_]+)=\(\n"
    r"  rg -c '(?P<token>[^']*)' \\\n"
    r"    (?P<file>Poincare/[A-Za-z]+\.lean) \|\| true\n"
    r"\)\n"
    r"if \[ \"\$(?P=var)\" != \"(?P<count>[0-9]+)\" \]; then\n"
    r"  echo \"(?P<fail>FAIL: [^\"]*)\"\n"
    r"  rg -n '(?P=token)' \\\n"
    r"    (?P=file) \|\| true\n"
    r"  exit 1\n"
    r"fi\n",
    re.M,
)
FORBIDDEN_BLOCK = re.compile(
    r"^if rg -q '(?P<token>[^']*)' \\\n"
    r"    (?P<file>Poincare/[A-Za-z]+\.lean); then\n"
    r"  echo \"(?P<fail>FAIL: [^\"]*)\"\n"
    r"  rg -n '(?P=token)' \\\n"
    r"    (?P=file) \|\| true\n"
    r"  exit 1\n"
    r"fi\n",
    re.M,
)
FORBIDDEN_LOOP = re.compile(
    r"^for (?P<var>[a-z_]+) in \\\n(?P<items>(?:  [A-Za-z0-9_]+(?: \\)?\n)+)"
    r"do\n"
    r"  if rg -q \"\\\\b\$\{(?P=var)\}\\\\b\" \\\n"
    r"      (?P<file>Poincare/[A-Za-z]+\.lean); then\n"
    r"    echo \"(?P<fail>FAIL: [^\"]*)\"\n"
    r"    rg -n \"\\\\b\$\{(?P=var)\}\\\\b\" \\\n"
    r"      (?P=file) \|\| true\n"
    r"    exit 1\n"
    r"  fi\n"
    r"done\n",
    re.M,
)
COUNT_LOOP = re.compile(
    r"^for (?P<var>[a-z_]+) in \\\n(?P<items>(?:  [A-Za-z0-9_]+(?: \\)?\n)+)"
    r"do\n"
    r"  (?P<cvar>[a-z_]+)=\(\n"
    r"    rg -c \"\\\\b\$\{(?P=var)\}\\\\b\" \\\n"
    r"      (?P<file>Poincare/[A-Za-z]+\.lean) \|\| true\n"
    r"  \)\n"
    r"  if \[ \"\$(?P=cvar)\" != \"(?P<count>[0-9]+)\" \]; then\n"
    r"    echo \"(?P<fail>FAIL: [^\"]*) \$\{(?P=var)\}\"\n"
    r"    rg -n \"\\\\b\$\{(?P=var)\}\\\\b\" \\\n"
    r"      (?P=file) \|\| true\n"
    r"    exit 1\n"
    r"  fi\n"
    r"done\n",
    re.M,
)
SED_RANGE_BLOCK = re.compile(
    r"^if sed -n '(?P<range>[^']*)' \\\n"
    r"    (?P<file>Poincare/[A-Za-z]+\.lean) \|\n"
    r"    rg -q '(?P<token>[^']*)'; then\n"
    r"  echo \"(?P<fail>FAIL: [^\"]*)\"\n"
    r"  sed -n '(?P=range)' \\\n"
    r"    (?P=file) \|\n"
    r"    rg -n '(?P=token)' \|\| true\n"
    r"  exit 1\n"
    r"fi\n",
    re.M,
)


def semantic_source_checks(text: str) -> list[dict]:
    lines = strip_heredocs(text.split("\n"))
    start = find_line(lines, r"^topology_package_payload_count=\($")
    end = find_line(lines, r"^# Attribute-prefixed route checks included in the full surface guard\.$")
    body = "\n".join(lines[start:end]) + "\n"
    checks: list[dict] = []
    position = 0
    while position < len(body):
        if body[position] == "\n":
            position += 1
            continue
        for kind, regex in (
            ("count", COUNT_BLOCK), ("forbidden", FORBIDDEN_BLOCK), ("forbidden_loop", FORBIDDEN_LOOP),
            ("count_loop", COUNT_LOOP), ("sed_range", SED_RANGE_BLOCK),
        ):
            match = regex.match(body, position)
            if match:
                break
        else:
            snippet = body[position:position + 200]
            raise RuntimeError(f"unrecognised semantic source check block: {snippet!r}")
        entry = {"kind": kind, "file": match.group("file"), "fail": match.group("fail")}
        if kind in ("count", "forbidden"):
            entry["token"] = match.group("token")
        if kind == "count":
            entry["count"] = match.group("count")
        if kind in ("forbidden_loop", "count_loop"):
            entry["tokens"] = [item.strip().rstrip("\\").strip() for item in match.group("items").split("\n") if item.strip()]
        if kind == "count_loop":
            entry["count"] = match.group("count")
        if kind == "sed_range":
            entry["range"] = match.group("range")
            entry["token"] = match.group("token")
        checks.append(entry)
        position = match.end()
    return checks


def for_list(lines: list[str], var: str, *, start_at: int = 0) -> tuple[list[str], int]:
    """Return the items of the first ``for VAR in ... do`` loop at/after ``start_at``."""
    index = find_line(lines, rf"^\s*for {re.escape(var)} in( |$)", start_at)
    head = lines[index].strip()
    items: list[str] = []
    rest = head[len(f"for {var} in"):].strip()
    if rest.endswith("; do"):
        return rest[: -len("; do")].split(), index
    if rest != "\\":
        raise RuntimeError(f"unexpected loop header: {head!r}")
    index += 1
    while True:
        line = lines[index].strip()
        if line == "do":
            return items, index
        if line.endswith("; do"):
            items.extend(line[: -len("; do")].rstrip("\\").split())
            return items, index
        items.extend(line.rstrip("\\").split())
        index += 1


def semantic_steps(text: str) -> dict:
    lines = strip_heredocs(text.split("\n"))
    routes, _ = region(lines, r"^check_route_counterpart_family '", r'^echo "SEMANTIC SURFACE:')
    check_region_purity(routes)
    calls_start = find_line(lines, r"^check_completion_certificate_constructor_endpoint_family \\$")
    calls_end = find_line(lines, r"^for payload_route_family in ", calls_start)
    constructor_calls = lines[calls_start:calls_end]
    check_region_purity(constructor_calls)
    payload_families, index = for_list(lines, "payload_route_family", start_at=calls_end)
    boundary_families, index = for_list(lines, "boundary_endpoint_family", start_at=index)
    boundary_payload_families, index = for_list(lines, "boundary_payload_family", start_at=index)
    parity_families, _ = for_list(lines, "family", start_at=find_line(lines, r"^route_parity_dir="))
    return {
        "routes": run_recorded(routes),
        "constructor_endpoint_families": run_recorded(constructor_calls),
        "payload_route_families": payload_families,
        "boundary_endpoint_families": boundary_families,
        "boundary_payload_families": boundary_payload_families,
        "parity_families": parity_families,
    }


def manual_check_lines(text: str) -> list[str]:
    """Comment-only ``#check`` lines outside heredocs (legacy self-referential token surface)."""
    lines = strip_heredocs(text.split("\n"))
    return [line.strip() for line in lines if re.match(r"^\s*#check ", line)]


# ---------------------------------------------------------------------------
# completion audit


CONSTRUCTOR_ENDPOINT_BLOCK = re.compile(
    r"  rg --no-filename -o '\^theorem (?P<prefix>[A-Za-z0-9_]+)_\(\[A-Za-z0-9_\]\+\)\\b' \\\n"
    r"    -r 'completion_certificate_of_\$1' \\\n"
    r"    Poincare/CanonicalBridges\.lean Poincare/CompletionTarget\.lean \|\n"
    r"(?P<sed>    sed '/_eq\$/d' \|\n)?"
    r"    sort -u > \"\$(?P<var>[a-z_]+)\"\n"
    r"(?:\n  if \[ ! -s \"\$constructor_surface_constructors\" \]; then\n"
    r"    echo \"(?P<nocons>FAIL: [^\"]*)\"\n    status=1\n    return\n  fi\n)?"
    r"\n  comm -23 \"\$constructor_surface_constructors\" \"\$(?P=var)\" \\\n"
    r"    > \"\$(?P<missing>[a-z_]+)\"\n\n"
    r"  if \[ -s \"\$(?P=missing)\" \]; then\n"
    r"    echo \"(?P<fail>FAIL: [^\"]*)\"\n"
    r"    sed 's/\^/MISSING: /' \"\$(?P=missing)\"\n"
    r"    status=1\n"
    r"  else\n"
    r"    echo \"(?P<pass>PASS: [^\"]*)\"\n"
    r"  fi\n"
)


def completion_steps(text: str) -> dict:
    lines = strip_heredocs(text.split("\n"))
    # checklist: check_present / check_file_contains
    checklist: list[dict] = []
    present = re.compile(r'^check_present "([^"]*)" "([^"]*)"$')
    contains = re.compile(r'^check_file_contains "([^"]*)" "([^"]*)" \'([^\']*)\'$')
    start = find_line(lines, r'^check_present "')
    end = find_line(lines, r"^if rg -q '\^\(structure\|inductive\) ExternalFormalizationBlocker")
    for index in range(start, end):
        line = lines[index]
        if not line:
            continue
        match = present.match(line)
        if match:
            checklist.append({"kind": "present", "label": match.group(1), "path": match.group(2)})
            continue
        match = contains.match(line)
        if match:
            checklist.append({"kind": "contains", "label": match.group(1), "path": match.group(2), "pattern": match.group(3)})
            continue
        raise RuntimeError(f"unrecognised checklist line {index + 1}: {line!r}")
    chains = []
    index = end
    for _ in range(2):
        chain, index = parse_conjunction_chain(lines, index)
        chains.append(chain)
        while lines[index] == "":
            index += 1
    if not lines[index].startswith('if [ "${COMPLETION_AUDIT_SKIP_STATUS_SNAPSHOT:-0}" = "1" ]'):
        raise RuntimeError(f"unexpected line after crosswalk chain: {lines[index]!r}")

    # direct/package route suffix parity: recorded route steps inside the function
    fn_start = find_line(lines, r"^check_direct_package_route_suffix_parity\(\) \{$")
    routes_start = find_line(lines, r"^  check_route_counterpart_family '_to_boundary_route_eq'", fn_start)
    fn_end = find_line(lines, r"^\}$", routes_start)
    routes = lines[routes_start:fn_end]
    check_region_purity(routes)

    # constructor endpoint coverage: unrolled blocks + family loops
    cov_start = find_line(lines, r"^check_completion_constructor_endpoint_coverage\(\) \{$")
    cov_end = find_line(lines, r"^\}$", cov_start)
    cov_text = "\n".join(lines[cov_start:cov_end + 1]) + "\n"
    endpoint_blocks = []
    for match in CONSTRUCTOR_ENDPOINT_BLOCK.finditer(cov_text):
        endpoint_blocks.append({
            "prefix": match.group("prefix"), "drop_eq": bool(match.group("sed")),
            "fail": match.group("fail"), "pass": match.group("pass"),
        })
    if len(endpoint_blocks) != 10:
        raise RuntimeError(f"expected 10 constructor endpoint blocks, found {len(endpoint_blocks)}")
    payload_families, index = for_list(lines, "payload_route_family", start_at=cov_start)
    boundary_families, index = for_list(lines, "boundary_endpoint_family", start_at=index)
    boundary_payload_families, index = for_list(lines, "boundary_payload_family", start_at=index)
    parity_start = find_line(lines, r"^check_payload_route_parity\(\) \{$")
    parity_families, _ = for_list(lines, "family", start_at=parity_start)

    # check_decl region
    decl_start = find_line(lines, r"^check_completion_constructor_endpoint_coverage$") + 1
    decl_end = find_line(lines, r"^append_certificate_route_projection_contract_checks\(\) \{$", decl_start)
    decl_region = "\n".join(lines[decl_start:decl_end])
    awk_block = (
        "if awk '\n"
        "  /^(structure|inductive) HasExtinctionHomeomorphismDerivation([[:space:]]|$)/ { in_decl = 1 }\n"
        "  in_decl && /HasExtinctionHomeomorphismAssembly/ { found = 1 }\n"
        "  in_decl && /: Prop([[:space:]]+where)?$/ { in_decl = 0 }\n"
        "  END { exit found ? 0 : 1 }\n"
        "' Poincare/TopologyExtraction.lean; then\n"
        '  echo "PASS: topology homeomorphism derivation interface depends on homeomorphism assembly"\n'
        "else\n"
        '  echo "FAIL: topology homeomorphism derivation interface does not depend on homeomorphism assembly"\n'
        "  status=1\n"
        "fi"
    )
    if decl_region.count(awk_block) != 1:
        raise RuntimeError("expected exactly one topology derivation awk block")
    decl_region = decl_region.replace(awk_block, "__awk_topology_derivation_check")
    decl_lines = decl_region.split("\n")
    for line in decl_lines:
        if line == "" or line.startswith("check_decl ") or line.startswith("  check_decl ") \
                or line.startswith("for ") or line.startswith("  ") or line in ("do", "done") \
                or line == "__awk_topology_derivation_check":
            continue
        raise RuntimeError(f"unexpected line in check_decl region: {line!r}")
    decls = run_recorded(decl_lines, allow_echo=False)
    for record in decls:
        if "call" not in record or record["call"] not in ("check_decl", "__awk_topology_derivation_check"):
            raise RuntimeError(f"unexpected record in check_decl region: {record}")
        if record["call"] == "check_decl" and len(record["args"]) != 3:
            raise RuntimeError(f"check_decl arity: {record}")
    return {
        "checklist": checklist,
        "milestone_chain": chains[0],
        "crosswalk_chain": chains[1],
        "routes": run_recorded(routes),
        "constructor_endpoint_blocks": endpoint_blocks,
        "payload_route_families": payload_families,
        "boundary_endpoint_families": boundary_families,
        "boundary_payload_families": boundary_payload_families,
        "parity_families": parity_families,
        "decls": decls,
    }


# ---------------------------------------------------------------------------


def derive(ref: str) -> dict[str, object]:
    axiom = git_show(ref, "scripts/axiom_audit.sh")
    root = git_show(ref, "scripts/root_import_audit.sh")
    semantic = git_show(ref, "scripts/semantic_surface_audit.sh")
    completion = git_show(ref, "scripts/completion_audit.sh")
    interface = git_show(ref, "scripts/interface_audit.sh")
    return {
        "interface.json": interface_steps(interface),
        "axiom.json": naming_steps(axiom),
        "root_import.json": naming_steps(root),
        "semantic.json": semantic_steps(semantic),
        "semantic_source_checks.json": semantic_source_checks(semantic),
        "semantic_manual_checks.txt": manual_check_lines(semantic),
        "completion.json": completion_steps(completion),
        "completion_manual_checks.txt": manual_check_lines(completion),
    }


def render(name: str, value: object) -> str:
    if name.endswith(".txt"):
        return "\n".join(value) + "\n"
    return json.dumps(value, indent=1, ensure_ascii=False) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--ref", default=LEGACY_REF)
    parser.add_argument("--manifest-dir", default=str(MANIFEST_DIR))
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true", help="(default) compare with checked-in manifests")
    args = parser.parse_args(argv)
    manifest_dir = Path(args.manifest_dir)
    derived = derive(args.ref)
    if args.write:
        manifest_dir.mkdir(parents=True, exist_ok=True)
        for name, value in derived.items():
            (manifest_dir / name).write_text(render(name, value), encoding="utf-8")
            print(f"wrote {manifest_dir / name}")
        return 0
    problems = []
    for name, value in derived.items():
        path = manifest_dir / name
        if not path.is_file():
            problems.append(f"{name}: missing")
            continue
        if path.read_text(encoding="utf-8") != render(name, value):
            problems.append(f"{name}: differs from the legacy derivation")
        else:
            print(f"OK: {name} matches the legacy scripts")
    for problem in problems:
        print(f"FAIL: {problem}")
    if problems:
        return 1
    print("MANIFESTS: audit manifests are a mechanical derivation of the legacy scripts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
