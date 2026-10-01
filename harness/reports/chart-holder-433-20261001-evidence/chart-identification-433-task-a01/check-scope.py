#!/usr/bin/env python3
"""Check the frozen ChartIdentification API changes and h2-only proof scope.

This is a byte-preservation check. It neither invokes Lean nor validates proofs.
With --self-test it checks in-memory candidates without reading changed source.
"""

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


FILE = "Poincare/ChartIdentification.lean"
BASE = "681e24e8fedf59c21b71747e90835567dc790e43"
ORIGINAL = "55e4859b54acb9044d7966a12df7a12afa8b52fd"
SHA256 = "efb4f9099267c5196736abf95201373f869cb16aad57c8395caee282430e42eb"
FIRST, LAST = 62, 65

APPLICATIONS = {
    88: ("I", 1),
    110: ("I", 1),
    170: ("I", 1),
    211: ("I", 1),
    259: ("I'", 1),
    342: ("I'", 1),
    396: ("I'", 2),
    430: ("I'", 1),
    474: ("I'", 1),
    475: ("I'", 2),
    476: ("I'", 2),
    511: ("I'", 2),
    516: ("I'", 1),
}
UNFOLDINGS = {98: 1, 150: 1, 385: 1}
OLD_TOKEN = re.compile(rb"(?<![A-Za-z0-9_'])extDerivFun(?![A-Za-z0-9_'])")
NEW_TOKEN = re.compile(rb"(?<![A-Za-z0-9_'])mvfderiv(?![A-Za-z0-9_'])")
COMMANDS = re.compile(
    rb"(?m)^[ \t]*(?:import|namespace|section|end|theorem|lemma|def|"
    rb"abbrev|opaque|axiom|constant|instance|variable|universe|"
    rb"attribute|export|initialize|elab|macro|syntax)\b"
)


class ScopeError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise ScopeError(message)


def source_at(root, commit):
    return subprocess.check_output(
        ["git", "-C", str(root), "show", f"{commit}:{FILE}"]
    )


def freeze(root):
    base = source_at(root, BASE)
    original = source_at(root, ORIGINAL)
    require(base == original, "base/original source differs")
    require(hashlib.sha256(base).hexdigest() == SHA256, "frozen source hash differs")
    lines = base.splitlines(keepends=True)
    require(len(lines) == 610, "frozen line count differs")
    require(all(line.endswith(b"\n") for line in lines), "unexpected line endings")

    normalized = list(lines)
    application_count = unfolding_count = 0
    for number, (model, wanted) in APPLICATIONS.items():
        replacement = ("mvfderiv " + model).encode("ascii")
        normalized[number - 1], found = OLD_TOKEN.subn(
            replacement, normalized[number - 1]
        )
        require(found == wanted, f"application manifest mismatch on line {number}")
        application_count += found
    for number, wanted in UNFOLDINGS.items():
        normalized[number - 1], found = OLD_TOKEN.subn(
            b"mvfderiv", normalized[number - 1]
        )
        require(found == wanted, f"unfolding manifest mismatch on line {number}")
        unfolding_count += found

    require(application_count == 17, "application count differs")
    require(unfolding_count == 3, "unfolding count differs")
    expected = b"".join(normalized)
    require(len(OLD_TOKEN.findall(base)) == 21, "original token inventory differs")
    require(len(NEW_TOKEN.findall(base)) == 0, "base already contains mvfderiv")
    require(len(OLD_TOKEN.findall(expected)) == 1, "normalized old-token count differs")
    require(len(NEW_TOKEN.findall(expected)) == 20, "normalized new-token count differs")

    prefix = b"".join(normalized[:FIRST - 1])
    original_body = b"".join(normalized[FIRST - 1:LAST])
    suffix = b"".join(normalized[LAST:])
    require(b"/-" not in original_body and b"--" not in original_body,
            "frozen proof comment inventory differs")
    return base, prefix, suffix


def check_candidate(candidate, prefix, suffix):
    require(len(candidate) >= len(prefix) + len(suffix),
            "candidate shorter than frozen surrounding source")
    require(candidate.startswith(prefix), "frozen prefix changed")
    require(candidate.endswith(suffix), "frozen suffix changed")
    body = candidate[len(prefix):len(candidate) - len(suffix)]
    require(body.strip(), "permitted proof body is empty")
    require(body.endswith(b"\n"), "proof body lacks final newline")
    require(b"/-" not in body and b"--" not in body,
            "comments inserted into permitted proof region")
    require(COMMANDS.search(body) is None,
            "declaration or scope command in proof region")
    require(len(OLD_TOKEN.findall(candidate)) == 1,
            "unexpected extDerivFun occurrence")
    require(len(NEW_TOKEN.findall(candidate)) == 20,
            "unexpected mvfderiv occurrence")


def replace_one(source, old, new):
    require(old in source, "self-test mutation target missing")
    return source.replace(old, new, 1)


def self_test(base, prefix, suffix):
    lemma = b"    exact mfderivWithin_range_extChartAt_symm (I := I) (x := x)\n"
    positive = prefix + lemma + suffix
    base_lines = base.splitlines(keepends=True)
    missing_all = b"".join(base_lines[:FIRST - 1]) + lemma + b"".join(base_lines[LAST:])
    tests = [
        ("positive_one_line_lemma", positive, True),
        ("missing_normalizations", missing_all, False),
        ("missing_application", replace_one(positive, b"mvfderiv I f", b"extDerivFun f"), False),
        ("missing_unfolding", replace_one(positive, b"simp only [mvfderiv,", b"simp only [extDerivFun,"), False),
        ("wrong_model", replace_one(positive, b"mvfderiv I f", b"mvfderiv I' f"), False),
        ("import_change", replace_one(positive, b"import Mathlib.Analysis.Calculus.MeanValue", b"import Mathlib.Analysis.Calculus.FDeriv.Basic"), False),
        ("unrelated_proof_change", replace_one(positive, b"  exact key _\n", b"  rfl\n"), False),
        ("section_change", replace_one(positive, b"section DerivationIdentity", b"section ChangedIdentity"), False),
        ("h2_header_change", replace_one(positive, "      ContinuousLinearMap.id 𝕜 E := by\n".encode(), "      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by\n".encode()), False),
        ("comment_in_proof", prefix + b"    -- new comment\n" + lemma + suffix, False),
        ("extra_operator_in_proof", prefix + "    have hm := mvfderiv I (fun _ : M => (0 : 𝕜))\n".encode() + lemma + suffix, False),
        ("declaration_in_proof_region", prefix + b"theorem scopeEscape : True := by trivial\n" + lemma + suffix, False),
    ]
    results = []
    for name, candidate, wanted in tests:
        accepted = True
        diagnostic = "accepted"
        try:
            check_candidate(candidate, prefix, suffix)
        except ScopeError as error:
            accepted = False
            diagnostic = str(error)
        results.append({
            "case": name,
            "expected_accept": wanted,
            "accepted": accepted,
            "passed": accepted == wanted,
            "diagnostic": diagnostic,
            "candidate_sha256": hashlib.sha256(candidate).hexdigest(),
        })
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path, default=Path.cwd())
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        base, prefix, suffix = freeze(root)
        report = {
            "root": str(root),
            "file": FILE,
            "base": BASE,
            "original": ORIGINAL,
            "source_sha256": SHA256,
            "allowed_original_proof_lines": [FIRST, LAST],
            "applied_operators": 17,
            "model_I_applications": 4,
            "model_Iprime_applications": 13,
            "unfolding_identifiers": 3,
            "prefix_bytes": len(prefix),
            "suffix_bytes": len(suffix),
            "mode": "self-test" if args.self_test else "source-check",
            "lean_invoked": False,
        }
        if args.self_test:
            report["cases"] = self_test(base, prefix, suffix)
            report["passed"] = all(case["passed"] for case in report["cases"])
        else:
            candidate = (root / FILE).read_bytes()
            check_candidate(candidate, prefix, suffix)
            report["candidate_sha256"] = hashlib.sha256(candidate).hexdigest()
            report["passed"] = True
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0 if report["passed"] else 1
    except (ScopeError, OSError, subprocess.CalledProcessError) as error:
        print(json.dumps({"passed": False, "error": str(error)}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
