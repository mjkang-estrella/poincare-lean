"""Validate status snapshot fixtures without running mathematical completion gates.

An achieved fixture exercises report consistency only. It is not proof evidence.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "completion_audit.sh"
TOOLCHAIN = (ROOT / "lean-toolchain").read_text().strip()
RG_DIR = Path(shutil.which("rg") or ROOT / "scripts" / "bin" / "rg").parent
GATES = (
    ("Build", "Build", "Build completed successfully"),
    ("Interface audit", "Interface Audit", "== Interface audit =="),
    ("Mathlib gap audit", "Mathlib Gap Audit", "== Mathlib gap audit =="),
    ("Shape contract audit", "Shape Contract Audit", "== Shape contract audit =="),
    ("Theorem contract audit", "Theorem Contract Audit", "== Theorem contract audit =="),
    ("Semantic surface audit", "Semantic Surface Audit", "== Semantic surface audit =="),
    ("Root import audit", "Root Import Audit", "== Root import audit =="),
    ("Axiom footprint audit", "Axiom Footprint Audit", "== Axiom footprint audit =="),
)


def fixture(*, achieved: bool = False) -> str:
    result = "achieved" if achieved else "not achieved"
    code = 0 if achieved else 1
    boundary = "proved" if achieved else "reserved theorem absent only"
    lines = [
        "# Current Poincare Formalization Status", "", "## Result", "",
        f"- Completion: {result}", "- Generated at: 2026-09-30T00:00:00Z",
        f"- Lean toolchain: {TOOLCHAIN}",
        *(f"- {label} status: 0" for label, _, _ in GATES),
        f"- Completion audit status: {code}",
        f"- Completion boundary status: {boundary}",
    ]
    for _, heading, sentinel in GATES:
        lines += ["", f"## {heading}", "", "Status: 0", "", "```text", sentinel, "```"]
    lines += ["", "## Completion Audit", "", f"Status: {code}", "", "```text",
              "== Build gate ==", f"COMPLETION: {result}", "```", ""]
    return "\n".join(lines)


def snapshot_source() -> str:
    """Extract only the production presence check and snapshot-validation block."""
    text = SCRIPT.read_text(encoding="utf-8")
    presence = re.search(r"^check_present\(\) \{\n.*?^\}\n", text, re.S | re.M)
    if not presence:
        raise AssertionError("check_present is not defined in completion_audit.sh")
    call = 'check_present "Generated current status" "CURRENT_STATUS.md"\n'
    if text.count(call) != 1:
        raise AssertionError("Expected one generated status presence check")
    start = text.index('if [ "${COMPLETION_AUDIT_SKIP_STATUS_SNAPSHOT:-0}" = "1" ]; then')
    end = text.index("\nif rg -q '^def PoincareConjectureStatement", start)
    # Retain earlier status-content checks so generation-skip regression tests
    # also cover accidental validation outside the guard.
    earlier_content = "\n".join(line for line in text[:start].splitlines()
                                if line.startswith("check_file_contains ") and
                                '"CURRENT_STATUS.md"' in line)
    contains = re.search(r"^check_file_contains\(\) \{\n.*?^\}\n", text, re.S | re.M)
    if not contains:
        raise AssertionError("check_file_contains is not defined in completion_audit.sh")
    return presence.group(0) + contains.group(0) + call + earlier_content + "\n" + text[start:end]


class CompletionStatusContractTest(unittest.TestCase):
    def run_snapshot(self, content: str | None, *, skip: bool = False,
                     portable_rg: bool = False) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            if content is not None:
                (root / "CURRENT_STATUS.md").write_text(content)
            (root / "lean-toolchain").write_text(TOOLCHAIN + "\n")
            rg_dir = ROOT / "scripts" / "bin" if portable_rg else RG_DIR
            env = {"PATH": f"{rg_dir}:/usr/bin:/bin"}
            if skip:
                env["COMPLETION_AUDIT_SKIP_STATUS_SNAPSHOT"] = "1"
            body = "set -eu\nstatus=0\n" + snapshot_source() + '\nexit "$status"\n'
            return subprocess.run(["sh", "-c", body], cwd=root, env=env, text=True,
                                  capture_output=True, check=False)

    def assert_rejected(self, content: str) -> None:
        result = self.run_snapshot(content)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("FAIL:", result.stdout)

    def test_coherent_achieved_fixture_is_accepted(self) -> None:
        result = self.run_snapshot(fixture(achieved=True))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("FAIL:", result.stdout)

    def test_coherent_incomplete_fixture_is_accepted(self) -> None:
        result = self.run_snapshot(fixture())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_current_snapshot_contract_is_accepted(self) -> None:
        result = self.run_snapshot((ROOT / "CURRENT_STATUS.md").read_text())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_coherent_fixtures_work_with_portable_ripgrep(self) -> None:
        for achieved in (False, True):
            with self.subTest(achieved=achieved):
                result = self.run_snapshot(fixture(achieved=achieved), portable_rg=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_inconsistent_completion_rows_are_rejected(self) -> None:
        for achieved in (False, True):
            content = fixture(achieved=achieved)
            changes = {
                f"- Completion: {'achieved' if achieved else 'not achieved'}":
                    f"- Completion: {'not achieved' if achieved else 'achieved'}",
                f"- Completion audit status: {0 if achieved else 1}":
                    f"- Completion audit status: {1 if achieved else 0}",
                f"- Completion boundary status: {'proved' if achieved else 'reserved theorem absent only'}":
                    f"- Completion boundary status: {'reserved theorem absent only' if achieved else 'proved'}",
            }
            for old, new in changes.items():
                with self.subTest(achieved=achieved, row=old):
                    self.assert_rejected(content.replace(old, new))

    def test_nonzero_scaffold_rows_are_rejected(self) -> None:
        for label, _, _ in GATES:
            with self.subTest(gate=label):
                self.assert_rejected(fixture(achieved=True).replace(
                    f"- {label} status: 0", f"- {label} status: 1"))

    def test_unknown_completion_boundary_is_rejected(self) -> None:
        self.assert_rejected(fixture().replace("reserved theorem absent only", "unexpected completion audit failures"))

    def test_missing_contract_rows_are_rejected(self) -> None:
        for row in fixture().splitlines():
            if row.startswith("- ") and "Generated at:" not in row and "Lean toolchain:" not in row:
                with self.subTest(row=row):
                    self.assert_rejected(fixture().replace(row + "\n", ""))

    def test_duplicate_contract_rows_are_rejected(self) -> None:
        for row in fixture().splitlines():
            if row.startswith("- ") and "Generated at:" not in row and "Lean toolchain:" not in row:
                with self.subTest(row=row):
                    self.assert_rejected(fixture() + row + "\n")

    def test_opposite_completion_sentinel_is_rejected(self) -> None:
        for achieved in (False, True):
            with self.subTest(achieved=achieved):
                result = "achieved" if achieved else "not achieved"
                opposite = "not achieved" if achieved else "achieved"
                self.assert_rejected(fixture(achieved=achieved).replace(
                    f"COMPLETION: {result}", f"COMPLETION: {opposite}"))

    def test_duplicate_or_conflicting_completion_sentinels_are_rejected(self) -> None:
        for sentinel in ("achieved", "not achieved"):
            with self.subTest(sentinel=sentinel):
                self.assert_rejected(fixture() + f"COMPLETION: {sentinel}\n")

    def test_missing_evidence_sections_are_rejected(self) -> None:
        for heading in [heading for _, heading, _ in GATES] + ["Completion Audit"]:
            with self.subTest(heading=heading):
                self.assert_rejected(fixture().replace(f"## {heading}\n", ""))

    def test_missing_audit_sentinels_are_rejected(self) -> None:
        for sentinel in [sentinel for _, _, sentinel in GATES] + ["== Build gate ==", "COMPLETION: not achieved"]:
            with self.subTest(sentinel=sentinel):
                self.assert_rejected(fixture().replace(sentinel + "\n", ""))

    def test_current_toolchain_match_is_required(self) -> None:
        self.assert_rejected(fixture().replace(TOOLCHAIN, "leanprover/lean4:stale"))

    def test_generation_skip_ignores_stale_status_content(self) -> None:
        for content in ("", "obsolete status content\n", fixture(achieved=True).replace(TOOLCHAIN, "stale")):
            with self.subTest(content=content[:30]):
                result = self.run_snapshot(content, skip=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("SKIP: generated status snapshot checks disabled during status generation", result.stdout)

    def test_generation_skip_still_requires_status_file_presence(self) -> None:
        result = self.run_snapshot(None, skip=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("FAIL: Generated current status -> CURRENT_STATUS.md missing", result.stdout)


if __name__ == "__main__":
    unittest.main()
