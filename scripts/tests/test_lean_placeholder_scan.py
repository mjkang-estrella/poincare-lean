"""The placeholder scan reports code, not comment prose."""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCANNER = ROOT / "scripts" / "lean_placeholder_scan.py"


class LeanPlaceholderScanTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="placeholder-scan-"))

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def scan(self, *paths: str) -> list[str]:
        result = subprocess.run([sys.executable, str(SCANNER), *paths], cwd=self.tmp, text=True,
                                capture_output=True, check=True)
        return result.stdout.splitlines()

    def test_comment_prose_is_ignored(self) -> None:
        (self.tmp / "Prose.lean").write_text(
            "/-- Two subdivisions admit a refinement; we postulate nothing.\n"
            "  sorry is not used here. -/\n"
            "theorem ok : True := trivial\n"
            "-- axiom-free: this comment says sorry\n"
            "/- outer /- nested axiom foo : True -/ still comment -/\n"
            'def s := "sorry inside a string"\n')
        self.assertEqual(self.scan("Prose.lean"), [])

    def test_real_placeholders_are_reported(self) -> None:
        (self.tmp / "Bad.lean").write_text(
            "axiom bad : True\n"
            "theorem x : True := by\n"
            "  sorry\n"
            "constant c : Nat\n"
            "  postulate p : True\n"
            "theorem y : 1 = 1 := by admit\n"
            "opaque o : Nat\n")
        hits = self.scan("Bad.lean")
        self.assertEqual([hit.split(":")[1] for hit in hits], ["1", "3", "4", "5", "6", "7"])

    def test_directory_walk_and_sorted_output(self) -> None:
        (self.tmp / "sub").mkdir()
        (self.tmp / "sub" / "B.lean").write_text("axiom b : True\n")
        (self.tmp / "A.lean").write_text("theorem a : True := by sorry\n")
        self.assertEqual(self.scan("."), ["./A.lean:1:theorem a : True := by sorry", "./sub/B.lean:1:axiom b : True"])


if __name__ == "__main__":
    unittest.main()
