"""Tests for the portable ripgrep fallback used by the audit scripts."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SHIM = ROOT / "scripts" / "bin" / "rg"


class RgFallbackTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="rg-fallback-"))
        (self.tmp / "t1.txt").write_text("alpha one\nbeta two\nalpha three\n")
        (self.tmp / "t2.txt").write_text("gamma\nalpha four\n")
        (self.tmp / "t3.txt").write_text("")
        (self.tmp / "t4.txt").write_text("def foo\nabbrev bar\n  constant x : Nat\nversion 7\n")
        (self.tmp / "sub").mkdir()
        (self.tmp / "sub" / "t5.txt").write_text("alpha five\n")

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def run_shim(self, *args: str, stdin: str | None = None):
        result = subprocess.run([str(SHIM), *args], cwd=self.tmp, text=True, input=stdin,
                                capture_output=True, check=False)
        return result.returncode, result.stdout

    def test_count_single_file_and_no_match(self) -> None:
        self.assertEqual(self.run_shim("-c", "alpha", "t1.txt"), (0, "2\n"))
        self.assertEqual(self.run_shim("-c", "zzz", "t1.txt"), (1, ""))
        self.assertEqual(self.run_shim("-c", "alpha", "t3.txt"), (1, ""))

    def test_line_numbers_and_filenames(self) -> None:
        self.assertEqual(self.run_shim("-n", "alpha", "t1.txt"), (0, "1:alpha one\n3:alpha three\n"))
        self.assertEqual(self.run_shim("-n", "alpha", "t1.txt", "t2.txt"),
                         (0, "t1.txt:1:alpha one\nt1.txt:3:alpha three\nt2.txt:2:alpha four\n"))
        self.assertEqual(self.run_shim("-Hn", "gamma", "t2.txt"), (0, "t2.txt:1:gamma\n"))

    def test_only_matching_replacement_and_lookahead(self) -> None:
        self.assertEqual(self.run_shim("--no-filename", "-o", "al[a-z]+", "t1.txt", "t2.txt"),
                         (0, "alpha\nalpha\nalpha\n"))
        self.assertEqual(self.run_shim("-o", r"alpha (\w+)", "-r", "X_$1", "t1.txt"), (0, "X_one\nX_three\n"))
        self.assertEqual(self.run_shim("-P", "--no-filename", "-o", "alpha(?= t)", "t1.txt"), (0, "alpha\n"))

    def test_whole_line_invert_quiet_and_stdin(self) -> None:
        self.assertEqual(self.run_shim("-qx", "alpha one", "t1.txt")[0], 0)
        self.assertEqual(self.run_shim("-qx", "alpha", "t1.txt")[0], 1)
        self.assertEqual(self.run_shim("-v", "alpha", "t1.txt"), (0, "beta two\n"))
        self.assertEqual(self.run_shim("-v", ".", "t1.txt"), (1, ""))
        self.assertEqual(self.run_shim("-c", "-v", "alpha", "t1.txt"), (0, "1\n"))
        self.assertEqual(self.run_shim("-n", "bar", stdin="foo\nbar\n"), (0, "2:bar\n"))
        self.assertEqual(self.run_shim("-qi", "ALPHA", "t1.txt")[0], 0)

    def test_posix_classes_and_directories(self) -> None:
        self.assertEqual(self.run_shim("-c", r"^(def|abbrev)[[:space:]]+[A-Za-z0-9_]+", "t4.txt"), (0, "2\n"))
        self.assertEqual(self.run_shim("-q", r"^[[:space:]]*constant[[:space:]]+x", "t4.txt")[0], 0)
        self.assertEqual(self.run_shim("-c", r"[[:digit:]]", "t4.txt"), (0, "1\n"))
        code, out = self.run_shim("-n", "alpha", "sub")
        self.assertEqual((code, out), (0, "sub/t5.txt:1:alpha five\n"))

    def test_files_listing(self) -> None:
        code, out = self.run_shim("--files", ".")
        self.assertEqual(code, 0)
        self.assertEqual(sorted(out.split()), ["./sub/t5.txt", "./t1.txt", "./t2.txt", "./t3.txt", "./t4.txt"])

    @unittest.skipUnless(shutil.which("rg"), "real ripgrep not available")
    def test_agrees_with_real_ripgrep(self) -> None:
        cases = [["-c", "alpha", "t1.txt"], ["-n", "alpha", "t1.txt", "t2.txt"],
                 ["--no-filename", "-o", "al[a-z]+", "t1.txt", "t2.txt"],
                 ["-o", r"alpha (\w+)", "-r", "X_$1", "t1.txt"], ["-qx", "alpha one", "t1.txt"],
                 ["-v", "alpha", "t1.txt"], ["-P", "--no-filename", "-o", "alpha(?= t)", "t1.txt"],
                 ["-q", r"^alpha\b", "t1.txt"], ["-q", r"beta\s+two$", "t1.txt"]]
        for case in cases:
            real = subprocess.run(["rg", *case], cwd=self.tmp, text=True, capture_output=True, check=False)
            self.assertEqual(self.run_shim(*case), (real.returncode, real.stdout), case)


if __name__ == "__main__":
    unittest.main()
