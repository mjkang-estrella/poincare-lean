"""The completion audit reuses gate results recorded by write_status_summary.sh."""

from __future__ import annotations

import re
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "completion_audit.sh"


def run_gate_source() -> str:
    text = SCRIPT.read_text(encoding="utf-8")
    match = re.search(r"^run_gate\(\) \{\n.*?^\}\n", text, re.S | re.M)
    if not match:
        raise AssertionError("run_gate is not defined in completion_audit.sh")
    return match.group(0)


class CompletionGateReuseTest(unittest.TestCase):
    def run_sh(self, body: str, env: dict[str, str]) -> subprocess.CompletedProcess:
        script = "set -eu\n" + run_gate_source() + body
        return subprocess.run(["sh", "-c", script], text=True, capture_output=True, check=False, env=env)

    def test_gate_runs_when_no_recorded_result(self) -> None:
        result = self.run_sh('run_gate "Build" build echo ran-build\n', {"PATH": "/usr/bin:/bin"})
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "== Build gate ==\nran-build\n")

    def test_recorded_success_is_reused_without_running(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "build.status").write_text("0\n")
            result = self.run_sh('run_gate "Build" build sh -c "echo must-not-run; exit 9"\n',
                                 {"PATH": "/usr/bin:/bin", "COMPLETION_AUDIT_GATE_RESULTS_DIR": directory})
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "== Build gate ==\nREUSE: Build gate result recorded by "
                         "scripts/write_status_summary.sh (status 0)\n")

    def test_recorded_failure_aborts_with_that_status(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "axiom.status").write_text("1\n")
            result = self.run_sh('run_gate "Axiom footprint" axiom true\necho unreachable\n',
                                 {"PATH": "/usr/bin:/bin", "COMPLETION_AUDIT_GATE_RESULTS_DIR": directory})
        self.assertEqual(result.returncode, 1)
        self.assertNotIn("unreachable", result.stdout)

    def test_theorem_contract_audit_prints_its_sentinel_header(self) -> None:
        text = (ROOT / "scripts" / "theorem_contract_audit.sh").read_text(encoding="utf-8")
        self.assertIn('echo "== Theorem contract audit =="', text)

    def test_status_summary_passes_results_directory(self) -> None:
        text = (ROOT / "scripts" / "write_status_summary.sh").read_text(encoding="utf-8")
        self.assertIn('COMPLETION_AUDIT_GATE_RESULTS_DIR="$tmp_dir" sh scripts/completion_audit.sh', text)


if __name__ == "__main__":
    unittest.main()
