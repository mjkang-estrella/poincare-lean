from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("frozen_contract_audit", ROOT / "scripts/frozen_contract_audit.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

from harness.v2.tests.test_statement_contracts import contract_fixture
from harness.v2.runtime.validation import statement_contract_snapshot


class FrozenAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.contract, raw = contract_fixture()
        (self.root / "README").write_bytes(b"fixture\n")
        (self.root / "review.json").write_bytes(raw)
        folder = self.root / "harness/v2/contracts"
        folder.mkdir(parents=True)
        self.manifest = folder / "example.contract.json"
        self.save()

    def save(self):
        self.manifest.write_text(json.dumps({"schema_version": "1.0", "statement_contract": self.contract}))

    def run_audit(self, *args):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return audit.main(["--repo", str(self.root), *args])

    def test_current_review_and_definition_snapshot_pass(self):
        self.assertEqual(self.run_audit("--check-context-only"), 0)

    def test_missing_manifests_fail_closed(self):
        self.manifest.unlink()
        self.assertEqual(self.run_audit(), 1)

    def test_changed_definition_or_review_never_runs_lean(self):
        for path in ("README", "review.json"):
            with self.subTest(path=path):
                target = self.root / path
                original = target.read_bytes()
                target.write_bytes(b"changed")
                with patch.object(audit.subprocess, "run") as run:
                    self.assertEqual(self.run_audit(), 1)
                    run.assert_not_called()
                target.write_bytes(original)

    def test_missing_and_symlinked_review_rejected(self):
        target = self.root / "review.json"
        original = target.read_bytes()
        target.unlink()
        self.assertEqual(self.run_audit("--check-context-only"), 1)
        (self.root / "other.json").write_bytes(original)
        target.symlink_to(self.root / "other.json")
        self.assertEqual(self.run_audit("--check-context-only"), 1)

    def test_secondary_statement_cannot_change_with_stale_review(self):
        self.contract["declarations"][1]["lean_type"] = "True"
        self.save()
        self.assertEqual(self.run_audit(), 1)

    def test_false_readback_rejected_even_with_updated_hash(self):
        path = self.root / "review.json"
        report = json.loads(path.read_bytes())
        report["verdict"] = "rejected"
        raw = json.dumps(report).encode()
        path.write_bytes(raw)
        self.contract["review"]["report_sha256"] = hashlib.sha256(raw).hexdigest()
        self.save()
        self.assertEqual(self.run_audit(), 1)

    def test_lean_failure_propagates(self):
        with patch.object(audit.subprocess, "run", return_value=subprocess.CompletedProcess([], 17)) as run:
            self.assertEqual(self.run_audit(), 17)
            self.assertIn("Nat.zero_ne_one", run.call_args.kwargs["input"])
            self.assertIn("(0 : Nat) ≠ 1", run.call_args.kwargs["input"])

    def test_context_drift_during_probe_is_rejected(self):
        def mutate(*args, **kwargs):
            (self.root / "README").write_bytes(b"changed during Lean")
            return subprocess.CompletedProcess([], 0)
        with patch.object(audit.subprocess, "run", side_effect=mutate):
            self.assertEqual(self.run_audit(), 1)

    def test_specific_imports_are_rebuilt_before_probe(self):
        self.contract["imports"] = ["Poincare.Example"]
        self.contract["review"]["snapshot_sha256"] = statement_contract_snapshot(self.contract)
        report = json.loads((self.root / "review.json").read_bytes())
        report["snapshot_sha256"] = self.contract["review"]["snapshot_sha256"]
        raw = json.dumps(report).encode()
        (self.root / "review.json").write_bytes(raw)
        self.contract["review"]["report_sha256"] = hashlib.sha256(raw).hexdigest()
        self.save()
        with patch.object(audit.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)) as run:
            self.assertEqual(self.run_audit(), 0)
            self.assertEqual(run.call_args_list[0].args[0], ["lake", "build", "Poincare.Example"])
            self.assertEqual(run.call_args_list[1].args[0], ["lake", "env", "lean", "--stdin"])
        def mutate(*args, **kwargs):
            (self.root / "review.json").write_bytes(b"changed during build")
            return subprocess.CompletedProcess([], 0)
        with patch.object(audit.subprocess, "run", side_effect=mutate) as run:
            self.assertEqual(self.run_audit(), 1)
            self.assertEqual(run.call_count, 1)

    def test_snapshot_mode_does_not_claim_compilation_or_review(self):
        (self.root / "review.json").unlink()
        with patch.object(audit.subprocess, "run") as run:
            self.assertEqual(self.run_audit("--snapshot"), 0)
            run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
