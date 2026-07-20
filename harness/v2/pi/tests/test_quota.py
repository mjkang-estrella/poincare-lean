from __future__ import annotations

import hashlib
import json
import stat
import tempfile
import unittest
from pathlib import Path

from harness.v2.pi.engine import _minimal_quota_failure_result
from harness.v2.pi.quota import PiQuotaError, SharedArtifactQuota


class SharedArtifactQuotaTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()

    def test_append_reports_the_complete_file_digest(self) -> None:
        quota = SharedArtifactQuota(self.root, 1024 * 1024)
        quota.write_once("events.jsonl", b"first\n")
        result = quota.append("events.jsonl", b"second\n")
        complete = b"first\nsecond\n"
        self.assertEqual(result.size_bytes, len(complete))
        self.assertEqual(result.sha256, hashlib.sha256(complete).hexdigest())

    def test_reserved_budget_always_emits_a_sealed_minimal_failure(self) -> None:
        quota = SharedArtifactQuota(self.root, 64 * 1024)
        quota.write_once("bulk.bin", b"x" * quota.normal_limit)
        with self.assertRaises(PiQuotaError):
            quota.append("bulk.bin", b"x")
        result = _minimal_quota_failure_result(
            artifact_quota=quota,
            artifact_dir=self.root,
            job_id="job-quota",
            reason="normal quota exhausted",
            process_returncode=70,
        )
        self.assertFalse(result.success)
        record = json.loads((self.root / "pi-run-result.json").read_text())
        self.assertEqual(record["quota_failure"], True)
        self.assertEqual(record["success"], False)
        for name in (
            "final-report.md",
            "evidence-manifest.json",
            "pi-run-result.json",
        ):
            self.assertEqual(
                stat.S_IMODE((self.root / name).stat().st_mode), 0o400
            )


if __name__ == "__main__":
    unittest.main()
