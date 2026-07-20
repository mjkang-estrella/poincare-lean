from __future__ import annotations

import hashlib
import json
import sqlite3
import subprocess
import tempfile
import unittest
from pathlib import Path

from harness.v2.pi.engine import (
    PiEngineError,
    _crosscheck_tool_evidence,
    _replay_patch_journal,
    _sparse_lean_acceptance_commands,
    _validated_sampling,
    _validate_commit_fence_state,
)
from harness.v2.pi.journal import PatchJournal


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class SparseAcceptanceSelectionTest(unittest.TestCase):
    def test_env_wrapped_and_raw_lean_file_gates_are_selected(self) -> None:
        env_gate = [
            "env",
            "LEAN_NUM_THREADS=1",
            "lake",
            "env",
            "lean",
            "Poincare/Test.lean",
        ]
        raw_gate = ["lake", "env", "lean", "Poincare/Other.lean"]
        task = {
            "acceptance": {
                "commands": [
                    env_gate,
                    ["env", "LEAN_NUM_THREADS=1", "lake", "build", "Poincare.Test"],
                    raw_gate,
                    ["git", "diff", "--check"],
                ]
            }
        }
        self.assertEqual(
            _sparse_lean_acceptance_commands(task),
            [env_gate, raw_gate],
        )

    def test_engine_sampling_boundary_rejects_extra_or_missing_fields(self) -> None:
        task = {"budget": {"max_output_tokens": 128}}
        for sampling in (
            {"max_tokens": 64, "temperature": 0, "top_p": 0.9},
            {"max_tokens": 64},
        ):
            with self.subTest(sampling=sampling):
                with self.assertRaisesRegex(PiEngineError, "sampling"):
                    _validated_sampling(
                        task,
                        {"backend": {"sampling": sampling}},
                    )


class CommitFenceTest(unittest.TestCase):
    def setUp(self) -> None:
        self.connection = sqlite3.connect(":memory:")
        self.connection.row_factory = sqlite3.Row
        self.connection.executescript(
            """
            CREATE TABLE jobs(
                job_id TEXT, task_id TEXT, task_revision INTEGER, state TEXT,
                lease_owner TEXT, lease_generation INTEGER, lease_expires_at REAL
            );
            CREATE TABLE tasks(task_id TEXT, revision INTEGER, state TEXT);
            CREATE TABLE file_leases(
                scope TEXT, owner TEXT, generation INTEGER, expires_at REAL, job_id TEXT
            );
            INSERT INTO jobs VALUES('job-1','task-1',1,'running','owner',7,9999999999);
            INSERT INTO tasks VALUES('task-1',1,'active');
            INSERT INTO file_leases VALUES('Poincare/Test.lean','owner',7,9999999999,'job-1');
            """
        )
        self.capability = {
            "job_id": "job-1",
            "task_id": "task-1",
            "task_revision": 1,
            "lease_owner": "owner",
            "lease_token": 7,
            "allowed_paths": ["Poincare/Test.lean"],
        }

    def tearDown(self) -> None:
        self.connection.close()

    def test_exact_live_state_passes_and_every_authority_drift_fails(self) -> None:
        _validate_commit_fence_state(self.connection, self.capability)
        mutations = (
            "UPDATE jobs SET state='reviewing'",
            "UPDATE jobs SET lease_generation=8",
            "UPDATE jobs SET lease_expires_at=1",
            "UPDATE tasks SET state='superseded'",
            "UPDATE tasks SET revision=2",
            "UPDATE file_leases SET owner='other'",
            "UPDATE file_leases SET generation=8",
            "UPDATE file_leases SET expires_at=1",
            "UPDATE file_leases SET scope='Poincare/Other.lean'",
        )
        original = "\n".join(self.connection.iterdump())
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                candidate = sqlite3.connect(":memory:")
                candidate.row_factory = sqlite3.Row
                candidate.executescript(original)
                candidate.execute(mutation)
                with self.assertRaises(PiEngineError):
                    _validate_commit_fence_state(candidate, self.capability)
                candidate.close()


class JournalReplayBoundaryTest(unittest.TestCase):
    def test_temp_index_replay_and_rpc_tool_crosscheck_match_head_diff(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            worktree = root / "repo"
            artifacts = root / "artifacts"
            worktree.mkdir()
            artifacts.mkdir()
            target = worktree / "Test.lean"
            before = b"theorem x : True := by\n  trivial\n"
            after = b"theorem x : True := by\n  exact True.intro\n"
            target.write_bytes(before)
            subprocess.run(["git", "init", "-q", "-b", "codex/test"], cwd=worktree, check=True)
            subprocess.run(["git", "add", "."], cwd=worktree, check=True)
            subprocess.run(
                [
                    "git", "-c", "user.name=Harness Test",
                    "-c", "user.email=harness@example.invalid",
                    "commit", "-qm", "base",
                ],
                cwd=worktree,
                check=True,
            )
            patch_bytes = (
                b"diff --git a/Test.lean b/Test.lean\n"
                b"--- a/Test.lean\n+++ b/Test.lean\n"
                b"@@ -1,2 +1,2 @@\n theorem x : True := by\n"
                b"-  trivial\n+  exact True.intro\n"
            )
            journal = PatchJournal.create(artifacts, "job-1", "session-1")
            intent = journal.record_intent("call-1", ("Test.lean",), patch_bytes)
            subprocess.run(
                ["git", "apply", "--whitespace=error-all", "-"],
                cwd=worktree,
                input=patch_bytes,
                check=True,
            )
            journal.commit(
                intent,
                {"Test.lean": _sha(before)},
                {"Test.lean": _sha(after)},
            )
            journal.close()
            journal.dispose()
            replayed, committed = _replay_patch_journal(
                artifact_dir=artifacts,
                job_id="job-1",
                session_id="session-1",
                worktree=worktree,
                patch_limit=1024 * 1024,
            )
            live = subprocess.check_output(
                [
                    "git", "diff", "--binary", "--no-ext-diff", "--no-textconv",
                    "--no-color", "HEAD", "--",
                ],
                cwd=worktree,
            )
            self.assertEqual(replayed, live)
            self.assertEqual(len(committed), 1)

            tool_records = (
                {"type": "tool_execution_start", "toolCallId": "call-1", "toolName": "apply_patch_scoped"},
                {"type": "tool_execution_end", "toolCallId": "call-1", "toolName": "apply_patch_scoped"},
            )
            (artifacts / "tool-events.jsonl").write_text(
                "".join(json.dumps(item) + "\n" for item in tool_records),
                encoding="utf-8",
            )
            broker_records = (
                {"event": "rpc_request_received", "sequence": 1, "tool_call_id": "call-1", "tool_name": "apply_patch_scoped"},
                {
                    "event": "pi_tool_result", "sequence": 1,
                    "tool_call_id": "call-1", "tool_name": "apply_patch_scoped",
                    "details": {
                        "patch_sha256": intent.patch_sha256,
                        "journal_intent_sequence": intent.sequence,
                    },
                },
                {
                    "event": "rpc_request_terminal", "sequence": 1,
                    "tool_call_id": "call-1", "tool_name": "apply_patch_scoped",
                    "ok": True, "response_sent": True,
                },
            )
            (artifacts / "pi-broker-events.jsonl").write_text(
                "".join(json.dumps(item) + "\n" for item in broker_records),
                encoding="utf-8",
            )
            crosscheck = _crosscheck_tool_evidence(
                artifact_dir=artifacts,
                committed=committed,
            )
            self.assertEqual(crosscheck["valid"], True)


if __name__ == "__main__":
    unittest.main()
