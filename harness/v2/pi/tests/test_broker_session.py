from __future__ import annotations

import contextlib
import shutil
import subprocess
import tempfile
import threading
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from harness.v2.pi.broker import BrokerError, BrokerSession
from harness.v2.pi.journal import verify_patch_journal
from harness.v2.pi.quota import SharedArtifactQuota


class BrokerSessionTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name).resolve()
        self.worktree = self.base / "repo"
        self.artifacts = self.base / "artifacts"
        self.state = self.base / "state"
        self.control = self.base / "control"
        self.scratch = self.base / "lean-checks"
        for directory in (
            self.worktree,
            self.artifacts,
            self.state,
            self.control,
            self.scratch,
        ):
            directory.mkdir(mode=0o700)
        (self.worktree / "Poincare").mkdir()
        self.target = self.worktree / "Poincare/Test.lean"
        self.target.write_text("theorem x : True := by\n  trivial\n", encoding="utf-8")
        subprocess.run(
            ["git", "init", "-q", "-b", "codex/test"],
            cwd=self.worktree,
            check=True,
        )
        subprocess.run(["git", "add", "."], cwd=self.worktree, check=True)
        subprocess.run(
            [
                "git",
                "-c",
                "user.name=Harness Test",
                "-c",
                "user.email=harness@example.invalid",
                "commit",
                "-qm",
                "base",
            ],
            cwd=self.worktree,
            check=True,
        )
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=self.worktree, text=True
        ).strip()
        sparse = {
            "bwrap_path": "/sealed/bwrap",
            "systemd_run_path": "/sealed/systemd-run",
            "git_path": "/sealed/git",
            "immutable_lake_cache": "/sealed/cache",
            "toolchain_roots": "/sealed/toolchain",
            "base_commit": head,
            "base_tree": "1" * 40,
            "forbidden_host_paths": [str(self.control)],
            "memory_max_bytes": 1024,
            "tasks_max": 1,
            "cpu_quota_percent": 1,
            "process_limits": {},
        }
        self.capability = {
            "schema_version": "poincare.pi-capability.v1",
            "session_id": "session-1",
            "job_id": "job-1",
            "task_id": "task-1",
            "task_revision": 1,
            "state_dir": str(self.state),
            "control_root": str(self.control),
            "artifact_dir": str(self.artifacts),
            "worktree": str(self.worktree),
            "base_commit": head,
            "branch": "codex/test",
            "lease_owner": "owner",
            "lease_token": 1,
            "allowed_paths": ["Poincare/Test.lean"],
            "forbidden_paths": [],
            "readable_paths": ["Poincare/Test.lean"],
            "acceptance_commands": [
                [
                    "env",
                    "LEAN_NUM_THREADS=1",
                    "lake",
                    "env",
                    "lean",
                    "Poincare/Test.lean",
                ]
            ],
            "forbidden_added_tokens": [],
            "backend": {},
            "prompt_sha256": "0" * 64,
            "context_sha256": "1" * 64,
            "launched_at_epoch": 0,
            "deadline_epoch": 9_999_999_999,
            "lean_timeout_seconds": 30,
            "artifact_quota_bytes": 8 * 1024 * 1024,
            "extension_sha256": "2" * 64,
            "system_prompt_sha256": "3" * 64,
            "trusted_code": {},
            "lean_scratch_root": str(self.scratch),
            "sparse_lean": sparse,
        }
        self.quota = SharedArtifactQuota(
            self.artifacts, self.capability["artifact_quota_bytes"]
        )
        self.live = ({}, {}, self.worktree, self.artifacts)

    def request(
        self, sequence: int, call_id: str, tool: str, params: dict[str, object]
    ) -> dict[str, object]:
        return {
            "protocol": "poincare.pi-rpc.v1",
            "job_id": "job-1",
            "session_id": "session-1",
            "sequence": sequence,
            "tool_call_id": call_id,
            "tool": tool,
            "params": params,
        }

    def test_scoped_patch_is_journalled_and_request_identity_is_consumed(self) -> None:
        patch_text = """diff --git a/Poincare/Test.lean b/Poincare/Test.lean
--- a/Poincare/Test.lean
+++ b/Poincare/Test.lean
@@ -1,2 +1,2 @@
 theorem x : True := by
-  trivial
+  exact True.intro
"""
        with patch(
            "harness.v2.pi.broker._validate_live", return_value=self.live
        ), patch("harness.v2.pi.broker._live_guard", return_value=True):
            session = BrokerSession(self.capability, quota=self.quota)
            result = session.execute(
                self.request(1, "patch-1", "apply_patch_scoped", {"patch": patch_text})
            )
            with self.assertRaisesRegex(BrokerError, "replay|sequence"):
                session.execute(self.request(1, "patch-1", "git_diff", {}))
            session.close()

        committed = verify_patch_journal(
            self.artifacts, "job-1", "session-1"
        )
        self.assertEqual(len(committed), 1)
        self.assertEqual(committed[0].tool_call_id, "patch-1")
        self.assertEqual(result["details"]["patch_sha256"], committed[0].patch_sha256)
        self.assertIn("exact True.intro", self.target.read_text(encoding="utf-8"))

    def test_lean_check_uses_fresh_sparse_snapshot_and_cleans_it(self) -> None:
        def build(**kwargs: object) -> dict[str, object]:
            output = Path(kwargs["output_dir"])
            output.mkdir()
            (output / "Poincare").mkdir()
            shutil.copy2(self.target, output / "Poincare/Test.lean")
            return {"root": str(output), "tree_sha256": "a" * 64}

        def cleanup(*, sparse_snapshot: dict[str, object], checks_root: Path) -> None:
            self.assertEqual(checks_root, self.scratch)
            shutil.rmtree(Path(sparse_snapshot["root"]))

        process_result = SimpleNamespace(
            stdout=b"ok\n",
            stderr=b"",
            returncode=0,
            timed_out=False,
            output_limited=False,
            guard_cancelled=False,
            duration_seconds=0.1,
        )
        sandbox = {"profile_version": "poincare-lean-sparse-bwrap-v1"}
        mocks = (
            patch("harness.v2.pi.broker._validate_live", return_value=self.live),
            patch("harness.v2.pi.broker._live_guard", return_value=True),
            patch(
                "harness.v2.pi.broker.acquire_build_job_lock",
                return_value=contextlib.nullcontext(),
            ),
            patch("harness.v2.pi.broker.build_sparse_lean_snapshot", side_effect=build),
            patch(
                "harness.v2.pi.broker.audit_sparse_lean_bubblewrap",
                return_value=sandbox,
            ),
            patch(
                "harness.v2.pi.broker.bubblewrap_sparse_lean_argv",
                return_value=("/bin/true",),
            ),
            patch("harness.v2.pi.broker.sparse_lean_process_limits", return_value=None),
            patch("harness.v2.pi.broker.run_limited", return_value=process_result),
            patch(
                "harness.v2.pi.broker._systemd_user_environment",
                return_value={"PATH": "/nonexistent"},
            ),
            patch(
                "harness.v2.pi.broker.remove_sparse_lean_snapshot",
                side_effect=cleanup,
            ),
        )
        with contextlib.ExitStack() as stack:
            for mocked in mocks:
                stack.enter_context(mocked)
            session = BrokerSession(self.capability, quota=self.quota)
            result = session.execute(
                self.request(1, "lean-1", "lean_check", {"command_index": 0})
            )
            session.close()

        self.assertIn("Lean check passed", result["text"])
        self.assertEqual(list(self.scratch.iterdir()), [])
        manifest = self.artifacts / result["details"]["sandbox_manifest_artifact"]
        self.assertTrue(manifest.is_file())

    def test_out_of_order_duplicate_and_parallel_requests_fail_closed(self) -> None:
        entered = threading.Event()
        release = threading.Event()

        def blocking_read(*_args: object, **_kwargs: object) -> dict[str, object]:
            entered.set()
            self.assertTrue(release.wait(timeout=5))
            return {"text": "ok"}

        with patch(
            "harness.v2.pi.broker._validate_live", return_value=self.live
        ), patch(
            "harness.v2.pi.broker._tool_read_context", side_effect=blocking_read
        ):
            session = BrokerSession(self.capability, quota=self.quota)
            with self.assertRaisesRegex(BrokerError, "exactly 1"):
                session.execute(
                    self.request(2, "future", "read_context", {"path": "Poincare/Test.lean"})
                )

            worker_error: list[BaseException] = []

            def worker() -> None:
                try:
                    session.execute(
                        self.request(
                            1,
                            "first",
                            "read_context",
                            {"path": "Poincare/Test.lean"},
                        )
                    )
                except BaseException as exc:  # pragma: no cover - asserted below
                    worker_error.append(exc)

            thread = threading.Thread(target=worker)
            thread.start()
            self.assertTrue(entered.wait(timeout=5))
            with self.assertRaisesRegex(BrokerError, "parallel"):
                session.execute(
                    self.request(
                        2,
                        "parallel",
                        "read_context",
                        {"path": "Poincare/Test.lean"},
                    )
                )
            release.set()
            thread.join(timeout=5)
            self.assertFalse(thread.is_alive())
            self.assertEqual(worker_error, [])
            with self.assertRaisesRegex(BrokerError, "replay"):
                session.execute(
                    self.request(
                        2,
                        "first",
                        "read_context",
                        {"path": "Poincare/Test.lean"},
                    )
                )
            session.close()


if __name__ == "__main__":
    unittest.main()
