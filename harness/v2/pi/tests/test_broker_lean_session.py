from __future__ import annotations

import contextlib
import hashlib
import shutil
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from harness.v2.pi.broker import BrokerError, BrokerSession, _BrokerLeanSession, _tool_lean_check
from harness.v2.pi.lean_session import LeanSessionUnavailable
from harness.v2.pi.quota import SharedArtifactQuota
from harness.v2.pi.security import SecurityError
from harness.v2.pi.tests import test_broker_session as broker_session_fixture


class StubSession:
    """Lifecycle spy; compiler semantics are tested with real Lean separately."""

    instances: list[StubSession] = []
    unsupported = False

    def __init__(self, argv: tuple[str, ...], **kwargs: object) -> None:
        self.argv, self.alive, self.version = argv, True, 0
        self.__class__.instances.append(self)

    def close(self) -> None:
        self.alive = False

    def check(self, text: str, **kwargs: object) -> object:
        if self.unsupported:
            raise LeanSessionUnavailable("pinned Lean server lacks waitForDiagnostics")
        self.version += 1
        return SimpleNamespace(stdout=b'{"diagnostics":[]}\n', stderr=b"", returncode=0,
            timed_out=False, output_limited=False, guard_cancelled=False,
            duration_seconds=0.01, document_version=self.version,
            reused_success=False, phase_seconds={"import_load_and_elaboration": 0.01})


class BrokerLeanSessionTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.root, self.scratch, self.artifacts = [self.directory / name for name in ("repo", "scratch", "artifacts")]
        for directory in (self.root, self.scratch, self.artifacts):
            directory.mkdir(mode=0o700)
        (self.root / "Poincare").mkdir()
        self.target = self.root / "Poincare/Test.lean"
        self.helper = self.root / "Poincare/Helper.lean"
        self.target.write_text("import Init\nnamespace X\ntheorem x : True := by trivial\n")
        self.helper.write_text("theorem helper : True := by trivial\n")
        for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            (self.root / name).write_text("config\n")
        self.config = dict(base_commit="1" * 40, base_tree="2" * 40,
            forbidden_host_paths=[str(self.artifacts)], bwrap_path="/sealed/bwrap",
            systemd_run_path="/sealed/systemd-run", git_path="/sealed/git",
            immutable_lake_cache="/sealed/cache", toolchain_roots="/sealed/lean",
            memory_max_bytes=1024, tasks_max=2, cpu_quota_percent=100, process_limits={})
        self.capability = dict(job_id="job", session_id="session", base_commit="1" * 40,
            deadline_epoch=9999999999, lean_timeout_seconds=5, state_dir=str(self.directory),
            sparse_lean=self.config, trusted_code={}, readable_paths=["Poincare/Test.lean", "Poincare/Helper.lean"],
            acceptance_commands=[["lake", "env", "lean", "Poincare/Test.lean"]])
        self.quota = SharedArtifactQuota(self.artifacts, 8 * 1024 * 1024)
        self.manager = _BrokerLeanSession()
        self.addCleanup(self.manager.close)
        StubSession.instances, StubSession.unsupported = [], False
        stack = contextlib.ExitStack()
        self.addCleanup(stack.close)
        for mocked in (
            patch("harness.v2.pi.broker._validate_live", return_value=({}, {}, self.root, self.artifacts)),
            patch("harness.v2.pi.broker._live_guard", return_value=True),
            patch("harness.v2.pi.broker.acquire_build_job_lock", side_effect=lambda *args, **kwargs: contextlib.nullcontext()),
            patch("harness.v2.pi.broker.build_sparse_lean_snapshot", side_effect=self.snapshot),
            patch("harness.v2.pi.broker.audit_sparse_lean_bubblewrap", return_value={"profile_version": "sparse-test"}),
            patch("harness.v2.pi.broker.attest_protected_sparse_cache", side_effect=SecurityError("no protected mount")),
            patch("harness.v2.pi.broker.bubblewrap_sparse_lean_server_argv", return_value=("/sandbox/lean", "--server")),
            patch("harness.v2.pi.broker.bubblewrap_sparse_lean_argv", return_value=("/sandbox/lean", "/work/Poincare/Test.lean")),
            patch("harness.v2.pi.broker.validate_sparse_lean_session", return_value={"profile_version": "sparse-test"}),
            patch("harness.v2.pi.broker.sparse_lean_process_limits", return_value=None),
            patch("harness.v2.pi.broker._systemd_user_environment", return_value={"PATH": "/nonexistent"}),
            patch("harness.v2.pi.broker._lean_scratch_root", return_value=self.scratch),
            patch("harness.v2.pi.broker.remove_sparse_lean_snapshot", side_effect=lambda **kwargs: shutil.rmtree(kwargs["sparse_snapshot"]["root"])),
            patch("harness.v2.pi.broker.LeanProofSession", StubSession),
            patch("harness.v2.pi.broker.sys.platform", "linux"),
        ):
            stack.enter_context(mocked)
        self.addCleanup(self.manager.close)

    def snapshot(self, **kwargs: object) -> dict[str, object]:
        destination = Path(kwargs["output_dir"])
        destination.mkdir()
        (destination / "Poincare").mkdir()
        files = []
        for relative in ("Poincare/Test.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            data = (self.root / relative).read_bytes()
            (destination / relative).write_bytes(data)
            files.append({"path": relative, "sha256": hashlib.sha256(data).hexdigest(), "size_bytes": len(data)})
        return {"root": str(destination), "tree_sha256": hashlib.sha256(repr(files).encode()).hexdigest(), "files": files}

    def check(self, call_id: str, **params: object) -> dict[str, object]:
        return _tool_lean_check(self.capability, self.root, self.quota, call_id,
            {"command_index": 0, **params}, self.manager)

    def test_body_edits_reuse_process_header_config_and_helper_changes_restart(self) -> None:
        first = self.check("first")
        self.target.write_text(self.target.read_text().replace("trivial", "exact True.intro"))
        second = self.check("second", fresh=False)
        self.assertTrue(first["details"]["restarted"])
        self.assertFalse(second["details"]["restarted"])
        self.assertEqual(len(StubSession.instances), 1)
        self.target.write_text(self.target.read_text().replace("import Init", "import Lean"))
        self.assertTrue(self.check("import-change")["details"]["restarted"])
        self.helper.write_text(self.helper.read_text() + "theorem helper2 : True := by trivial\n")
        self.assertTrue(self.check("helper-change")["details"]["restarted"])
        (self.root / "lean-toolchain").write_text("new compiler generation\n")
        self.assertTrue(self.check("toolchain-change")["details"]["restarted"])
        self.assertEqual(len(StubSession.instances), 4)
        self.assertTrue(all(not instance.alive for instance in StubSession.instances[:-1]))
        self.manager.close()
        self.assertEqual(list(self.scratch.iterdir()), [])

    def test_dependency_attestation_failure_closes_instead_of_reusing_success(self) -> None:
        self.check("first")
        with patch("harness.v2.pi.broker.validate_sparse_lean_session", side_effect=SecurityError("cache generation changed")):
            with self.assertRaisesRegex(SecurityError, "cache generation"):
                self.check("changed-cache")
        self.assertFalse(StubSession.instances[0].alive)
        self.assertEqual(list(self.scratch.iterdir()), [])

    def test_unsupported_sync_fallback_preserves_distinct_append_only_artifacts(self) -> None:
        StubSession.unsupported = True
        fresh = SimpleNamespace(stdout=b"fresh ok\n", stderr=b"", returncode=0,
            timed_out=False, output_limited=False, guard_cancelled=False, duration_seconds=0.01)
        with patch("harness.v2.pi.broker.run_limited", return_value=fresh):
            result = self.check("unsupported")
        self.assertEqual(result["details"]["verification_mode"], "fresh_compiler")
        self.assertIn("waitForDiagnostics", result["details"]["session_fallback_reason"])
        artifacts = list((self.artifacts / "pi-tools").iterdir())
        self.assertEqual(len([item for item in artifacts if item.name.endswith(".lean-sandbox.json")]), 1)
        self.assertEqual(len([item for item in artifacts if item.name.endswith(".lean-session-sandbox.json")]), 1)
        self.assertEqual(list(self.scratch.iterdir()), [])

    def test_explicit_fresh_and_io_automatically_use_fresh_compiler(self) -> None:
        fresh = SimpleNamespace(stdout=b"ok", stderr=b"", returncode=0,
            timed_out=False, output_limited=False, guard_cancelled=False, duration_seconds=0.01)
        with patch("harness.v2.pi.broker.run_limited", return_value=fresh):
            requested = self.check("fresh", fresh=True)
            self.assertEqual(requested["details"]["session_fallback_reason"], "caller_requested_fresh")
            self.target.write_text(self.target.read_text() + 'run_cmd pure ()\n')
            automatic = self.check("io")
            self.assertEqual(automatic["details"]["session_fallback_reason"], "explicit_io_or_metaprogramming")
        self.assertEqual(StubSession.instances, [])
        with self.assertRaisesRegex(BrokerError, "boolean"):
            self.check("invalid-fresh", fresh="yes")

    def test_patch_of_another_file_and_revoke_close_retained_session(self) -> None:
        self.check("first")
        self.manager.invalidate_on_patch(["Poincare/Test.lean"])
        self.assertTrue(StubSession.instances[0].alive)
        self.manager.invalidate_on_patch(["Poincare/Helper.lean"])
        self.assertFalse(StubSession.instances[0].alive)
        self.check("second")
        with patch("harness.v2.pi.broker._validate_live", side_effect=BrokerError("lease revoked")):
            with self.assertRaisesRegex(BrokerError, "lease revoked"):
                self.check("revoked")
        self.assertFalse(StubSession.instances[-1].alive)
        self.assertEqual(list(self.scratch.iterdir()), [])


class BrokerFinalFreshTest(unittest.TestCase):
    setUp = broker_session_fixture.BrokerSessionTest.setUp

    def test_clean_close_runs_final_fresh_once_and_journals_it(self) -> None:
        with patch("harness.v2.pi.broker._validate_live", return_value=self.live), \
             patch("harness.v2.pi.broker._live_guard", return_value=True), \
             patch("harness.v2.pi.broker._tool_lean_check", return_value={"details": {
                 "returncode": 0, "timed_out": False, "output_limited": False,
                 "verification_mode": "fresh_compiler"}}) as fresh:
            session = BrokerSession(self.capability, quota=self.quota)
            session._incremental_command_indices.add(0)
            session.close()
            session.close()
        fresh.assert_called_once()
        self.assertEqual(fresh.call_args.args[-1], {"command_index": 0})
        self.assertIn("pi_final_fresh_lean_check", (self.artifacts / "pi-broker-events.jsonl").read_text())

    def test_final_fresh_failure_rejects_sealing_and_retains_evidence(self) -> None:
        with patch("harness.v2.pi.broker._validate_live", return_value=self.live), \
             patch("harness.v2.pi.broker._live_guard", return_value=True), \
             patch("harness.v2.pi.broker._tool_lean_check", return_value={"details": {
                 "returncode": 1, "timed_out": False, "output_limited": False}}):
            session = BrokerSession(self.capability, quota=self.quota)
            session._incremental_command_indices.add(0)
            with self.assertRaisesRegex(BrokerError, "final fresh Lean"):
                session.close()
        self.assertIn('"returncode":1', (self.artifacts / "pi-broker-events.jsonl").read_text())

    def test_revoked_job_cannot_launch_final_fresh_check(self) -> None:
        with patch("harness.v2.pi.broker._validate_live", return_value=self.live), \
             patch("harness.v2.pi.broker._live_guard", return_value=False), \
             patch("harness.v2.pi.broker._tool_lean_check") as fresh:
            session = BrokerSession(self.capability, quota=self.quota)
            session._incremental_command_indices.add(0)
            session.close()
        fresh.assert_not_called()


if __name__ == "__main__":
    unittest.main()
