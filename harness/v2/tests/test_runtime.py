from __future__ import annotations

import copy
import fcntl
import hashlib
import json
import os
import shlex
import shutil
import sqlite3
import subprocess
import tempfile
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from pathlib import Path
from threading import Barrier, Event
from unittest.mock import patch

from harness.v2.runtime import (
    ConflictError,
    HarnessError,
    HarnessStore,
    LeaseError,
    TransitionError,
)
from harness.v2.runtime.migrations import MIGRATIONS
from harness.v2.runtime.validation import scopes_overlap


BASE_COMMIT = "a" * 40
OTHER_COMMIT = "c" * 40
GIT_EXECUTABLE = Path(shutil.which("git") or "/usr/bin/git").resolve()
DECLARATION_PROBE_ARGV = [
    "env",
    "LEAN_NUM_THREADS=1",
    "lake",
    "env",
    "lean",
    "--stdin",
]


class FakeClock:
    def __init__(self) -> None:
        self.value = datetime(2026, 7, 19, 12, 0, tzinfo=timezone.utc)

    def __call__(self) -> datetime:
        return self.value

    def advance(self, seconds: int) -> None:
        self.value += timedelta(seconds=seconds)


class LockAwareClock:
    """Observe whether each sample occurs while the caller owns SQLite's write lock."""

    def __init__(self, database: Path, source: FakeClock) -> None:
        self.database = database
        self.source = source
        self.enabled = False
        self.samples_inside_transaction: list[bool] = []

    def __call__(self) -> datetime:
        if self.enabled:
            connection = sqlite3.connect(self.database, timeout=0, isolation_level=None)
            try:
                try:
                    connection.execute("BEGIN IMMEDIATE")
                except sqlite3.OperationalError as error:
                    if "locked" not in str(error).lower():
                        raise
                    self.samples_inside_transaction.append(True)
                else:
                    self.samples_inside_transaction.append(False)
                    connection.rollback()
            finally:
                connection.close()
        return self.source()


def task_record(
    task_id: str,
    allowed_path: str = "Poincare/Example.lean",
    base_commit: str = BASE_COMMIT,
) -> dict:
    return {
        "schema_version": "2.0",
        "id": task_id,
        "revision": 1,
        "status": "proposed",
        "base_commit": base_commit,
        "objective": {
            "title": f"Close {task_id}",
            "statement": "Prove one frozen theorem-shaped objective.",
            "frozen_lean_type": "Prop",
            "deliverables": ["One checked declaration"],
        },
        "scope": {
            "allowed_paths": [allowed_path],
            "forbidden_paths": ["Poincare.lean"],
        },
        "context": {"files": [], "symbols": ["ExampleTarget"], "depends_on": []},
        "acceptance": {
            "commands": [["git", "diff", "--check"]],
            "required_declarations": ["ExampleTarget"],
            "forbidden_added_tokens": ["sorry", "admit", "axiom", "native_decide"],
        },
        "stop_conditions": ["The frozen type changed"],
        "budget": {
            "max_attempts": 3,
            "wall_clock_minutes": 30,
            "max_output_tokens": 4000,
            "disk_mb": 512,
        },
    }


def task_revision(
    task_id: str, revision: int, base_commit: str = BASE_COMMIT
) -> dict:
    record = task_record(task_id, base_commit=base_commit)
    record["revision"] = revision
    record["supersedes"] = task_id
    return record


def job_record(
    task_id: str,
    worktree_root: str | Path = "/tmp/poincare-worktrees",
    attempt: int = 1,
    task_revision_number: int = 1,
    base_commit: str = BASE_COMMIT,
) -> dict:
    job_id = f"{task_id}-a{attempt:02d}"
    return {
        "schema_version": "2.0",
        "id": job_id,
        "task_id": task_id,
        "task_revision": task_revision_number,
        "attempt": attempt,
        "state": "queued",
        "backend": {
            "kind": "leanstral",
            "model": "test-model",
            "model_revision": "test-revision",
            "endpoint": "http://127.0.0.1:8000/v1",
            "sampling": {"max_tokens": 4000, "temperature": 0},
        },
        "workspace": {
            "base_commit": base_commit,
            "worktree": str(Path(worktree_root) / job_id),
            "branch": f"codex/{task_id}/a{attempt:02d}",
            "lease_owner": "not-active-until-claim",
            "lease_expires_at": "2099-01-01T00:00:00Z",
        },
        "artifacts": {
            "directory": f"harness/v2/state/jobs/{job_id}",
            "prompt_sha256": "0" * 64,
            "context_sha256": "1" * 64,
        },
        "gate": {"status": "not_run"},
    }


class RuntimeTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name).resolve()
        self.integration_root = self.base / "integration"
        self.worktree_root = self.base / "worktrees"
        self.integration_root.mkdir()
        self.worktree_root.mkdir()
        subprocess.run(
            ["git", "init", "--quiet", str(self.integration_root)], check=True
        )
        (self.integration_root / "README").write_text("fixture\n", encoding="utf-8")
        subprocess.run(
            ["git", "-C", str(self.integration_root), "add", "README"], check=True
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(self.integration_root),
                "-c",
                "user.name=Harness Test",
                "-c",
                "user.email=harness@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "fixture",
            ],
            check=True,
        )
        self.base_commit = subprocess.run(
            ["git", "-C", str(self.integration_root), "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        self.accepted_commit = self.base_commit
        self.accepted_tree = subprocess.run(
            ["git", "-C", str(self.integration_root), "rev-parse", "HEAD^{tree}"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        self.state_dir = self.integration_root / "harness" / "v2" / "state"
        self.clock = FakeClock()
        self.store = HarnessStore(
            self.state_dir,
            clock=self.clock,
            worktree_root=self.worktree_root,
            integration_root=self.integration_root,
            git_executable=GIT_EXECUTABLE,
        )
        self.store.initialize()
        self.store.set_dispatch_state("running", actor="runtime-test-setup")

    def job_record(
        self, task_id: str, attempt: int = 1, task_revision_number: int = 1
    ) -> dict:
        return job_record(
            task_id,
            self.worktree_root,
            attempt=attempt,
            task_revision_number=task_revision_number,
            base_commit=self.base_commit,
        )

    def task_record(
        self, task_id: str, allowed_path: str = "Poincare/Example.lean"
    ) -> dict:
        return task_record(task_id, allowed_path, base_commit=self.base_commit)

    def task_revision(self, task_id: str, revision: int) -> dict:
        return task_revision(task_id, revision, base_commit=self.base_commit)

    def test_runtime_git_uses_injected_attested_executable_and_scrubbed_environment(
        self,
    ) -> None:
        wrapper = self.base / "attested-git"
        log = self.base / "git-environment.log"
        wrapper.write_text(
            "#!/bin/sh\n"
            + "printf '%s\\t%s\\t%s\\t%s\\t%s\\n' \"$0\" \"$PATH\" \"${HOME-unset}\" "
            + '"${GIT_CONFIG_NOSYSTEM-unset}" "${GIT_NO_REPLACE_OBJECTS-unset}" '
            + f">> {shlex.quote(str(log))}\n"
            + f"exec {shlex.quote(str(GIT_EXECUTABLE))} \"$@\"\n",
            encoding="utf-8",
        )
        wrapper.chmod(0o500)
        store = HarnessStore(
            self.state_dir,
            clock=self.clock,
            worktree_root=self.worktree_root,
            integration_root=self.integration_root,
            git_executable=wrapper,
        )
        self.assertEqual(
            store._git_text(self.integration_root, "rev-parse", "HEAD"),
            self.base_commit,
        )
        executable, path, home, no_system, no_replacements = log.read_text(
            encoding="utf-8"
        ).strip().split("\t")
        self.assertEqual(Path(executable), wrapper)
        self.assertEqual(path, "/usr/bin:/bin")
        self.assertEqual(home, "/nonexistent")
        self.assertEqual(no_system, "1")
        self.assertEqual(no_replacements, "1")

    def test_runtime_git_rejects_binary_drift_after_initialization(self) -> None:
        wrapper = self.base / "attested-git"
        wrapper.write_text(
            f"#!/bin/sh\nexec {shlex.quote(str(GIT_EXECUTABLE))} \"$@\"\n",
            encoding="utf-8",
        )
        wrapper.chmod(0o500)
        store = HarnessStore(
            self.state_dir,
            clock=self.clock,
            worktree_root=self.worktree_root,
            integration_root=self.integration_root,
            git_executable=wrapper,
        )
        wrapper.chmod(0o700)
        wrapper.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
        wrapper.chmod(0o500)
        with self.assertRaisesRegex(TransitionError, "re-attestation"):
            store._git_text(self.integration_root, "rev-parse", "HEAD")

    def test_runtime_git_rejects_relative_authority_path(self) -> None:
        with self.assertRaisesRegex(HarnessError, "absolute and normalized"):
            HarnessStore(self.state_dir, git_executable="git")

    def create_worktree(self, job: dict) -> None:
        path = Path(job["workspace"]["worktree"])
        if path.exists():
            return
        subprocess.run(
            [
                "git",
                "-C",
                str(self.integration_root),
                "worktree",
                "add",
                "--quiet",
                "--detach",
                str(path),
                self.base_commit,
            ],
            check=True,
        )

    def enqueue_job(self, job: dict) -> dict:
        payload = self.store.enqueue_job(job)
        self.create_worktree(job)
        return payload

    def make_active_job(
        self, task_id: str, allowed_path: str = "Poincare/Example.lean"
    ) -> str:
        self.store.import_task(self.task_record(task_id, allowed_path))
        self.store.transition_task(task_id, "ready")
        job = self.job_record(task_id)
        self.enqueue_job(job)
        return job["id"]

    def claim_and_run(self, job_id: str, *, owner: str = "worker") -> int:
        claimed = self.store.claim_job(
            job_id=job_id, owner=owner, lease_seconds=60
        )
        token = claimed["runtime"]["lease_token"]
        self.store.heartbeat_job(
            job_id,
            owner=owner,
            lease_token=token,
            lease_seconds=60,
            to_state="running",
        )
        return token

    def hold_execution_fence(self, job_id: str) -> int:
        path = self.store.job_execution_lock_path(job_id)
        descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return descriptor

    def make_reviewing_job(
        self,
        task_id: str,
        *,
        worker: str = "worker",
        task: dict | None = None,
    ) -> tuple[str, int, dict]:
        if task is None:
            job_id = self.make_active_job(task_id)
        else:
            self.store.import_task(task)
            self.store.transition_task(task_id, "ready")
            job = self.job_record(task_id)
            self.enqueue_job(job)
            job_id = job["id"]
        token = self.claim_and_run(job_id, owner=worker)
        reviewing = self.store.heartbeat_job(
            job_id,
            owner=worker,
            lease_token=token,
            lease_seconds=60,
            to_state="reviewing",
        )
        return job_id, token, reviewing

    def valid_gate_document(
        self,
        job_id: str,
        *,
        accepted_commit: str | None = None,
        status: str = "passed",
    ) -> dict:
        if accepted_commit is None:
            accepted_commit = self.accepted_commit
        job = self.store.get_job(job_id)
        task = self.store.get_task(
            job["job"]["task_id"], job["job"]["task_revision"]
        )["task"]
        artifact_dir = Path(job["runtime"]["artifact_directory"])
        declarations: list[dict] = []
        for index, symbol in enumerate(
            task["acceptance"].get("required_declarations", [])
        ):
            source_lines = ["import Poincare", f"#check {symbol}"]
            if index == 0:
                source_lines.append(
                    f"#check ({symbol} : {task['objective']['frozen_lean_type']})"
                )
            source = "\n".join(source_lines) + "\n"
            output_dir = artifact_dir / "declaration-probes"
            output_dir.mkdir(exist_ok=True)
            stdout_path = output_dir / f"{index}.stdout"
            stderr_path = output_dir / f"{index}.stderr"
            stdout_content = f"{symbol} checked\n".encode()
            stderr_content = b""
            stdout_path.write_bytes(stdout_content)
            stderr_path.write_bytes(stderr_content)
            declarations.append(
                {
                    "symbol": symbol,
                    "source": source,
                    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                    "argv": DECLARATION_PROBE_ARGV,
                    "status": "passed",
                    "exit_code": 0,
                    "stdout_path": stdout_path.relative_to(artifact_dir).as_posix(),
                    "stdout_sha256": hashlib.sha256(stdout_content).hexdigest(),
                    "stderr_path": stderr_path.relative_to(artifact_dir).as_posix(),
                    "stderr_sha256": hashlib.sha256(stderr_content).hexdigest(),
                }
            )
        commands = [
            {"argv": argv, "status": "passed", "exit_code": 0}
            for argv in task["acceptance"]["commands"]
        ]
        if status == "failed":
            commands[0] = {
                "argv": task["acceptance"]["commands"][0],
                "status": "failed",
                "exit_code": 1,
            }
        return {
            "schema_version": "2.0",
            "status": status,
            "accepted_commit": accepted_commit,
            "accepted_tree": self.accepted_tree,
            "commands": commands,
            "declarations": declarations,
        }

    def write_gate(self, job_id: str, document: dict | None = None) -> Path:
        job = self.store.get_job(job_id)
        gate = Path(job["runtime"]["artifact_directory"]) / "gate.json"
        if document is None:
            document = self.valid_gate_document(job_id)
        gate.write_text(json.dumps(document) + "\n", encoding="utf-8")
        return gate

    def pass_job(
        self,
        job_id: str,
        *,
        reviewer: str = "codex-reviewer",
        accepted_commit: str | None = None,
        exit_reason: str = "independent gate and review passed",
    ) -> dict:
        if accepted_commit is None:
            accepted_commit = self.accepted_commit
        self.write_gate(
            job_id,
            self.valid_gate_document(job_id, accepted_commit=accepted_commit),
        )
        return self.store.review_job(
            job_id,
            reviewer=reviewer,
            state="passed",
            exit_reason=exit_reason,
            gate_status="passed",
            gate_result="gate.json",
            accepted_commit=accepted_commit,
        )

    def test_task_job_and_independent_review_transitions(self) -> None:
        record = self.task_record("state-task")
        self.assertEqual(self.store.import_task(record)["task"]["status"], "proposed")
        self.store.transition_task("state-task", "ready")
        self.enqueue_job(self.job_record("state-task"))
        claimed = self.store.claim_job(
            job_id="state-task-a01", owner="worker-one", lease_seconds=60
        )
        token = claimed["runtime"]["lease_token"]
        self.store.heartbeat_job(
            "state-task-a01",
            owner="worker-one",
            lease_token=token,
            lease_seconds=60,
            to_state="running",
        )
        with self.assertRaises(TransitionError):
            self.store.finish_job(
                "state-task-a01",
                owner="worker-one",
                lease_token=token,
                state="passed",
                exit_reason="worker tried to self-promote",
            )
        self.store.heartbeat_job(
            "state-task-a01",
            owner="worker-one",
            lease_token=token,
            lease_seconds=60,
            to_state="reviewing",
        )
        self.write_gate("state-task-a01")
        with self.assertRaises(TransitionError):
            self.store.review_job(
                "state-task-a01",
                reviewer="worker-one",
                state="passed",
                exit_reason="self review",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=self.accepted_commit,
            )
        passed = self.store.review_job(
            "state-task-a01",
            reviewer="codex-reviewer",
            state="passed",
            exit_reason="independent gate and review passed",
            gate_status="passed",
            gate_result="gate.json",
            accepted_commit=self.accepted_commit,
        )
        self.assertEqual(passed["job"]["state"], "passed")
        self.assertEqual(passed["job"]["gate"]["result_path"], "gate.json")
        self.assertFalse(Path(passed["job"]["gate"]["result_path"]).is_absolute())
        self.assertEqual(passed["runtime"]["reviewer_identity"], "codex-reviewer")
        self.assertEqual(self.store.get_task("state-task")["task"]["status"], "active")

    def test_review_requires_live_complete_lease_and_rejects_prior_worker(self) -> None:
        job_id, _, _ = self.make_reviewing_job("lease-review", worker="worker-one")
        self.write_gate(job_id)
        self.clock.advance(61)
        with self.assertRaises(LeaseError):
            self.store.review_job(
                job_id,
                reviewer="codex-reviewer",
                state="passed",
                exit_reason="too late",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=self.accepted_commit,
            )
        recovered = self.store.claim_job(
            job_id=job_id, owner="worker-two", lease_seconds=60
        )
        self.assertGreater(recovered["runtime"]["lease_token"], 1)
        with self.assertRaises(TransitionError):
            self.store.review_job(
                job_id,
                reviewer="worker-one",
                state="passed",
                exit_reason="prior worker self review",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=self.accepted_commit,
            )

    def test_blocked_task_requires_exact_job_evidence(self) -> None:
        job_id = self.make_active_job("blocked-task")
        token = self.claim_and_run(job_id)
        self.store.finish_job(
            job_id,
            owner="worker",
            lease_token=token,
            state="blocked",
            exit_reason="Unknown identifier Exact.Resisting.Shape",
        )
        blocked = self.store.transition_task(
            "blocked-task",
            "blocked",
            blocked_reason="Exact.Resisting.Shape cannot be constructed in scope",
            evidence_job_id=job_id,
        )
        self.assertEqual(blocked["task"]["status"], "blocked")
        self.assertEqual(blocked["runtime"]["blocked_evidence_job_id"], job_id)

    def test_blocked_task_accepts_three_same_shape_interrupted_jobs(self) -> None:
        task_id = "repeated-interrupted-task"
        first = self.make_active_job(task_id)
        first_token = self.claim_and_run(first, owner="supervisor-one")
        self.store.finish_job(
            first,
            owner="supervisor-one",
            lease_token=first_token,
            state="interrupted",
            exit_reason="pi_execution_unsuccessful",
        )

        interrupted_jobs = [first]
        for attempt in (2, 3):
            job = self.job_record(task_id, attempt=attempt)
            self.enqueue_job(job)
            token = self.claim_and_run(job["id"], owner=f"supervisor-{attempt}")
            self.store.finish_job(
                job["id"],
                owner=f"supervisor-{attempt}",
                lease_token=token,
                state="interrupted",
                exit_reason="pi_execution_unsuccessful",
            )
            interrupted_jobs.append(job["id"])

        blocked = self.store.transition_task(
            task_id,
            "blocked",
            blocked_reason="three supervised attempts ended on one execution invariant",
            evidence_job_id=interrupted_jobs[-1],
        )
        self.assertEqual(blocked["task"]["status"], "blocked")
        self.assertEqual(
            blocked["runtime"]["blocked_evidence_job_id"], interrupted_jobs[-1]
        )
        connection = self.store._connect()
        try:
            event = connection.execute(
                """
                SELECT details_json FROM task_events
                WHERE task_id = ? AND to_state = 'blocked'
                ORDER BY sequence DESC LIMIT 1
                """,
                (task_id,),
            ).fetchone()
        finally:
            connection.close()
        self.assertEqual(
            json.loads(event["details_json"])["repeated_interrupted_job_ids"],
            interrupted_jobs,
        )

    def test_blocked_task_rejects_nonrepeated_interrupted_evidence(self) -> None:
        task_id = "single-interrupted-task"
        job_id = self.make_active_job(task_id)
        token = self.claim_and_run(job_id, owner="supervisor")
        self.store.finish_job(
            job_id,
            owner="supervisor",
            lease_token=token,
            state="interrupted",
            exit_reason="pi_execution_unsuccessful",
        )
        with self.assertRaisesRegex(
            TransitionError, "requires three same-Task worker-finished Jobs"
        ):
            self.store.transition_task(
                task_id,
                "blocked",
                blocked_reason="one interrupted attempt is not enough evidence",
                evidence_job_id=job_id,
            )

    def test_glob_scopes_are_conservative_and_claims_serialize(self) -> None:
        self.assertTrue(scopes_overlap("foo*/a*", "foobar*/a?"))
        self.assertTrue(
            scopes_overlap("Poincare/Alpha/*.lean", "Poincare/Beta/*.lean")
        )
        first = self.make_active_job("glob-one", "Poincare/Alpha/*.lean")
        second = self.make_active_job("glob-two", "Poincare/Beta/*.lean")
        self.store.claim_job(job_id=first, owner="worker-one", lease_seconds=30)
        with self.assertRaises(LeaseError):
            self.store.claim_job(job_id=second, owner="worker-two", lease_seconds=30)
        self.clock.advance(31)
        self.assertEqual(
            self.store.claim_job(
                job_id=second, owner="worker-two", lease_seconds=30
            )["job"]["state"],
            "preparing",
        )

    def test_recovery_increments_fencing_token(self) -> None:
        job_id = self.make_active_job("recover-task")
        first = self.store.claim_job(job_id=job_id, owner="worker-a", lease_seconds=10)
        self.clock.advance(11)
        recovered = self.store.claim_job(
            job_id=job_id, owner="worker-b", lease_seconds=10
        )
        self.assertGreater(
            recovered["runtime"]["lease_token"], first["runtime"]["lease_token"]
        )
        with self.assertRaises(LeaseError):
            self.store.heartbeat_job(
                job_id,
                owner="worker-a",
                lease_token=first["runtime"]["lease_token"],
                lease_seconds=10,
            )

    def test_queued_only_claim_never_recovers_an_expired_active_job(self) -> None:
        expired = self.make_active_job("queued-only-expired")
        self.store.claim_job(job_id=expired, owner="worker-a", lease_seconds=10)
        queued = self.make_active_job("queued-only-fresh", "Poincare/Fresh.lean")
        self.clock.advance(11)

        claimed = self.store.claim_job(
            owner="automatic-worker", lease_seconds=60, queued_only=True
        )
        self.assertEqual(claimed["job"]["id"], queued)
        self.assertEqual(self.store.get_job(expired)["job"]["state"], "preparing")
        with self.assertRaisesRegex(ConflictError, "queued-only"):
            self.store.claim_job(
                job_id=expired,
                owner="automatic-worker",
                lease_seconds=60,
                queued_only=True,
            )

    def test_durable_dispatch_stop_serializes_with_claim_and_start(self) -> None:
        job_id = self.make_active_job("dispatch-stop")
        stopped = self.store.set_dispatch_state("stopped", actor="deploy-stop")
        self.assertEqual(stopped["desired_state"], "stopped")
        with self.assertRaisesRegex(LeaseError, "durably stopped"):
            self.store.claim_job(job_id=job_id, owner="worker", lease_seconds=60)

        running = self.store.set_dispatch_state("running", actor="deploy-launch")
        self.assertEqual(running["generation"], stopped["generation"] + 1)
        claimed = self.store.claim_job(
            job_id=job_id, owner="worker", lease_seconds=60
        )
        token = claimed["runtime"]["lease_token"]
        self.store.set_dispatch_state("stopped", actor="deploy-stop")
        with self.assertRaisesRegex(LeaseError, "closed dispatch generation"):
            self.store.heartbeat_job(
                job_id,
                owner="worker",
                lease_token=token,
                lease_seconds=60,
                to_state="running",
            )
        with self.assertRaisesRegex(TransitionError, "cannot restart while active Job"):
            self.store.set_dispatch_state("running", actor="deploy-relaunch")
        with self.assertRaisesRegex(LeaseError, "closed dispatch generation"):
            self.store.heartbeat_job(
                job_id,
                owner="worker",
                lease_token=token,
                lease_seconds=60,
                to_state="running",
            )

    def test_running_job_can_drain_while_stopped_but_not_after_relaunch(self) -> None:
        job_id = self.make_active_job("graceful-drain")
        token = self.claim_and_run(job_id, owner="worker")
        self.store.set_dispatch_state("stopped", actor="graceful-stop")
        renewed = self.store.heartbeat_job(
            job_id,
            owner="worker",
            lease_token=token,
            lease_seconds=60,
        )
        self.assertEqual(renewed["job"]["state"], "running")
        reviewing = self.store.heartbeat_job(
            job_id,
            owner="worker",
            lease_token=token,
            lease_seconds=60,
            to_state="reviewing",
        )
        self.assertEqual(reviewing["job"]["state"], "reviewing")
        rejected = self.store.review_job(
            job_id,
            reviewer="codex-reviewer",
            state="rejected",
            exit_reason="drained during graceful stop",
        )
        self.assertEqual(rejected["job"]["state"], "rejected")

        self.store.set_dispatch_state("running", actor="after-drain-relaunch")
        stale_job = self.make_active_job("relaunch-fence", "Poincare/Other.lean")
        stale_token = self.claim_and_run(stale_job, owner="worker-two")
        self.store.set_dispatch_state("stopped", actor="second-stop")
        with self.assertRaisesRegex(TransitionError, "cannot restart while active Job"):
            self.store.set_dispatch_state("running", actor="unsafe-direct-relaunch")
        drained = self.store.heartbeat_job(
            stale_job,
            owner="worker-two",
            lease_token=stale_token,
            lease_seconds=60,
        )
        self.assertEqual(drained["job"]["state"], "running")

    def test_expired_scope_is_not_reused_while_old_execution_is_live(self) -> None:
        first = self.make_active_job("expired-scope-one", "Poincare/Shared.lean")
        second = self.make_active_job("expired-scope-two", "Poincare/Shared.lean")
        self.store.claim_job(job_id=first, owner="worker-one", lease_seconds=10)
        descriptor = self.hold_execution_fence(first)
        self.clock.advance(11)
        try:
            with self.assertRaisesRegex(LeaseError, "in-flight execution"):
                self.store.claim_job(
                    job_id=second, owner="worker-two", lease_seconds=60
                )
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)
        claimed = self.store.claim_job(
            job_id=second, owner="worker-two", lease_seconds=60
        )
        self.assertEqual(claimed["job"]["state"], "preparing")

    def test_execution_fence_blocks_claim_recovery_reviewing_and_terminal_release(self) -> None:
        job_id = self.make_active_job("execution-fence")
        token = self.claim_and_run(job_id, owner="worker")
        descriptor = self.hold_execution_fence(job_id)
        try:
            with self.assertRaisesRegex(LeaseError, "in-flight supervised"):
                self.store.claim_job(
                    job_id=job_id, owner="worker", lease_seconds=60
                )
            with self.assertRaisesRegex(LeaseError, "in-flight supervised"):
                self.store.heartbeat_job(
                    job_id,
                    owner="worker",
                    lease_token=token,
                    lease_seconds=60,
                    to_state="reviewing",
                )
            with self.assertRaisesRegex(LeaseError, "in-flight supervised"):
                self.store.finish_job(
                    job_id,
                    owner="worker",
                    lease_token=token,
                    state="interrupted",
                    exit_reason="must wait for reap",
                )
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)

        reviewing = self.store.heartbeat_job(
            job_id,
            owner="worker",
            lease_token=token,
            lease_seconds=60,
            to_state="reviewing",
        )
        self.assertEqual(reviewing["job"]["state"], "reviewing")
        descriptor = self.hold_execution_fence(job_id)
        try:
            with self.assertRaisesRegex(LeaseError, "in-flight supervised"):
                self.store.review_job(
                    job_id,
                    reviewer="codex-reviewer",
                    state="rejected",
                    exit_reason="must wait for execution close",
                )
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)

    def test_slow_review_validation_does_not_starve_unrelated_heartbeat(self) -> None:
        reviewing_job, _, _ = self.make_reviewing_job(
            "slow-review", worker="review-worker"
        )
        self.write_gate(reviewing_job)
        other_job = self.make_active_job(
            "heartbeat-during-review", "Poincare/Heartbeat.lean"
        )
        other_token = self.claim_and_run(other_job, owner="other-worker")
        entered = Event()
        release = Event()
        original = HarnessStore._validate_reviewed_commit

        def slow_validate(store: HarnessStore, *args, **kwargs):
            entered.set()
            if not release.wait(timeout=5):
                raise AssertionError("test did not release slow review validation")
            return original(store, *args, **kwargs)

        with patch.object(HarnessStore, "_validate_reviewed_commit", slow_validate):
            with ThreadPoolExecutor(max_workers=2) as executor:
                review_future = executor.submit(
                    self.store.review_job,
                    reviewing_job,
                    reviewer="codex-reviewer",
                    state="passed",
                    exit_reason="slow independent gate passed",
                    gate_status="passed",
                    gate_result="gate.json",
                    accepted_commit=self.accepted_commit,
                )
                self.assertTrue(entered.wait(timeout=2))
                heartbeat_started = time.monotonic()
                heartbeat = self.store.heartbeat_job(
                    other_job,
                    owner="other-worker",
                    lease_token=other_token,
                    lease_seconds=60,
                )
                heartbeat_elapsed = time.monotonic() - heartbeat_started
                self.assertEqual(heartbeat["job"]["state"], "running")
                self.assertLess(heartbeat_elapsed, 1.0)
                release.set()
                reviewed = review_future.result(timeout=5)
        self.assertEqual(reviewed["job"]["state"], "passed")

    def test_stop_interrupt_requires_stopped_dispatch_and_reaped_execution(self) -> None:
        job_id = self.make_active_job("stop-interrupt")
        self.claim_and_run(job_id, owner="worker")
        with self.assertRaisesRegex(TransitionError, "dispatch state"):
            self.store.interrupt_job_after_stop(
                job_id, actor="deploy-stop", exit_reason="operator stop"
            )

        self.store.set_dispatch_state("stopped", actor="deploy-stop")
        descriptor = self.hold_execution_fence(job_id)
        try:
            with self.assertRaisesRegex(LeaseError, "in-flight supervised"):
                self.store.interrupt_job_after_stop(
                    job_id, actor="deploy-stop", exit_reason="operator stop"
                )
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)

        interrupted = self.store.interrupt_job_after_stop(
            job_id, actor="deploy-stop", exit_reason="operator stop"
        )
        self.assertEqual(interrupted["job"]["state"], "interrupted")
        self.assertFalse(interrupted["runtime"]["lease_active"])
        self.assertTrue(
            all(not scope["active"] for scope in interrupted["runtime"]["scopes"])
        )

        self.store.set_dispatch_state("running", actor="queue-test-reopen")
        queued_job = self.make_active_job(
            "queued-stop-preserved", "Poincare/Queued.lean"
        )
        self.store.set_dispatch_state("stopped", actor="queue-test-stop")
        with self.assertRaisesRegex(TransitionError, "preserves queued Jobs"):
            self.store.interrupt_job_after_stop(
                queued_job,
                actor="deploy-stop",
                exit_reason="queued jobs are not consumed",
            )
        self.assertEqual(self.store.get_job(queued_job)["job"]["state"], "queued")

    def test_supersession_and_cross_task_replacement_wait_for_terminal_jobs(self) -> None:
        job_id = self.make_active_job("supersession-source")
        self.claim_and_run(job_id)
        with self.assertRaisesRegex(ConflictError, "nonterminal Job"):
            self.store.import_task(self.task_revision("supersession-source", 2))

        replacement = self.task_record("supersession-replacement")
        replacement["supersedes"] = "supersession-source"
        with self.assertRaisesRegex(ConflictError, "nonterminal Job"):
            self.store.import_task(replacement)

        self.store.set_dispatch_state("stopped", actor="deploy-stop")
        self.store.interrupt_job_after_stop(
            job_id, actor="deploy-stop", exit_reason="close old attempt"
        )
        imported = self.store.import_task(replacement)
        self.assertEqual(imported["task"]["status"], "proposed")
        self.assertEqual(
            self.store.get_task("supersession-source")["task"]["status"],
            "superseded",
        )
        superseded = self.store.transition_task(
            "supersession-source",
            "superseded",
            superseding_task_id="supersession-replacement",
        )
        self.assertEqual(superseded["task"]["status"], "superseded")

    def test_task_accept_and_block_wait_for_every_nonterminal_attempt(self) -> None:
        passed_job, _, _ = self.make_reviewing_job("accept-all-attempts")
        passed = self.pass_job(passed_job)
        second = self.job_record("accept-all-attempts", attempt=2)
        self.enqueue_job(second)
        second_token = self.claim_and_run(second["id"], owner="second-worker")
        with self.assertRaisesRegex(ConflictError, "nonterminal Job"):
            self.store.transition_task(
                "accept-all-attempts",
                "accepted",
                accepted_commit=self.accepted_commit,
                gate_job_id=passed_job,
            )
        self.store.finish_job(
            second["id"],
            owner="second-worker",
            lease_token=second_token,
            state="interrupted",
            exit_reason="close second attempt",
        )
        accepted = self.store.transition_task(
            "accept-all-attempts",
            "accepted",
            accepted_commit=passed["job"]["accepted_commit"],
            gate_job_id=passed_job,
        )
        self.assertEqual(accepted["task"]["status"], "accepted")

        blocked_job = self.make_active_job(
            "block-all-attempts", "Poincare/Blocked.lean"
        )
        blocked_token = self.claim_and_run(blocked_job, owner="blocked-worker")
        self.store.finish_job(
            blocked_job,
            owner="blocked-worker",
            lease_token=blocked_token,
            state="blocked",
            exit_reason="exact resisting Lean type",
        )
        blocked_second = self.job_record("block-all-attempts", attempt=2)
        self.enqueue_job(blocked_second)
        blocked_second_token = self.claim_and_run(
            blocked_second["id"], owner="blocked-worker-two"
        )
        with self.assertRaisesRegex(ConflictError, "nonterminal Job"):
            self.store.transition_task(
                "block-all-attempts",
                "blocked",
                blocked_reason="blocked with evidence",
                evidence_job_id=blocked_job,
            )
        self.store.finish_job(
            blocked_second["id"],
            owner="blocked-worker-two",
            lease_token=blocked_second_token,
            state="interrupted",
            exit_reason="close second blocked attempt",
        )
        blocked = self.store.transition_task(
            "block-all-attempts",
            "blocked",
            blocked_reason="blocked with evidence",
            evidence_job_id=blocked_job,
        )
        self.assertEqual(blocked["task"]["status"], "blocked")

    def test_concurrent_overlapping_claims_are_serialized(self) -> None:
        first = self.make_active_job("race-one", "Poincare/Race/**")
        second = self.make_active_job("race-two", "Poincare/Race/Exact.lean")
        barrier = Barrier(2)

        def claim(job_id: str, owner: str) -> str:
            barrier.wait()
            try:
                HarnessStore(self.state_dir, clock=self.clock).claim_job(
                    job_id=job_id, owner=owner, lease_seconds=60
                )
            except LeaseError:
                return "conflict"
            return "claimed"

        with ThreadPoolExecutor(max_workers=2) as executor:
            outcomes = list(
                executor.map(
                    lambda item: claim(*item),
                    [(first, "race-worker-one"), (second, "race-worker-two")],
                )
            )
        self.assertEqual(sorted(outcomes), ["claimed", "conflict"])

    def test_transaction_timestamps_are_sampled_after_write_lock(self) -> None:
        job_id = self.make_active_job("clock-task")
        observing_clock = LockAwareClock(self.store.database_path, self.clock)
        self.store._clock = observing_clock
        observing_clock.enabled = True
        claimed = self.store.claim_job(
            job_id=job_id, owner="worker", lease_seconds=60
        )
        self.assertTrue(observing_clock.samples_inside_transaction)
        self.assertTrue(all(observing_clock.samples_inside_transaction))
        observing_clock.samples_inside_transaction.clear()
        token = claimed["runtime"]["lease_token"]
        self.store.heartbeat_job(
            job_id,
            owner="worker",
            lease_token=token,
            lease_seconds=60,
            to_state="running",
        )
        self.assertTrue(observing_clock.samples_inside_transaction)
        self.assertTrue(all(observing_clock.samples_inside_transaction))
        observing_clock.samples_inside_transaction.clear()
        self.store.finish_job(
            job_id,
            owner="worker",
            lease_token=token,
            state="blocked",
            exit_reason="exact blocker",
        )
        self.assertTrue(observing_clock.samples_inside_transaction)
        self.assertTrue(all(observing_clock.samples_inside_transaction))

    def test_init_import_enqueue_and_claim_are_idempotent(self) -> None:
        self.assertEqual(self.store.initialize()["schema_version"], 5)
        self.assertEqual(self.store.initialize()["schema_version"], 5)
        task = self.task_record("repeat-task")
        self.store.import_task(task)
        self.store.import_task(copy.deepcopy(task))
        self.store.transition_task("repeat-task", "ready")
        self.store.transition_task("repeat-task", "ready")
        job = self.job_record("repeat-task")
        first_enqueue = self.enqueue_job(job)
        second_enqueue = self.store.enqueue_job(copy.deepcopy(job))
        self.assertEqual(first_enqueue["job"]["id"], second_enqueue["job"]["id"])
        first_claim = self.store.claim_job(
            job_id=job["id"], owner="same-worker", lease_seconds=60
        )
        second_claim = self.store.claim_job(
            job_id=job["id"], owner="same-worker", lease_seconds=60
        )
        self.assertEqual(
            first_claim["runtime"]["lease_token"],
            second_claim["runtime"]["lease_token"],
        )

    def test_structured_gate_commit_binding_and_acceptance(self) -> None:
        job_id, _, _ = self.make_reviewing_job("accept-task", worker="worker")
        self.pass_job(job_id)
        with self.assertRaises(TransitionError):
            self.store.transition_task(
                "accept-task",
                "accepted",
                accepted_commit=OTHER_COMMIT,
                gate_job_id=job_id,
            )
        accepted = self.store.transition_task(
            "accept-task",
            "accepted",
            accepted_commit=self.accepted_commit,
            gate_job_id=job_id,
        )
        self.assertEqual(accepted["task"]["accepted_commit"], self.accepted_commit)
        repeated = self.store.transition_task(
            "accept-task",
            "accepted",
            accepted_commit=self.accepted_commit,
            gate_job_id=job_id,
        )
        self.assertEqual(repeated["task"]["status"], "accepted")

    def test_review_rejects_incomplete_inconsistent_or_untyped_gate(self) -> None:
        task = self.task_record("strict-gate")
        task["acceptance"]["commands"].append(["lake", "env", "lean", "Check.lean"])
        job_id, _, _ = self.make_reviewing_job("strict-gate", task=task)
        valid = self.valid_gate_document(job_id)

        cases: list[dict] = []
        missing_field = copy.deepcopy(valid)
        missing_field.pop("declarations")
        cases.append(missing_field)
        missing_command = copy.deepcopy(valid)
        missing_command["commands"].pop()
        cases.append(missing_command)
        wrong_command = copy.deepcopy(valid)
        wrong_command["commands"][0]["argv"] = ["true"]
        cases.append(wrong_command)
        failed_command = copy.deepcopy(valid)
        failed_command["commands"][0].update(status="failed", exit_code=1)
        cases.append(failed_command)
        untyped_probe = copy.deepcopy(valid)
        source = "import Poincare\n#check ExampleTarget\n"
        untyped_probe["declarations"][0]["source"] = source
        untyped_probe["declarations"][0]["source_sha256"] = hashlib.sha256(
            source.encode()
        ).hexdigest()
        cases.append(untyped_probe)
        failed_probe = copy.deepcopy(valid)
        failed_probe["declarations"][0].update(status="failed", exit_code=1)
        cases.append(failed_probe)
        absolute_output = copy.deepcopy(valid)
        absolute_output["declarations"][0]["stdout_path"] = "/tmp/output"
        cases.append(absolute_output)
        wrong_commit = copy.deepcopy(valid)
        wrong_commit["accepted_commit"] = OTHER_COMMIT
        cases.append(wrong_commit)

        for document in cases:
            with self.subTest(document=document):
                self.write_gate(job_id, document)
                with self.assertRaises(TransitionError):
                    self.store.review_job(
                        job_id,
                        reviewer="codex-reviewer",
                        state="passed",
                        exit_reason="strict review",
                        gate_status="passed",
                        gate_result="gate.json",
                        accepted_commit=self.accepted_commit,
                    )
        self.write_gate(job_id, valid)
        passed = self.store.review_job(
            job_id,
            reviewer="codex-reviewer",
            state="passed",
            exit_reason="strict review",
            gate_status="passed",
            gate_result="gate.json",
            accepted_commit=self.accepted_commit,
        )
        self.assertEqual(passed["job"]["state"], "passed")

    def test_accepted_retry_revalidates_gate_and_declaration_outputs(self) -> None:
        job_id, _, _ = self.make_reviewing_job("retry-tamper")
        gate = self.write_gate(job_id)
        self.store.review_job(
            job_id,
            reviewer="codex-reviewer",
            state="passed",
            exit_reason="reviewed",
            gate_status="passed",
            gate_result="gate.json",
            accepted_commit=self.accepted_commit,
        )
        self.store.transition_task(
            "retry-tamper",
            "accepted",
            accepted_commit=self.accepted_commit,
            gate_job_id=job_id,
        )
        original = gate.read_bytes()
        gate.write_text('{"changed":true}\n', encoding="utf-8")
        with self.assertRaises(TransitionError):
            self.store.transition_task(
                "retry-tamper",
                "accepted",
                accepted_commit=self.accepted_commit,
                gate_job_id=job_id,
            )
        gate.write_bytes(original)
        probe_stdout = gate.parent / "declaration-probes" / "0.stdout"
        original_stdout = probe_stdout.read_bytes()
        probe_stdout.write_text("mutated\n", encoding="utf-8")
        with self.assertRaises(TransitionError):
            self.store.transition_task(
                "retry-tamper",
                "accepted",
                accepted_commit=self.accepted_commit,
                gate_job_id=job_id,
            )
        probe_stdout.write_bytes(original_stdout)
        worktree = Path(self.store.get_job(job_id)["job"]["workspace"]["worktree"])
        subprocess.run(
            [
                "git",
                "-C",
                str(worktree),
                "-c",
                "user.name=Harness Test",
                "-c",
                "user.email=harness@example.invalid",
                "commit",
                "--quiet",
                "--allow-empty",
                "-m",
                "drift",
            ],
            check=True,
        )
        with self.assertRaises(TransitionError):
            self.store.transition_task(
                "retry-tamper",
                "accepted",
                accepted_commit=self.accepted_commit,
                gate_job_id=job_id,
            )

    def test_review_binds_existing_commit_tree_and_repository(self) -> None:
        job_id, _, _ = self.make_reviewing_job("git-binding")
        wrong_tree = self.valid_gate_document(job_id)
        wrong_tree["accepted_tree"] = OTHER_COMMIT
        self.write_gate(job_id, wrong_tree)
        with self.assertRaises(TransitionError):
            self.store.review_job(
                job_id,
                reviewer="codex-reviewer",
                state="passed",
                exit_reason="wrong tree",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=self.accepted_commit,
            )

        nonexistent = self.valid_gate_document(job_id, accepted_commit=OTHER_COMMIT)
        nonexistent["accepted_tree"] = OTHER_COMMIT
        self.write_gate(job_id, nonexistent)
        with self.assertRaises(TransitionError):
            self.store.review_job(
                job_id,
                reviewer="codex-reviewer",
                state="passed",
                exit_reason="missing commit",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=OTHER_COMMIT,
            )

        worktree = Path(self.store.get_job(job_id)["job"]["workspace"]["worktree"])
        subprocess.run(
            [
                "git",
                "-C",
                str(self.integration_root),
                "worktree",
                "remove",
                "--force",
                str(worktree),
            ],
            check=True,
        )
        worktree.mkdir()
        subprocess.run(["git", "init", "--quiet", str(worktree)], check=True)
        (worktree / "FOREIGN").write_text("foreign\n", encoding="utf-8")
        subprocess.run(["git", "-C", str(worktree), "add", "FOREIGN"], check=True)
        subprocess.run(
            [
                "git",
                "-C",
                str(worktree),
                "-c",
                "user.name=Harness Test",
                "-c",
                "user.email=harness@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "foreign",
            ],
            check=True,
        )
        foreign_commit = subprocess.run(
            ["git", "-C", str(worktree), "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        foreign_tree = subprocess.run(
            ["git", "-C", str(worktree), "rev-parse", "HEAD^{tree}"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        foreign_gate = self.valid_gate_document(
            job_id, accepted_commit=foreign_commit
        )
        foreign_gate["accepted_tree"] = foreign_tree
        self.write_gate(job_id, foreign_gate)
        with self.assertRaises(TransitionError):
            self.store.review_job(
                job_id,
                reviewer="codex-reviewer",
                state="passed",
                exit_reason="foreign repository",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=foreign_commit,
            )

    def test_nonterminal_jobs_block_new_task_revisions(self) -> None:
        queued = self.make_active_job("stale-claim")
        with self.assertRaisesRegex(ConflictError, "nonterminal Job"):
            self.store.import_task(self.task_revision("stale-claim", 2))

        passed_job, _, _ = self.make_reviewing_job("stale-accept")
        self.pass_job(passed_job)
        self.store.import_task(self.task_revision("stale-accept", 2))
        with self.assertRaises(TransitionError):
            self.store.transition_task(
                "stale-accept",
                "accepted",
                revision=1,
                accepted_commit=self.accepted_commit,
                gate_job_id=passed_job,
            )

        reviewing_job, _, _ = self.make_reviewing_job("stale-review")
        self.write_gate(reviewing_job)
        with self.assertRaisesRegex(ConflictError, "nonterminal Job"):
            self.store.import_task(self.task_revision("stale-review", 2))

    def test_configured_roots_are_persisted_and_enforced(self) -> None:
        initialized = self.store.initialize()
        self.assertEqual(initialized["worktree_root"], str(self.worktree_root))
        self.assertEqual(initialized["integration_root"], str(self.integration_root))
        self.store.import_task(self.task_record("wrong-root"))
        self.store.transition_task("wrong-root", "ready")
        wrong = self.job_record("wrong-root")
        wrong["workspace"]["worktree"] = str(
            self.integration_root / "wrong-root-a01"
        )
        with self.assertRaises(ConflictError):
            self.store.enqueue_job(wrong)

        partial_state = self.base / "partial-integration" / "state"
        with self.assertRaises(HarnessError):
            HarnessStore(
                partial_state, worktree_root=self.worktree_root
            ).initialize()
        nested = self.integration_root / "nested-worktrees"
        nested.mkdir()
        with self.assertRaises(HarnessError):
            HarnessStore(
                self.base / "nested-state",
                worktree_root=nested,
                integration_root=self.integration_root,
            ).initialize()

    def test_unconfigured_runtime_enqueues_but_claim_fails_closed(self) -> None:
        state = self.base / "unconfigured-state"
        store = HarnessStore(state, clock=self.clock)
        self.assertIsNone(store.initialize()["worktree_root"])
        store.import_task(self.task_record("deferred-root"))
        store.transition_task("deferred-root", "ready")
        store.enqueue_job(
            job_record(
                "deferred-root", self.worktree_root, base_commit=self.base_commit
            )
        )
        with self.assertRaises(LeaseError):
            store.claim_job(
                job_id="deferred-root-a01", owner="worker", lease_seconds=60
            )

    def test_init_rejects_symlinked_parent_before_creating_state(self) -> None:
        target = self.base / "outside-target"
        target.mkdir()
        link = self.base / "linked-parent"
        link.symlink_to(target, target_is_directory=True)
        with self.assertRaises(HarnessError):
            HarnessStore(link / "nested" / "state", clock=self.clock).initialize()
        self.assertFalse((target / "nested").exists())

    def test_database_and_artifact_parent_symlinks_are_rejected(self) -> None:
        unsafe_state = self.base / "unsafe-state"
        unsafe_state.mkdir()
        target = self.base / "outside.sqlite3"
        target.write_bytes(b"do not modify")
        (unsafe_state / "harness.sqlite3").symlink_to(target)
        with self.assertRaises(HarnessError):
            HarnessStore(unsafe_state, clock=self.clock).initialize()
        self.assertEqual(target.read_bytes(), b"do not modify")

        job_id, _, _ = self.make_reviewing_job("artifact-symlink")
        self.write_gate(job_id)
        jobs = self.state_dir / "jobs"
        moved = self.state_dir / "jobs-real"
        jobs.rename(moved)
        jobs.symlink_to(moved, target_is_directory=True)
        with self.assertRaises(HarnessError):
            self.store.review_job(
                job_id,
                reviewer="codex-reviewer",
                state="passed",
                exit_reason="must fail closed",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=self.accepted_commit,
            )
        self.assertFalse((moved / job_id / "result.json").exists())

    def test_gate_path_swap_to_symlink_is_rejected(self) -> None:
        job_id, _, _ = self.make_reviewing_job("gate-path-swap")
        gate = self.write_gate(job_id)
        target = gate.with_name("gate-target.json")
        gate.rename(target)
        gate.symlink_to(target.name)
        with self.assertRaises(ConflictError):
            self.store.review_job(
                job_id,
                reviewer="codex-reviewer",
                state="passed",
                exit_reason="symlink swap",
                gate_status="passed",
                gate_result="gate.json",
                accepted_commit=self.accepted_commit,
            )
        self.assertFalse((gate.parent / "result.json").exists())

    def test_restart_preserves_schema_roots_database_and_artifacts(self) -> None:
        job_id = self.make_active_job("restart-task")
        claimed = self.store.claim_job(
            job_id=job_id, owner="persistent-worker", lease_seconds=120
        )
        restarted = HarnessStore(self.state_dir, clock=self.clock)
        self.assertEqual(restarted.schema_version(), 5)
        restored = restarted.get_job(job_id)
        self.assertEqual(restored["job"]["state"], "preparing")
        self.assertEqual(
            restored["runtime"]["lease_token"], claimed["runtime"]["lease_token"]
        )

    def test_schema_three_migrates_to_durable_dispatch_control(self) -> None:
        state = self.integration_root / "legacy-v3-state"
        state.mkdir()
        database = state / "harness.sqlite3"
        connection = sqlite3.connect(database)
        connection.execute(
            """
            CREATE TABLE schema_migrations (
                version INTEGER PRIMARY KEY,
                name TEXT NOT NULL,
                applied_at TEXT NOT NULL
            )
            """
        )
        for version, name, statements in MIGRATIONS:
            if version > 3:
                break
            for statement in statements:
                connection.execute(statement)
            connection.execute(
                "INSERT INTO schema_migrations(version, name, applied_at) VALUES (?, ?, ?)",
                (version, name, "2026-07-19T00:00:00.000000Z"),
            )
        connection.execute("PRAGMA user_version = 3")
        connection.commit()
        connection.close()

        migrated = HarnessStore(
            state,
            clock=self.clock,
            worktree_root=self.worktree_root,
            integration_root=self.integration_root,
        )
        self.assertEqual(migrated.initialize()["schema_version"], 5)
        self.assertEqual(migrated.get_dispatch_state()["desired_state"], "stopped")

    def test_secret_fields_and_cross_record_mismatches_are_rejected(self) -> None:
        declaration_syntax = self.task_record("bad-frozen-type")
        declaration_syntax["objective"]["frozen_lean_type"] = (
            "noncomputable def BadTarget : Prop"
        )
        with self.assertRaisesRegex(HarnessError, "Lean type expression"):
            self.store.import_task(declaration_syntax)
        self.store.import_task(self.task_record("safe-task"))
        self.store.transition_task("safe-task", "ready")
        secret_job = self.job_record("safe-task")
        secret_job["backend"]["sampling"]["token"] = "do-not-store-this"
        with self.assertRaises(HarnessError):
            self.store.enqueue_job(secret_job)
        mismatch = self.job_record("safe-task")
        mismatch["workspace"]["base_commit"] = OTHER_COMMIT
        with self.assertRaises(ConflictError):
            self.store.enqueue_job(mismatch)

    def test_job_contract_matches_the_pi_executor_sampling_boundary(self) -> None:
        self.store.import_task(self.task_record("pi-contract-task"))
        self.store.transition_task("pi-contract-task", "ready")

        invalid_jobs = []
        wrong_backend = self.job_record("pi-contract-task")
        wrong_backend["backend"]["kind"] = "codex"
        invalid_jobs.append(wrong_backend)

        extra_sampling = self.job_record("pi-contract-task")
        extra_sampling["backend"]["sampling"]["reasoning_effort"] = "high"
        invalid_jobs.append(extra_sampling)

        missing_sampling = self.job_record("pi-contract-task")
        del missing_sampling["backend"]["sampling"]["temperature"]
        invalid_jobs.append(missing_sampling)

        zero_tokens = self.job_record("pi-contract-task")
        zero_tokens["backend"]["sampling"]["max_tokens"] = 0
        invalid_jobs.append(zero_tokens)

        nonfinite_temperature = self.job_record("pi-contract-task")
        nonfinite_temperature["backend"]["sampling"]["temperature"] = float("inf")
        invalid_jobs.append(nonfinite_temperature)

        for record in invalid_jobs:
            with self.subTest(record=record["backend"]):
                with self.assertRaises(HarnessError):
                    self.store.enqueue_job(record)

    def test_concurrent_init_is_idempotent(self) -> None:
        integration = self.base / "concurrent-integration"
        worktrees = self.base / "concurrent-worktrees"
        integration.mkdir()
        worktrees.mkdir()
        state = integration / "state"
        with ThreadPoolExecutor(max_workers=4) as executor:
            results = list(
                executor.map(
                    lambda _: HarnessStore(
                        state,
                        clock=self.clock,
                        worktree_root=worktrees,
                        integration_root=integration,
                    ).initialize(),
                    range(4),
                )
            )
        self.assertEqual(
            [result["schema_version"] for result in results], [5, 5, 5, 5]
        )


if __name__ == "__main__":
    unittest.main()
