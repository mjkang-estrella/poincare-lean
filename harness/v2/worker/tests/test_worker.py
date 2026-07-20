from __future__ import annotations

import hashlib
import io
import json
import os
import socketserver
import subprocess
import tempfile
import threading
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from unittest.mock import patch

import harness.v2.worker.client as worker_client
from harness.v2.runtime.store import HarnessStore
from harness.v2.worker.artifacts import ArtifactError, ArtifactStore
from harness.v2.worker.binding import BindingError, assert_binding_live
from harness.v2.worker.cli import _parser
from harness.v2.worker.client import (
    LeanstralConfig,
    LeanstralError,
    check_health,
    run_once,
    snapshot_job,
)
from harness.v2.worker.secrets import secret_kind
from harness.v2.worker.snapshot import (
    SnapshotError,
    build_prompt_snapshot,
    compute_prompt_snapshot,
)


MODEL = "mistralai/Leanstral-1.5-119B-A6B"
REVISION = "81592da95d94ab0439bfce16df1d55b402e598b6"
SECRET = "test-secret-never-persist"


class _State:
    model = MODEL
    completion_status = 200
    post_count = 0
    requests: list[dict[str, Any]] = []
    get_requests: list[dict[str, Any]] = []
    redirect_url: str | None = None
    health_delay = 0.0
    completion_delay = 0.0
    health_padding = ""
    assistant = "Analysis\n\nProposed patch\nNONE"


class _Handler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return

    def _send(self, status: int, payload: dict[str, Any]) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            return

    def do_GET(self) -> None:
        _State.get_requests.append(
            {"path": self.path, "authorization": self.headers.get("Authorization")}
        )
        if self.path != "/v1/models":
            self._send(404, {"error": "not found"})
            return
        if _State.redirect_url is not None:
            self.send_response(302)
            self.send_header("Location", _State.redirect_url)
            self.end_headers()
            return
        if _State.health_delay:
            time.sleep(_State.health_delay)
        self._send(
            200,
            {
                "object": "list",
                "data": [{"id": _State.model}],
                "padding": _State.health_padding,
            },
        )

    def do_POST(self) -> None:
        _State.post_count += 1
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length)
        payload = json.loads(raw)
        _State.requests.append(
            {"path": self.path, "authorization": self.headers.get("Authorization"), "json": payload}
        )
        if _State.completion_delay:
            time.sleep(_State.completion_delay)
        if _State.completion_status != 200:
            self._send(_State.completion_status, {"error": "fake failure"})
            return
        self._send(
            200,
            {
                "id": "chatcmpl-test",
                "model": _State.model,
                "choices": [
                    {
                        "index": 0,
                        "message": {"role": "assistant", "content": _State.assistant},
                        "finish_reason": "stop",
                    }
                ],
            },
        )


class _Server(ThreadingHTTPServer):
    """HTTPServer without a reverse-DNS lookup during bind.

    Some developer machines have intentionally restricted local DNS.  The
    standard HTTPServer asks getfqdn() for a display name even though these
    tests only use a numeric loopback address.
    """

    def server_bind(self) -> None:
        socketserver.TCPServer.server_bind(self)
        host, port = self.server_address[:2]
        self.server_name = str(host)
        self.server_port = int(port)

    def handle_error(self, request: object, client_address: object) -> None:
        # Deadline tests intentionally close a socket while a delayed handler
        # is still preparing its response.
        return


class _RedirectState:
    hits: list[str] = []
    authorizations: list[str | None] = []


class _RedirectHandler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return

    def do_GET(self) -> None:
        _RedirectState.hits.append(self.path)
        _RedirectState.authorizations.append(self.headers.get("Authorization"))
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps({"data": [{"id": MODEL}]}).encode())


class FakeServer:
    def __enter__(self) -> "FakeServer":
        _State.model = MODEL
        _State.completion_status = 200
        _State.post_count = 0
        _State.requests = []
        _State.get_requests = []
        _State.redirect_url = None
        _State.health_delay = 0.0
        _State.completion_delay = 0.0
        _State.health_padding = ""
        _State.assistant = "Analysis\n\nProposed patch\nNONE"
        self.server = _Server(("127.0.0.1", 0), _Handler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        host, port = self.server.server_address
        self.url = f"http://{host}:{port}/v1"
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        self.server.shutdown()
        self.thread.join(timeout=2)
        self.server.server_close()


class RedirectTarget:
    def __enter__(self) -> "RedirectTarget":
        _RedirectState.hits = []
        _RedirectState.authorizations = []
        self.server = _Server(("127.0.0.1", 0), _RedirectHandler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        host, port = self.server.server_address
        self.url = f"http://{host}:{port}/capture"
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        self.server.shutdown()
        self.thread.join(timeout=2)
        self.server.server_close()


def _task(context_files: list[str], base_commit: str = "a" * 40) -> dict[str, Any]:
    return {
        "schema_version": "2.0",
        "id": "test-worker-task",
        "revision": 1,
        "status": "ready",
        "base_commit": base_commit,
        "objective": {
            "title": "Prove one bounded lemma",
            "statement": "Propose a proof for the frozen theorem.",
            "frozen_lean_type": "True",
            "deliverables": ["One proof proposal"],
        },
        "scope": {"allowed_paths": ["Poincare/Test.lean"], "forbidden_paths": ["Poincare.lean"]},
        "context": {"files": context_files, "symbols": ["example"], "depends_on": []},
        "acceptance": {
            "commands": [["lake", "env", "lean", "Poincare/Test.lean"]],
            "required_declarations": ["example"],
            "forbidden_added_tokens": ["sorry", "admit", "axiom", "native_decide"],
        },
        "stop_conditions": ["The frozen type changed"],
        "budget": {
            "max_attempts": 1,
            "wall_clock_minutes": 2,
            "max_output_tokens": 2048,
            "disk_mb": 128,
        },
    }


class WorkerTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        # Resolve the OS temporary directory first. On macOS /var is itself a
        # system symlink, while artifact paths under the repository/runtime are
        # expected to have no symlink components.
        self.root = Path(self.temp.name).resolve()
        (self.root / "Poincare").mkdir()
        (self.root / "Poincare" / "A.lean").write_text("theorem a : True := by trivial\n", encoding="utf-8")
        (self.root / "Poincare" / "B.lean").write_text("theorem b : True := by trivial\n", encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        subprocess.run(["git", "config", "user.name", "Harness Test"], cwd=self.root, check=True)
        subprocess.run(
            ["git", "config", "user.email", "harness@example.invalid"],
            cwd=self.root,
            check=True,
        )
        self.base_commit = self._commit_sources("initial context")
        self.task_path = self.root / "task.json"
        self.task_path.write_text(
            json.dumps(
                _task(["Poincare/B.lean", "Poincare/A.lean"], self.base_commit)
            ),
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temp.cleanup()

    def _commit_sources(self, message: str) -> str:
        subprocess.run(["git", "add", "Poincare"], cwd=self.root, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", message], cwd=self.root, check=True
        )
        return subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=self.root,
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()

    def write_task(self, context_files: list[str]) -> dict[str, Any]:
        task = _task(context_files, self.base_commit)
        self.task_path.write_text(json.dumps(task), encoding="utf-8")
        return task

    def config(self, url: str) -> LeanstralConfig:
        return LeanstralConfig(
            base_url=url,
            model=MODEL,
            api_key=SECRET,
            model_revision=REVISION,
            timeout_seconds=3,
            max_tokens=4096,
            reasoning_effort="high",
            temperature=1.0,
        )

    def make_live_job(
        self,
        endpoint: str,
        *,
        prompt_sha256: str | None = None,
        context_sha256: str | None = None,
        to_running: bool = True,
    ) -> dict[str, Any]:
        control = self.root / "control"
        worktrees = self.root / "worktrees"
        job_id = "test-worker-task-a01"
        worktree = worktrees / job_id
        control.mkdir()
        worktree.mkdir(parents=True)
        (worktree / "Poincare").mkdir()
        (worktree / "Poincare/A.lean").write_text(
            "theorem a : True := by trivial\n", encoding="utf-8"
        )
        (worktree / "Poincare/B.lean").write_text(
            "theorem b : True := by trivial\n", encoding="utf-8"
        )
        (worktree / "Poincare/Test.lean").write_text(
            "theorem test : True := by trivial\n", encoding="utf-8"
        )
        branch = "codex/test-worker-task/a01"
        subprocess.run(["git", "init", "-q", "-b", branch], cwd=worktree, check=True)
        subprocess.run(
            ["git", "config", "user.name", "Harness Test"], cwd=worktree, check=True
        )
        subprocess.run(
            ["git", "config", "user.email", "harness@example.invalid"],
            cwd=worktree,
            check=True,
        )
        subprocess.run(["git", "add", "Poincare"], cwd=worktree, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", "Job baseline"], cwd=worktree, check=True
        )
        base = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=worktree,
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        task = _task(["Poincare/B.lean", "Poincare/A.lean"], base)
        task["status"] = "proposed"
        state_dir = control / "harness/v2/state"
        store = HarnessStore(
            state_dir,
            worktree_root=worktrees,
            integration_root=control,
        )
        store.initialize()
        store.set_dispatch_state("running", actor="worker-test-setup")
        store.import_task(task)
        ready = store.transition_task(task["id"], "ready")["task"]
        snapshot = compute_prompt_snapshot(task=ready, repo_root=worktree)
        job = {
            "schema_version": "2.0",
            "id": job_id,
            "task_id": task["id"],
            "task_revision": 1,
            "attempt": 1,
            "state": "queued",
            "backend": {
                "kind": "leanstral",
                "model": MODEL,
                "model_revision": REVISION,
                "endpoint": endpoint,
                "sampling": {
                    "max_tokens": 2048,
                    "temperature": 1.0,
                },
            },
            "workspace": {
                "base_commit": base,
                "worktree": str(worktree),
                "branch": branch,
                "lease_owner": "not-active-until-claim",
                "lease_expires_at": "2099-01-01T00:00:00Z",
            },
            "artifacts": {
                "directory": f"harness/v2/state/jobs/{job_id}",
                "prompt_sha256": prompt_sha256 or snapshot.prompt_sha256,
                "context_sha256": context_sha256 or snapshot.context_sha256,
            },
            "gate": {"status": "not_run"},
        }
        store.enqueue_job(job)
        claimed = store.claim_job(job_id=job_id, owner="codex-test", lease_seconds=600)
        token = claimed["runtime"]["lease_token"]
        if to_running:
            store.heartbeat_job(
                job_id,
                owner="codex-test",
                lease_token=token,
                lease_seconds=600,
                to_state="running",
            )
        return {
            "store": store,
            "state_dir": state_dir,
            "job_id": job_id,
            "owner": "codex-test",
            "token": token,
            "worktree": worktree,
            "artifact_dir": state_dir / "jobs" / job_id,
        }

    @staticmethod
    def run_live(config: LeanstralConfig, live: dict[str, Any]):
        return run_once(
            config=config,
            job_id=live["job_id"],
            state_dir=live["state_dir"],
            lease_owner=live["owner"],
            lease_token=live["token"],
        )

    def test_snapshot_is_deterministic_and_context_is_sorted(self) -> None:
        first = build_prompt_snapshot(
            task_path=self.task_path, repo_root=self.root, artifact_dir=self.root / "artifacts-1"
        )
        second = build_prompt_snapshot(
            task_path=self.task_path, repo_root=self.root, artifact_dir=self.root / "artifacts-2"
        )
        self.assertEqual(first.prompt_sha256, second.prompt_sha256)
        self.assertEqual(first.context_sha256, second.context_sha256)
        self.assertEqual([entry.path for entry in first.context_entries], ["Poincare/A.lean", "Poincare/B.lean"])
        self.assertLess(first.prompt.index("Poincare/A.lean"), first.prompt.index("Poincare/B.lean"))

    def test_snapshot_ignores_ambient_git_repository_redirection(self) -> None:
        with patch.dict(
            os.environ,
            {
                "GIT_DIR": str(self.root / "nonexistent-git-dir"),
                "GIT_WORK_TREE": str(self.root / "nonexistent-worktree"),
                "GIT_CONFIG_PARAMETERS": "'core.hooksPath=/tmp/hostile'",
            },
        ):
            snapshot = build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "sanitized-git-environment",
            )
        self.assertEqual(snapshot.task["base_commit"], self.base_commit)

    def test_snapshot_rejects_path_escape_and_overwrite(self) -> None:
        self.task_path.write_text(
            json.dumps(_task(["../outside.lean"], self.base_commit)), encoding="utf-8"
        )
        with self.assertRaises(SnapshotError):
            build_prompt_snapshot(
                task_path=self.task_path, repo_root=self.root, artifact_dir=self.root / "bad-artifacts"
            )

        self.write_task(["Poincare/A.lean"])
        artifact_dir = self.root / "once"
        build_prompt_snapshot(task_path=self.task_path, repo_root=self.root, artifact_dir=artifact_dir)
        with self.assertRaises(ArtifactError):
            build_prompt_snapshot(task_path=self.task_path, repo_root=self.root, artifact_dir=artifact_dir)

    def test_bound_snapshot_rejects_immutable_hash_disagreement_before_writes(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(
                server.url,
                prompt_sha256="0" * 64,
                context_sha256="1" * 64,
            )
            with self.assertRaisesRegex(BindingError, "hashes differ"):
                snapshot_job(
                    config=self.config(server.url),
                    job_id=live["job_id"],
                    state_dir=live["state_dir"],
                    lease_owner=live["owner"],
                    lease_token=live["token"],
                )
        self.assertFalse((live["artifact_dir"] / "prompt.md").exists())
        self.assertFalse((live["artifact_dir"] / "context-manifest.json").exists())

    def test_artifact_symlink_roots_parents_and_targets_are_rejected(self) -> None:
        real_root = self.root / "real-artifacts"
        real_root.mkdir()
        linked_root = self.root / "linked-artifacts"
        linked_root.symlink_to(real_root, target_is_directory=True)
        with self.assertRaisesRegex(ArtifactError, "root or parent"):
            build_prompt_snapshot(
                task_path=self.task_path, repo_root=self.root, artifact_dir=linked_root
            )

        linked_parent = self.root / "linked-parent"
        linked_parent.symlink_to(real_root, target_is_directory=True)
        with self.assertRaisesRegex(ArtifactError, "root or parent"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=linked_parent / "nested-job",
            )

        artifact_dir = self.root / "safe-artifacts"
        artifact_dir.mkdir()
        external = self.root / "external"
        external.mkdir()
        (artifact_dir / "responses").symlink_to(external, target_is_directory=True)
        from harness.v2.worker.artifacts import ArtifactStore

        with self.assertRaisesRegex(ArtifactError, "parent must not be a symbolic link"):
            ArtifactStore(artifact_dir).write_once("responses/result.json", b"{}\n")

        target_dir = self.root / "target-link-artifacts"
        target_dir.mkdir()
        outside = self.root / "outside.txt"
        outside.write_text("outside", encoding="utf-8")
        (target_dir / "prompt.md").symlink_to(outside)
        with self.assertRaisesRegex(ArtifactError, "unsafe file|target must not be"):
            build_prompt_snapshot(
                task_path=self.task_path, repo_root=self.root, artifact_dir=target_dir
            )

    def test_full_task_validation_rejects_unknown_fields(self) -> None:
        invalid = _task(["Poincare/A.lean"], self.base_commit)
        invalid["unexpected"] = True
        self.task_path.write_text(json.dumps(invalid), encoding="utf-8")
        with self.assertRaisesRegex(SnapshotError, "unknown fields"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "invalid-task",
            )

    def test_snapshot_requires_exact_base_commit(self) -> None:
        task = _task(["Poincare/A.lean"], "b" * 40)
        self.task_path.write_text(json.dumps(task), encoding="utf-8")
        with self.assertRaisesRegex(SnapshotError, "does not match Task base_commit"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "wrong-base",
            )

    def test_snapshot_rejects_dirty_context_and_allowed_scope(self) -> None:
        (self.root / "Poincare" / "A.lean").write_text(
            "theorem a : True := by simp\n", encoding="utf-8"
        )
        self.write_task(["Poincare/A.lean"])
        with self.assertRaisesRegex(SnapshotError, "allowed scope is dirty"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "dirty-context",
            )

        subprocess.run(
            ["git", "restore", "Poincare/A.lean"], cwd=self.root, check=True
        )
        (self.root / "Poincare" / "Test.lean").write_text(
            "theorem test : True := by trivial\n", encoding="utf-8"
        )
        with self.assertRaisesRegex(SnapshotError, "allowed scope is dirty"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "dirty-allowed",
            )

    def test_snapshot_allows_unrelated_dirty_file(self) -> None:
        (self.root / "notes.txt").write_text("unrelated\n", encoding="utf-8")
        result = build_prompt_snapshot(
            task_path=self.task_path,
            repo_root=self.root,
            artifact_dir=self.root / "unrelated-dirty",
        )
        self.assertEqual(result.task["base_commit"], self.base_commit)

    def test_snapshot_rejects_untracked_context(self) -> None:
        (self.root / "Poincare" / "Generated.lean").write_text(
            "theorem generated : True := by trivial\n", encoding="utf-8"
        )
        self.write_task(["Poincare/Generated.lean"])
        with self.assertRaisesRegex(SnapshotError, "must be tracked"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "untracked-context",
            )

    def test_snapshot_caps_per_file_and_aggregate_context(self) -> None:
        with patch("harness.v2.worker.snapshot.MAX_CONTEXT_FILE_BYTES", 16):
            with self.assertRaisesRegex(SnapshotError, "context file .* exceeds"):
                build_prompt_snapshot(
                    task_path=self.task_path,
                    repo_root=self.root,
                    artifact_dir=self.root / "large-context-file",
                )
        with (
            patch("harness.v2.worker.snapshot.MAX_CONTEXT_FILE_BYTES", 1024),
            patch("harness.v2.worker.snapshot.MAX_CONTEXT_TOTAL_BYTES", 40),
        ):
            with self.assertRaisesRegex(SnapshotError, "aggregate"):
                build_prompt_snapshot(
                    task_path=self.task_path,
                    repo_root=self.root,
                    artifact_dir=self.root / "large-context-total",
                )

    def test_secret_like_context_is_never_snapshotted(self) -> None:
        marker = "sk-abcdefghijklmnopqrstuvwx"
        (self.root / "Poincare" / "A.lean").write_text(
            f'def credential := "{marker}"\n', encoding="utf-8"
        )
        self.base_commit = self._commit_sources("add secret-shaped fixture")
        self.write_task(["Poincare/A.lean"])
        artifact_dir = self.root / "secret-context"
        with self.assertRaisesRegex(SnapshotError, "secret-bearing"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=artifact_dir,
            )
        self.assertFalse(artifact_dir.exists())
        self.assertNotIn(marker, self.task_path.read_text(encoding="utf-8"))

    def test_task_disk_budget_covers_preexisting_and_new_artifacts(self) -> None:
        task = self.write_task(["Poincare/A.lean"])
        task["budget"]["disk_mb"] = 1
        self.task_path.write_text(json.dumps(task), encoding="utf-8")
        artifact_dir = self.root / "disk-budget"
        artifact_dir.mkdir()
        (artifact_dir / "preexisting.bin").write_bytes(b"x" * (1024 * 1024))
        with self.assertRaisesRegex(ArtifactError, "disk budget exceeded"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=artifact_dir,
            )

    def test_health_fails_closed_on_model_mismatch(self) -> None:
        with FakeServer() as server:
            _State.model = "wrong-model"
            with self.assertRaisesRegex(LeanstralError, "identity mismatch"):
                check_health(self.config(server.url))
            self.assertEqual(_State.post_count, 0)

    def test_health_response_body_is_capped(self) -> None:
        with FakeServer() as server:
            _State.health_padding = "x" * 512
            with patch("harness.v2.worker.client.MAX_HEALTH_RESPONSE_BYTES", 128):
                with self.assertRaisesRegex(LeanstralError, "body cap"):
                    check_health(self.config(server.url))

    def test_redirect_is_not_followed_or_forwarded_authorization(self) -> None:
        with RedirectTarget() as target, FakeServer() as server:
            _State.redirect_url = target.url
            with self.assertRaisesRegex(LeanstralError, "HTTP 302"):
                check_health(self.config(server.url))
        self.assertEqual(_RedirectState.hits, [])
        self.assertEqual(_RedirectState.authorizations, [])
        self.assertEqual(_State.get_requests[0]["authorization"], f"Bearer {SECRET}")

    def test_run_preserves_artifacts_hashes_and_redacts_authorization(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            before = live["store"].get_job(live["job_id"])["job"]["state"]
            result = self.run_live(self.config(server.url), live)
            after = live["store"].get_job(live["job_id"])["job"]["state"]

        artifact_dir = live["artifact_dir"]
        response_bytes = (artifact_dir / result.response_artifact).read_bytes()
        self.assertEqual(hashlib.sha256(response_bytes).hexdigest(), result.response_sha256)
        self.assertEqual((artifact_dir / result.assistant_artifact).read_text(), "Analysis\n\nProposed patch\nNONE")
        events = (artifact_dir / "events.jsonl").read_text(encoding="utf-8")
        self.assertNotIn(SECRET, events)
        self.assertIn("<redacted>", events)
        session_bytes = (artifact_dir / "fallback-session.json").read_bytes()
        session_sha256 = hashlib.sha256(session_bytes).hexdigest()
        self.assertIn(session_sha256, events)
        evidence_bytes = (artifact_dir / result.evidence_artifact).read_bytes()
        self.assertEqual(hashlib.sha256(evidence_bytes).hexdigest(), result.evidence_sha256)
        evidence = json.loads(evidence_bytes)
        self.assertEqual(evidence["fallback_session_sha256"], session_sha256)
        self.assertEqual(evidence["outcome"], "completed")
        artifact_hashes = {item["path"]: item["sha256"] for item in evidence["artifacts"]}
        self.assertIn(result.response_artifact, artifact_hashes)
        self.assertEqual(
            artifact_hashes["events.jsonl"],
            hashlib.sha256((artifact_dir / "events.jsonl").read_bytes()).hexdigest(),
        )
        self.assertEqual(_State.requests[0]["authorization"], f"Bearer {SECRET}")
        sent = _State.requests[0]["json"]
        self.assertEqual(sent["model"], MODEL)
        self.assertEqual(sent["max_tokens"], 2048)
        self.assertNotIn("reasoning_effort", sent)
        self.assertEqual(sent["temperature"], 1.0)
        self.assertEqual((before, after), ("running", "running"))

    def test_completion_http_error_is_preserved(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            _State.completion_status = 503
            with self.assertRaisesRegex(LeanstralError, "HTTP 503"):
                self.run_live(self.config(server.url), live)
        artifact_dir = live["artifact_dir"]
        responses = list((artifact_dir / "responses").glob("completion-*.json"))
        self.assertEqual(len(responses), 1)
        self.assertIn("fake failure", responses[0].read_text(encoding="utf-8"))
        self.assertIn('"status_code":503', (artifact_dir / "events.jsonl").read_text())

    def test_completion_response_body_is_capped(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            _State.assistant = "x" * 1024
            with patch("harness.v2.worker.client.MAX_COMPLETION_RESPONSE_BYTES", 256):
                with self.assertRaisesRegex(LeanstralError, "body cap"):
                    self.run_live(self.config(server.url), live)
        artifact_dir = live["artifact_dir"]
        completion_responses = list(
            (artifact_dir / "responses").glob("completion-*.json")
        )
        self.assertEqual(completion_responses, [])

    def test_health_and_completion_share_one_deadline(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            _State.health_delay = 0.12
            # Leave enough of the common budget for the strengthened live
            # repository/snapshot rechecks to finish, then prove that the
            # completion request receives only the remainder rather than a
            # fresh per-request timeout.
            _State.completion_delay = 3.00
            config = replace(self.config(server.url), timeout_seconds=2.00)
            started = time.monotonic()
            with self.assertRaisesRegex(LeanstralError, "request to /chat/completions failed"):
                self.run_live(config, live)
            elapsed = time.monotonic() - started
        self.assertLess(elapsed, 2.25)

    def test_binding_requires_running_state_exact_lease_and_backend(self) -> None:
        with FakeServer() as server:
            preparing = self.make_live_job(server.url, to_running=False)
            with self.assertRaisesRegex(BindingError, "running Job"):
                snapshot_job(
                    config=self.config(server.url),
                    job_id=preparing["job_id"],
                    state_dir=preparing["state_dir"],
                    lease_owner=preparing["owner"],
                    lease_token=preparing["token"],
                )

    def test_binding_rejects_wrong_owner_token_and_pinned_revision(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            common = {
                "config": self.config(server.url),
                "job_id": live["job_id"],
                "state_dir": live["state_dir"],
            }
            with self.assertRaisesRegex(BindingError, "owner or fencing token"):
                snapshot_job(
                    **common,
                    lease_owner="wrong-owner",
                    lease_token=live["token"],
                )
            with self.assertRaisesRegex(BindingError, "owner or fencing token"):
                snapshot_job(
                    **common,
                    lease_owner=live["owner"],
                    lease_token=live["token"] + 1,
                )
            with self.assertRaisesRegex(BindingError, "revision differs"):
                snapshot_job(
                    **{
                        **common,
                        "config": replace(common["config"], model_revision="wrong-revision"),
                    },
                    lease_owner=live["owner"],
                    lease_token=live["token"],
                )
            with self.assertRaisesRegex(BindingError, "MODEL_REVISION"):
                snapshot_job(
                    **{
                        **common,
                        "config": replace(common["config"], model_revision=None),
                    },
                    lease_owner=live["owner"],
                    lease_token=live["token"],
                )

    def test_binding_wraps_malformed_sqlite_as_a_closed_failure(self) -> None:
        bad_state = self.root / "malformed-state"
        bad_state.mkdir()
        (bad_state / "harness.sqlite3").write_bytes(b"not a sqlite database")
        with FakeServer() as server:
            with self.assertRaisesRegex(BindingError, "cannot load live Harness Job"):
                snapshot_job(
                    config=self.config(server.url),
                    job_id="missing-a01",
                    state_dir=bad_state,
                    lease_owner="codex-test",
                    lease_token=1,
                )

    def test_binding_rejects_worktree_branch_head_and_dirty_scope(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            worktree = live["worktree"]
            config = self.config(server.url)
            arguments = {
                "config": config,
                "job_id": live["job_id"],
                "state_dir": live["state_dir"],
                "lease_owner": live["owner"],
                "lease_token": live["token"],
            }
            subprocess.run(["git", "switch", "-q", "-c", "wrong-branch"], cwd=worktree, check=True)
            with self.assertRaisesRegex(BindingError, "branch, or HEAD"):
                snapshot_job(**arguments)
            subprocess.run(
                ["git", "switch", "-q", "codex/test-worker-task/a01"],
                cwd=worktree,
                check=True,
            )
            (worktree / "notes.txt").write_text("new head\n", encoding="utf-8")
            subprocess.run(["git", "add", "notes.txt"], cwd=worktree, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "wrong head"], cwd=worktree, check=True)
            with self.assertRaisesRegex(BindingError, "branch, or HEAD"):
                snapshot_job(**arguments)
            subprocess.run(["git", "reset", "--soft", "HEAD^"], cwd=worktree, check=True)
            subprocess.run(["git", "restore", "--staged", "notes.txt"], cwd=worktree, check=True)
            (worktree / "notes.txt").unlink()
            (worktree / "Poincare/Test.lean").write_text(
                "theorem test : True := by simp\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(SnapshotError, "allowed scope is dirty"):
                snapshot_job(**arguments)

    def test_liveness_rechecks_registered_immutable_snapshots(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            binding, _ = snapshot_job(
                config=self.config(server.url),
                job_id=live["job_id"],
                state_dir=live["state_dir"],
                lease_owner=live["owner"],
                lease_token=live["token"],
            )
            job_path = live["artifact_dir"] / "job.json"
            job_path.write_bytes(job_path.read_bytes() + b" ")
            with self.assertRaisesRegex(BindingError, "registered job_snapshot"):
                assert_binding_live(binding)

    def test_cli_run_has_no_arbitrary_task_repo_or_artifact_path(self) -> None:
        valid = [
            "run",
            "--job-id",
            "task-a01",
            "--state-dir",
            "/safe/state",
            "--lease-owner",
            "codex",
            "--lease-token",
            "1",
        ]
        parsed = _parser().parse_args(valid)
        self.assertFalse(hasattr(parsed, "task"))
        self.assertFalse(hasattr(parsed, "repo_root"))
        self.assertFalse(hasattr(parsed, "artifact_dir"))
        with patch("sys.stderr", new=io.StringIO()):
            with self.assertRaises(SystemExit):
                _parser().parse_args([*valid, "--artifact-dir", "/tmp/arbitrary"])

    def test_context_symlinks_are_rejected_even_when_tracked(self) -> None:
        link = self.root / "Poincare" / "Link.lean"
        link.symlink_to("A.lean")
        self.base_commit = self._commit_sources("track context symlink")
        self.write_task(["Poincare/Link.lean"])
        with self.assertRaisesRegex(SnapshotError, "symbolic link"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "symlink-context",
            )

    def test_secret_detection_covers_aws_password_urls_and_exact_keys(self) -> None:
        self.assertEqual(secret_kind(b"AKIAABCDEFGHIJKLMNOP"), "AWS access key")
        self.assertEqual(
            secret_kind(b'password="correct-horse-battery"'),
            "password or API credential assignment",
        )
        self.assertEqual(
            secret_kind(b"https://worker:supersecret@example.invalid/v1"),
            "credential URL",
        )
        self.assertEqual(
            secret_kind(b"prefix exact-value suffix", exact_values=("exact-value",)),
            "configured API credential",
        )

        marker = "private-runtime-value"
        task = self.write_task(["Poincare/A.lean"])
        task["objective"]["statement"] = f"Prove the target using {marker}"
        self.task_path.write_text(json.dumps(task), encoding="utf-8")
        with self.assertRaisesRegex(SnapshotError, "rendered fallback prompt"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "exact-secret-task",
                exact_secrets=(marker,),
            )

        (self.root / "Poincare/A.lean").write_text(
            f'def runtimeValue := "{marker}"\n', encoding="utf-8"
        )
        self.base_commit = self._commit_sources("exact secret fixture")
        self.write_task(["Poincare/A.lean"])
        with self.assertRaisesRegex(SnapshotError, "secret-bearing"):
            build_prompt_snapshot(
                task_path=self.task_path,
                repo_root=self.root,
                artifact_dir=self.root / "exact-secret-context",
                exact_secrets=(marker,),
            )

    def test_secret_response_retains_only_hash_metadata(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            _State.assistant = f"unsafe response contains {SECRET}"
            with self.assertRaisesRegex(LeanstralError, "secret-bearing"):
                self.run_live(self.config(server.url), live)
        artifact_dir = live["artifact_dir"]
        self.assertEqual(list((artifact_dir / "responses").glob("completion-*.json")), [])
        self.assertFalse((artifact_dir / "assistant").exists())
        events = (artifact_dir / "events.jsonl").read_text(encoding="utf-8")
        self.assertIn("unsafe_response_rejected", events)
        self.assertIn(hashlib.sha256(json.dumps({
            "id": "chatcmpl-test",
            "model": MODEL,
            "choices": [{
                "index": 0,
                "message": {"role": "assistant", "content": _State.assistant},
                "finish_reason": "stop",
            }],
        }).encode("utf-8")).hexdigest(), events)
        self.assertNotIn(SECRET, events)
        for path in artifact_dir.rglob("*"):
            if path.is_file():
                self.assertNotIn(SECRET.encode("utf-8"), path.read_bytes(), path)

    def test_artifact_budget_recount_and_write_are_serialized_per_job(self) -> None:
        root = self.root / "concurrent-artifacts"
        stores = [ArtifactStore(root, max_bytes=1000), ArtifactStore(root, max_bytes=1000)]
        barrier = threading.Barrier(2)

        def attempt(index: int) -> bool:
            barrier.wait(timeout=2)
            try:
                stores[index].write_once(f"payload-{index}.bin", b"x" * 700)
                return True
            except ArtifactError:
                return False

        with ThreadPoolExecutor(max_workers=2) as executor:
            results = list(executor.map(attempt, range(2)))
        self.assertEqual(sum(results), 1)
        self.assertLessEqual(
            sum(path.stat().st_size for path in root.iterdir() if path.is_file()),
            1000,
        )

    def test_run_deadline_starts_before_live_binding_and_snapshot(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            original = worker_client.bind_live_job

            def delayed_binding(**kwargs: Any):
                time.sleep(0.08)
                return original(**kwargs)

            with patch(
                "harness.v2.worker.client.bind_live_job",
                side_effect=delayed_binding,
            ):
                with self.assertRaisesRegex(BindingError, "deadline exhausted"):
                    self.run_live(
                        replace(self.config(server.url), timeout_seconds=0.04),
                        live,
                    )
            self.assertEqual(_State.post_count, 0)
            self.assertEqual(_State.get_requests, [])

    def test_fallback_run_is_one_fresh_session_per_job(self) -> None:
        with FakeServer() as server:
            live = self.make_live_job(server.url)
            self.run_live(self.config(server.url), live)
            self.assertEqual(_State.post_count, 1)
            with self.assertRaisesRegex(ArtifactError, "already exists"):
                self.run_live(self.config(server.url), live)
            self.assertEqual(_State.post_count, 1)

    def test_environment_requires_service_identity(self) -> None:
        with self.assertRaisesRegex(LeanstralError, "LEANSTRAL_BASE_URL"):
            LeanstralConfig.from_env({})
        with self.assertRaisesRegex(LeanstralError, "credentials"):
            LeanstralConfig.from_env(
                {"LEANSTRAL_BASE_URL": "http://user:pass@example/v1", "LEANSTRAL_MODEL": MODEL}
            )
        with FakeServer() as server:
            unsafe = self.config(server.url)
            unsafe = LeanstralConfig(
                base_url=unsafe.base_url,
                model=unsafe.model,
                api_key="line-one\nline-two",
            )
            with self.assertRaisesRegex(LeanstralError, "line breaks"):
                check_health(unsafe)


if __name__ == "__main__":
    unittest.main()
