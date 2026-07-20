from __future__ import annotations

import hashlib
import json
import os
import shutil
import socketserver
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
import unittest
import uuid
from contextlib import redirect_stdout
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from io import StringIO
from pathlib import Path
from typing import Any
from unittest.mock import patch

from harness.v2.pi import PI_VERSION, TOOL_NAMES
from harness.v2.pi.broker import BrokerError, execute_tool
from harness.v2.pi.cli import main as cli_main
from harness.v2.pi.engine import PiEngineError, SYSTEM_PROMPT, run_job
from harness.v2.pi.integrity import TRUSTED_CODE_PATHS, attest_trusted_code
from harness.v2.pi.security import (
    BWRAP_PROFILE_VERSION,
    SecurityError,
    bubblewrap_lean_argv,
    canonical_package_overrides,
    lake_cache_tree_digest,
    lean_acceptance_argv,
    path_is_allowed,
    run_limited,
    validate_patch,
)
from harness.v2.pi.snapshot import build_snapshot
from harness.v2.runtime.store import ConflictError, HarnessStore


MODEL = "mistralai/Leanstral-1.5-119B-A6B"
REVISION = "fake-pinned-revision"
ENDPOINT = "http://127.0.0.1:9999/v1"


class _SSEState:
    requests: list[dict[str, Any]] = []


class _SSEHandler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return

    def _json(self, status: int, payload: dict[str, Any]) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:
        if self.path == "/v1/models":
            self._json(200, {"object": "list", "data": [{"id": MODEL}]})
        else:
            self._json(404, {"error": "not found"})

    def do_POST(self) -> None:
        length = int(self.headers.get("Content-Length", "0"))
        payload = json.loads(self.rfile.read(length))
        _SSEState.requests.append(
            {
                "path": self.path,
                "authorization": self.headers.get("Authorization"),
                "payload": payload,
            }
        )
        if self.path != "/v1/chat/completions":
            self._json(404, {"error": "not found"})
            return
        base = {
            "id": "chatcmpl-pi-extension-test",
            "object": "chat.completion.chunk",
            "created": 1,
            "model": MODEL,
        }
        chunks = [
            {**base, "choices": [{"index": 0, "delta": {"role": "assistant"}, "finish_reason": None}]},
            {**base, "choices": [{"index": 0, "delta": {"content": "OK"}, "finish_reason": None}]},
            {**base, "choices": [{"index": 0, "delta": {}, "finish_reason": "stop"}]},
            {
                **base,
                "choices": [],
                "usage": {"prompt_tokens": 20, "completion_tokens": 1, "total_tokens": 21},
            },
        ]
        body = b"".join(
            b"data: " + json.dumps(chunk).encode("utf-8") + b"\n\n"
            for chunk in chunks
        ) + b"data: [DONE]\n\n"
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


class _NoDnsServer(ThreadingHTTPServer):
    def server_bind(self) -> None:
        socketserver.TCPServer.server_bind(self)
        host, port = self.server_address[:2]
        self.server_name = str(host)
        self.server_port = int(port)


def _run(*argv: str, cwd: Path) -> str:
    result = subprocess.run(
        argv,
        cwd=cwd,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
        text=True,
    )
    return result.stdout.strip()


def _trusted_manifest_without_git_check(control_root: Path) -> dict[str, Any]:
    files: list[dict[str, Any]] = []
    aggregate = hashlib.sha256()
    aggregate.update(b"poincare-harness-v2-trusted-code-v1\0")
    for relative in TRUSTED_CODE_PATHS:
        data = (control_root / relative).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        files.append(
            {"path": relative, "sha256": digest, "size_bytes": len(data)}
        )
        aggregate.update(relative.encode("utf-8"))
        aggregate.update(b"\0")
        aggregate.update(digest.encode("ascii"))
        aggregate.update(b"\0")
        aggregate.update(str(len(data)).encode("ascii"))
        aggregate.update(b"\n")
    return {
        "schema_version": "poincare.pi-trusted-code.v1",
        "git_commit": "0" * 40,
        "aggregate_sha256": aggregate.hexdigest(),
        "files": files,
    }


def _task(base_commit: str, task_id: str) -> dict[str, Any]:
    return {
        "schema_version": "2.0",
        "id": task_id,
        "revision": 1,
        "status": "proposed",
        "base_commit": base_commit,
        "objective": {
            "title": "Close one bounded scalar lemma",
            "statement": "Prove the frozen local test theorem.",
            "frozen_lean_type": "True",
            "deliverables": ["One checked declaration"],
        },
        "scope": {
            "allowed_paths": ["Poincare/Test.lean"],
            "forbidden_paths": ["Poincare.lean"],
        },
        "context": {
            "files": ["Poincare/Test.lean"],
            "symbols": ["testValue"],
            "depends_on": [],
        },
        "acceptance": {
            "commands": [
                ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "Poincare/Test.lean"]
            ],
            "required_declarations": ["testValue"],
            "forbidden_added_tokens": ["sorry", "admit", "axiom", "native_decide"],
        },
        "stop_conditions": ["The frozen type changed"],
        "budget": {
            "max_attempts": 1,
            "wall_clock_minutes": 2,
            "max_output_tokens": 128,
            "disk_mb": 64,
        },
    }


FAKE_PI = r'''#!/usr/bin/env python3
import json
import os
import pathlib
import subprocess
import sys
import time

if sys.argv[1:] == ["-v"]:
    print("0.80.10")
    raise SystemExit(0)

args = sys.argv[1:]
required = {
    "--mode": "json",
    "--provider": "harness-leanstral",
    "--model": "mistralai/Leanstral-1.5-119B-A6B",
}
for flag, expected in required.items():
    if flag not in args or args[args.index(flag) + 1] != expected:
        print(f"bad {flag}", file=sys.stderr)
        raise SystemExit(21)
for flag in (
    "--no-builtin-tools", "--no-extensions", "--no-skills",
    "--no-prompt-templates", "--no-themes", "--no-context-files",
    "--no-approve", "--offline",
):
    if flag not in args:
        print(f"missing {flag}", file=sys.stderr)
        raise SystemExit(22)
if "--print" in args:
    raise SystemExit(23)
expected_tools = "read_context,search_symbol,apply_patch_scoped,lean_check,git_diff,report_blocked"
if args[args.index("--tools") + 1] != expected_tools:
    raise SystemExit(24)

session_id = args[args.index("--session-id") + 1]
session_dir = pathlib.Path(args[args.index("--session-dir") + 1])
job_id = args[args.index("--name") + 1]
system_prompt = pathlib.Path(args[args.index("--system-prompt") + 1])
if not system_prompt.is_file() or not system_prompt.read_text().startswith("You are the bounded"):
    raise SystemExit(25)
if os.environ.get("PI_SKIP_VERSION_CHECK") != "1":
    raise SystemExit(26)
if os.environ.get("LEANSTRAL_API_KEY"):
    raise SystemExit(27)
prompt = sys.stdin.buffer.read()
if not prompt.startswith(b"# Poincare Harness v2 Pi Job"):
    raise SystemExit(28)

session_dir.mkdir(parents=True, exist_ok=True)
(session_dir / f"{session_id}.jsonl").write_text(
    json.dumps({"type": "session", "version": 3, "id": session_id, "cwd": os.getcwd()}) + "\n"
)
(session_dir / "fake-invocation.json").write_text(json.dumps(args))
capability = json.loads(pathlib.Path(os.environ["HARNESS_PI_CAPABILITY"]).read_text())
artifact_dir = pathlib.Path(capability["artifact_dir"])
(artifact_dir / "fake-pi.pid").write_text(str(os.getpid()))

if "trusted-mutation" in job_id:
    (artifact_dir / "trusted-mutation-ready").write_text("ready\n")
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        if (artifact_dir / "trusted-mutation-done").exists():
            break
        time.sleep(0.02)
    else:
        raise SystemExit(29)

if "diff-allowed" in job_id:
    pathlib.Path("Poincare/Test.lean").write_text(
        "theorem testValue : True := by exact True.intro\n"
    )
elif "diff-staged" in job_id:
    pathlib.Path("Poincare/Test.lean").write_text(
        "theorem testValue : True := by exact True.intro\n"
    )
    subprocess.run(["git", "add", "Poincare/Test.lean"], check=True)
elif "diff-untracked" in job_id:
    pathlib.Path("Poincare/New.lean").write_text("theorem newValue : True := by trivial\n")
elif "diff-delete" in job_id:
    pathlib.Path("Poincare/Test.lean").unlink()
elif "diff-rename" in job_id:
    pathlib.Path("Poincare/Test.lean").rename("Poincare/Renamed.lean")
elif "diff-mode" in job_id:
    pathlib.Path("Poincare/Test.lean").chmod(0o755)
elif "diff-binary" in job_id:
    pathlib.Path("Poincare/Test.lean").write_bytes(b"\x00\x01\x02")
elif "diff-outside" in job_id:
    pathlib.Path("Poincare/Outside.lean").write_text(
        "theorem outsideValue : True := by exact True.intro\n"
    )
elif "diff-forbidden" in job_id:
    pathlib.Path("Poincare/Test.lean").write_text(
        "theorem testValue : True := by sorry\n"
    )

if "stale-running" in job_id or "artifact-failure" in job_id:
    print(json.dumps({"type": "session", "version": 3, "id": session_id, "cwd": os.getcwd()}), flush=True)
    (artifact_dir / "fake-pi-started").write_text("ready\n")
    time.sleep(30)
    raise SystemExit(99)

blocked = "blocked" in job_id
tool_name = "report_blocked" if blocked else "git_diff"
events = [
    {"type": "session", "version": 3, "id": session_id, "cwd": os.getcwd()},
    {"type": "agent_start"},
    {"type": "tool_execution_start", "toolCallId": "call-1", "toolName": tool_name, "args": {}},
    {"type": "tool_execution_end", "toolCallId": "call-1", "toolName": tool_name, "result": {}, "isError": False},
]
if blocked:
    report = {
        "schema_version": "poincare.pi-blocked.v1",
        "reported_at": "2026-07-19T00:00:00Z",
        "summary": "The exact local shape resists the bounded routes.",
        "exact_lean_type_or_error": "application type mismatch at testValue",
        "attempted_routes": ["simp", "exact True.intro"],
        "strongest_partial_result": "Context and target were verified without changing files.",
    }
    pathlib.Path(capability["artifact_dir"], "pi-blocked-report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    stop_reason = "toolUse"
    text = ""
else:
    stop_reason = "stop"
    text = "Result\nNo patch was required."
message = {
    "role": "assistant",
    "content": [{"type": "text", "text": text}],
    "provider": "harness-leanstral",
    "model": "mistralai/Leanstral-1.5-119B-A6B",
    "stopReason": stop_reason,
    "usage": {"input": 10, "output": 7, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 17},
}
events.extend([
    {"type": "message_start", "message": message},
    {"type": "message_end", "message": message},
    {"type": "agent_end", "messages": [message], "willRetry": False},
    {"type": "agent_settled"},
])
for event in events:
    print(json.dumps(event), flush=True)
'''


class PiFixture(unittest.TestCase):
    task_id = "pi-engine-task"
    sampling: dict[str, Any] = {"max_tokens": 128, "temperature": 0}

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.control = self.root / "control"
        self.job_id = f"{self.task_id}-a01"
        self.worktrees_root = self.root / "worktrees"
        self.worktree = self.worktrees_root / self.job_id
        self.control.mkdir()
        self.worktrees_root.mkdir()
        self.source_root = Path(__file__).resolve().parents[4]
        for relative in TRUSTED_CODE_PATHS:
            source = self.source_root / relative
            destination = self.control / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        source_extension = self.source_root / "harness/v2/pi/extension.ts"
        (self.control / "harness/v2/pi/extension.ts").write_bytes(
            source_extension.read_bytes()
        )
        (self.control / ".gitignore").write_text(
            "/harness/v2/state/\n", encoding="utf-8"
        )
        _run("git", "init", "-b", "control-test", cwd=self.control)
        _run("git", "config", "user.name", "Harness Test", cwd=self.control)
        _run(
            "git", "config", "user.email", "harness@example.invalid", cwd=self.control
        )
        _run("git", "add", ".", cwd=self.control)
        _run("git", "commit", "-m", "trusted control fixture", cwd=self.control)

        (self.worktree / "Poincare").mkdir(parents=True)
        (self.worktree / "Poincare/Test.lean").write_text(
            "theorem testValue : True := by trivial\n", encoding="utf-8"
        )
        (self.worktree / "Poincare/Outside.lean").write_text(
            "theorem outsideValue : True := by trivial\n", encoding="utf-8"
        )
        _run("git", "init", "-b", f"codex/{self.task_id}/a01", cwd=self.worktree)
        _run("git", "config", "user.name", "Harness Test", cwd=self.worktree)
        _run("git", "config", "user.email", "harness@example.invalid", cwd=self.worktree)
        _run("git", "add", "Poincare/Test.lean", "Poincare/Outside.lean", cwd=self.worktree)
        _run("git", "commit", "-m", "fixture", cwd=self.worktree)
        self.base_commit = _run("git", "rev-parse", "HEAD", cwd=self.worktree)

        self.task = _task(self.base_commit, self.task_id)
        self.state_dir = self.control / "harness/v2/state"
        self.store = HarnessStore(
            self.state_dir,
            worktree_root=self.worktrees_root,
            integration_root=self.control,
        )
        self.store.initialize()
        self.store.set_dispatch_state("running", actor="pi-test-setup")
        self.store.import_task(self.task)
        ready = self.store.transition_task(self.task_id, "ready")["task"]
        snapshot = build_snapshot(ready, self.worktree)
        job = {
            "schema_version": "2.0",
            "id": self.job_id,
            "task_id": self.task_id,
            "task_revision": 1,
            "attempt": 1,
            "state": "queued",
            "backend": {
                "kind": "leanstral",
                "model": MODEL,
                "model_revision": REVISION,
                "endpoint": ENDPOINT,
                "sampling": dict(self.sampling),
            },
            "workspace": {
                "base_commit": self.base_commit,
                "worktree": str(self.worktree),
                "branch": f"codex/{self.task_id}/a01",
                "lease_owner": "not-active-until-claim",
                "lease_expires_at": "2099-01-01T00:00:00Z",
            },
            "artifacts": {
                "directory": f"harness/v2/state/jobs/{self.job_id}",
                "prompt_sha256": snapshot.prompt_sha256,
                "context_sha256": snapshot.context_sha256,
            },
            "gate": {"status": "not_run"},
        }
        self.store.enqueue_job(job)
        claimed = self.store.claim_job(
            job_id=self.job_id, owner="codex-test", lease_seconds=600
        )
        self.lease_token = claimed["runtime"]["lease_token"]
        self.store.heartbeat_job(
            self.job_id,
            owner="codex-test",
            lease_token=self.lease_token,
            lease_seconds=600,
            to_state="running",
        )
        self.fake_pi = self.root / "pi"
        self.fake_pi.write_text(FAKE_PI, encoding="utf-8")
        self.fake_pi.chmod(0o755)

        self.tools_dir = self.root / "sandbox-tools"
        self.tools_dir.mkdir()
        (self.tools_dir / "bin").mkdir()
        self.fake_bwrap = self.tools_dir / "bwrap"
        self.fake_lake = self.tools_dir / "bin/lake"
        self.fake_lean = self.tools_dir / "bin/lean"
        for executable in (self.fake_bwrap, self.fake_lake, self.fake_lean):
            executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            executable.chmod(0o755)
        self.fake_runtime_lib = self.tools_dir / "libfake.so"
        self.fake_runtime_lib.write_bytes(b"fake runtime library")
        self.lake_cache_root = self.root / "lake-cache"
        (self.lake_cache_root / self.base_commit).mkdir(parents=True)

    def sandbox_auditor(self, *args: Any, **kwargs: Any) -> dict[str, Any]:
        control = Path(kwargs.get("control_root", self.control)).resolve()
        worktree = Path(kwargs.get("worktree", self.worktree)).resolve()
        forbidden = [Path(item).resolve() for item in kwargs.get("forbidden_paths", [])]
        digest = hashlib.sha256(self.fake_bwrap.read_bytes()).hexdigest()
        lake_digest = hashlib.sha256(self.fake_lake.read_bytes()).hexdigest()
        lean_digest = hashlib.sha256(self.fake_lean.read_bytes()).hexdigest()
        cache = self.lake_cache_root / self.base_commit
        return {
            "kind": "bubblewrap",
            "profile_version": BWRAP_PROFILE_VERSION,
            "bwrap_path": str(self.fake_bwrap),
            "bwrap_sha256": digest,
            "toolchain": {
                "source": str(self.tools_dir),
                "destination": "/opt/lean",
                "lake_host": str(self.fake_lake),
                "lake_sandbox": "/opt/lean/bin/lake",
                "lake_sha256": lake_digest,
                "lean_host": str(self.fake_lean),
                "lean_sandbox": "/opt/lean/bin/lean",
                "lean_sha256": lean_digest,
            },
            "runtime_mounts": [
                {
                    "source": str(self.fake_runtime_lib),
                    "destination": "/usr/lib/libfake.so",
                    "sha256": hashlib.sha256(
                        self.fake_runtime_lib.read_bytes()
                    ).hexdigest(),
                }
            ],
            "runtime_symlinks": [],
            "path_env": "/opt/lean/bin",
            "worktree": str(worktree),
            "worktree_entries": [{"name": "Poincare", "kind": "directory"}],
            "lake_cache": {
                "source": str(cache),
                "manifest_sha256": "0" * 64,
                "cache_tree_sha256": "0" * 64,
                "package_overrides_sha256": "0" * 64,
                "metadata_fingerprint": "0" * 64,
            },
            "forbidden_host_paths": sorted(
                {str(control), str(worktree), *(str(item) for item in forbidden)}
            ),
        }

    def import_revision_two(self) -> None:
        revision = json.loads(json.dumps(self.task))
        revision["revision"] = 2
        revision["supersedes"] = self.task_id
        revision["status"] = "proposed"
        self.store.import_task(revision)

    def execute(self, **overrides: Any):
        with patch.dict(
            os.environ,
            {
                "LEANSTRAL_BASE_URL": ENDPOINT,
                "LEANSTRAL_MODEL": MODEL,
                "LEANSTRAL_MODEL_REVISION": REVISION,
                "LEANSTRAL_API_KEY": "must-not-enter-pi",
                "HARNESS_PI_LAKE_CACHE_ROOT": str(self.lake_cache_root),
            },
            clear=False,
        ):
            arguments: dict[str, Any] = {
                "job_id": self.job_id,
                "lease_owner": "codex-test",
                "lease_token": self.lease_token,
                "state_dir": self.state_dir,
                "control_root": self.control,
                "pi_bin": str(self.fake_pi),
                "health_checker": lambda _config, *, artifact_dir: None,
                "integrity_attestor": lambda root: attest_trusted_code(
                    root, check_loaded_origins=False
                ),
                "sandbox_auditor": self.sandbox_auditor,
            }
            arguments.update(overrides)
            return run_job(
                **arguments,
            )


@unittest.skip(
    "legacy direct fake-Pi engine fixture cannot cross the production sealed-install/bwrap/RPC boundary"
)
class PiEngineTest(PiFixture):
    def test_fresh_fake_pi_session_captures_events_and_preserves_authority(self) -> None:
        result = self.execute()
        self.assertTrue(result.success)
        self.assertEqual(result.exit_reason, "agent_settled with final stopReason=stop")
        self.assertEqual(result.output_tokens, 7)
        artifact_dir = self.state_dir / "jobs" / self.job_id
        launch = json.loads((artifact_dir / "pi-launch.json").read_text())
        self.assertEqual(launch["active_tools"], list(TOOL_NAMES))
        self.assertEqual(launch["pi_version"], PI_VERSION)
        model_index = launch["argv"].index("--model")
        self.assertEqual(launch["argv"][model_index + 1], MODEL)
        self.assertNotIn("--print", launch["argv"])
        self.assertTrue((artifact_dir / "pi-events.jsonl").is_file())
        self.assertTrue((artifact_dir / "messages.jsonl").is_file())
        self.assertTrue((artifact_dir / "tool-events.jsonl").is_file())
        self.assertTrue((artifact_dir / "system-prompt.md").is_file())
        self.assertEqual(self.store.get_job(self.job_id)["job"]["state"], "running")

        evidence_path = artifact_dir / "evidence-manifest.json"
        evidence = json.loads(evidence_path.read_text())
        self.assertTrue(evidence["complete"])
        entries = {item["logical_name"]: item for item in evidence["files"]}
        self.assertEqual(
            set(entries),
            {
                "pi_events",
                "messages",
                "tool_events",
                "stderr",
                "broker_events",
                "session",
                "worker_patch",
                "final_report",
                "pi_launch",
                "pi_capability",
                "prompt",
                "context_manifest",
                "system_prompt",
                "trusted_code_manifest",
                "sandbox_manifest",
                "final_diff_audit",
                "health_check",
                "session_closed",
            },
        )
        for entry in entries.values():
            self.assertNotIn("missing", entry)
            evidence_file = artifact_dir / entry["path"]
            data = evidence_file.read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), entry["sha256"])
            self.assertEqual(len(data), entry["size_bytes"])
            self.assertEqual(evidence_file.stat().st_mode & 0o222, 0)
        result_record = json.loads((artifact_dir / "pi-run-result.json").read_text())
        self.assertEqual(result_record["evidence"], evidence["files"])
        self.assertEqual(
            result_record["evidence_manifest_sha256"],
            hashlib.sha256(evidence_path.read_bytes()).hexdigest(),
        )
        self.assertEqual(evidence_path.stat().st_mode & 0o222, 0)
        self.assertEqual((artifact_dir / "pi-run-result.json").stat().st_mode & 0o222, 0)

        capability_path = artifact_dir / "pi-capability.json"
        capability_hash = hashlib.sha256(capability_path.read_bytes()).hexdigest()
        with self.assertRaisesRegex(BrokerError, "closed|sealed|read-only|complete"):
            execute_tool(
                capability_path=capability_path,
                capability_sha256=capability_hash,
                tool_name="read_context",
                call_id="read-after-completion",
                value={"path": "Poincare/Test.lean"},
            )

class PiStaleBeforeLaunchTest(PiFixture):
    task_id = "pi-stale-before"

    def test_new_task_revision_fails_before_pi_launch(self) -> None:
        with self.assertRaisesRegex(ConflictError, "nonterminal Job|still has"):
            self.import_revision_two()
        self.assertFalse((self.state_dir / "jobs" / self.job_id / "fake-pi.pid").exists())
        self.assertEqual(self.store.get_task(self.task_id)["task"]["revision"], 1)


@unittest.skip(
    "legacy direct fake-Pi engine fixture cannot cross the production sealed-install/bwrap/RPC boundary"
)
class PiStaleDuringRunTest(PiFixture):
    task_id = "pi-stale-running"

    def test_new_task_revision_terminates_live_pi_process(self) -> None:
        started = self.state_dir / "jobs" / self.job_id / "fake-pi-started"
        errors: list[BaseException] = []

        def supersede() -> None:
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline and not started.exists():
                time.sleep(0.02)
            if not started.exists():
                errors.append(AssertionError("fake Pi did not start"))
                return
            try:
                self.import_revision_two()
            except BaseException as exc:  # recorded in the test thread
                errors.append(exc)

        thread = threading.Thread(target=supersede, daemon=True)
        thread.start()
        before = time.monotonic()
        result = self.execute()
        elapsed = time.monotonic() - before
        thread.join(timeout=5)
        self.assertFalse(errors, errors)
        self.assertFalse(thread.is_alive())
        self.assertFalse(result.success)
        self.assertLess(elapsed, 10)
        self.assertRegex(result.exit_reason, "revision|stale|lease|capability")


@unittest.skip(
    "legacy extension-spawned broker fixture was removed by the engine-owned RPC boundary"
)
class PiTrustedCodeMutationTest(PiFixture):
    task_id = "pi-trusted-mutation"

    def test_broker_rejects_trusted_code_mutation_during_live_job(self) -> None:
        artifact_dir = self.state_dir / "jobs" / self.job_id
        ready = artifact_dir / "trusted-mutation-ready"
        done = artifact_dir / "trusted-mutation-done"
        observed: list[str] = []

        def probe_broker() -> None:
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline and not ready.exists():
                time.sleep(0.02)
            if not ready.exists():
                observed.append("fake Pi did not reach trusted-mutation probe")
                return
            capability_path = artifact_dir / "pi-capability.json"
            capability_hash = hashlib.sha256(capability_path.read_bytes()).hexdigest()
            trusted = self.control / TRUSTED_CODE_PATHS[0]
            original = trusted.read_bytes()
            trusted.write_bytes(original + b"\n# malicious drift\n")
            try:
                try:
                    execute_tool(
                        capability_path=capability_path,
                        capability_sha256=capability_hash,
                        tool_name="git_diff",
                        call_id="trusted-mutation-probe",
                        value={},
                    )
                except BrokerError as exc:
                    observed.append(str(exc))
                else:
                    observed.append("broker incorrectly accepted trusted-code drift")
            finally:
                trusted.write_bytes(original)
                done.write_text("done\n", encoding="utf-8")

        thread = threading.Thread(target=probe_broker, daemon=True)
        thread.start()
        result = self.execute()
        thread.join(timeout=5)
        self.assertTrue(result.success, result.exit_reason)
        self.assertFalse(thread.is_alive())
        self.assertEqual(len(observed), 1, observed)
        self.assertRegex(observed[0], "trusted|changed|dirty")


@unittest.skip(
    "legacy direct fake-Pi engine fixture cannot cross the production sealed-install/bwrap/RPC boundary"
)
class PiBlockedEngineTest(PiFixture):
    task_id = "pi-blocked-task"

    def test_terminating_blocked_tool_is_canonical_non_success(self) -> None:
        result = self.execute()
        self.assertFalse(result.success)
        self.assertEqual(result.exit_reason, "worker_reported_blocked")
        artifact_dir = self.state_dir / "jobs" / self.job_id
        record = json.loads((artifact_dir / "pi-run-result.json").read_text())
        self.assertTrue(record["blocked_reported"])
        self.assertEqual(record["final_stop_reason"], "toolUse")
        self.assertIn("Exact Lean type", (artifact_dir / "final-report.md").read_text())


@unittest.skip(
    "legacy direct fake-Pi engine fixture cannot cross the production sealed-install/bwrap/RPC boundary"
)
class PiArtifactFailureTest(PiFixture):
    task_id = "pi-artifact-failure"

    def test_artifact_write_failure_kills_and_reaps_pi(self) -> None:
        artifact_dir = self.state_dir / "jobs" / self.job_id
        with patch(
            "harness.v2.pi.engine._append_line",
            side_effect=OSError("injected artifact write failure"),
        ):
            with self.assertRaisesRegex(OSError, "injected artifact write failure"):
                self.execute()
        pid_path = artifact_dir / "fake-pi.pid"
        self.assertTrue(pid_path.is_file())
        pid = int(pid_path.read_text())
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                break
            time.sleep(0.02)
        else:
            self.fail(f"Pi process {pid} survived artifact-write failure")


@unittest.skip(
    "legacy direct fake-Pi engine fixture cannot cross the production sealed-install/bwrap/RPC boundary"
)
class PiFinalDiffAuditTest(unittest.TestCase):
    def _fixture(self, task_id: str) -> PiFixture:
        fixture = PiFixture()
        fixture.task_id = task_id
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        return fixture

    @staticmethod
    def _head_diff(worktree: Path) -> bytes:
        return subprocess.run(
            [
                "git",
                "-c",
                "core.fsmonitor=false",
                "diff",
                "--binary",
                "--no-ext-diff",
                "--no-textconv",
                "--no-color",
                "HEAD",
                "--",
            ],
            cwd=worktree,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=True,
        ).stdout

    def test_allowed_tracked_edit_records_exact_full_head_diff(self) -> None:
        fixture = self._fixture("pi-diff-allowed")
        result = fixture.execute()
        self.assertTrue(result.success, result.exit_reason)
        artifact_dir = fixture.state_dir / "jobs" / fixture.job_id
        expected = self._head_diff(fixture.worktree)
        self.assertTrue(expected)
        self.assertEqual((artifact_dir / "worker.patch").read_bytes(), expected)
        audit = json.loads((artifact_dir / "final-diff-audit.json").read_text())
        self.assertTrue(audit["valid"])
        self.assertEqual(audit["changed_paths"], ["Poincare/Test.lean"])

    def test_unsafe_final_worktree_states_are_evidence_but_never_success(self) -> None:
        cases = (
            "staged",
            "untracked",
            "delete",
            "rename",
            "mode",
            "binary",
            "outside",
            "forbidden",
        )
        for case in cases:
            with self.subTest(case=case):
                fixture = self._fixture(f"pi-diff-{case}")
                result = fixture.execute()
                self.assertFalse(result.success)
                self.assertRegex(result.exit_reason, "diff|worktree|scope|forbidden|audit")
                artifact_dir = fixture.state_dir / "jobs" / fixture.job_id
                expected = self._head_diff(fixture.worktree)
                self.assertEqual((artifact_dir / "worker.patch").read_bytes(), expected)
                audit = json.loads(
                    (artifact_dir / "final-diff-audit.json").read_text()
                )
                self.assertFalse(audit["valid"])


class PiSecurityTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / "Poincare").mkdir()
        (self.root / "Poincare/Test.lean").write_text("theorem x : True := by trivial\n")

    def test_scope_patch_and_lean_allowlists_fail_closed(self) -> None:
        self.assertTrue(
            path_is_allowed(
                "Poincare/Test.lean", ["Poincare/**"], ["Poincare/Secret/**"]
            )
        )
        self.assertFalse(
            path_is_allowed(
                "Poincare/Secret/X.lean", ["Poincare/**"], ["Poincare/Secret/**"]
            )
        )
        valid = textwrap.dedent(
            """\
            diff --git a/Poincare/Test.lean b/Poincare/Test.lean
            --- a/Poincare/Test.lean
            +++ b/Poincare/Test.lean
            @@ -1 +1 @@
            -theorem x : True := by trivial
            +theorem x : True := by exact True.intro
            """
        )
        self.assertEqual(
            validate_patch(
                valid,
                root=self.root,
                allowed=["Poincare/Test.lean"],
                forbidden=[],
                forbidden_tokens=["sorry", "admit"],
            ),
            ("Poincare/Test.lean",),
        )
        with self.assertRaises(SecurityError):
            validate_patch(
                valid.replace("exact True.intro", "sorry"),
                root=self.root,
                allowed=["Poincare/Test.lean"],
                forbidden=[],
                forbidden_tokens=["sorry"],
            )
        with self.assertRaises(SecurityError):
            validate_patch(
                valid.replace("Poincare/Test.lean", "../escape.lean"),
                root=self.root,
                allowed=["Poincare/**"],
                forbidden=[],
                forbidden_tokens=["sorry"],
            )
        self.assertEqual(
            lean_acceptance_argv(
                ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "Poincare/Test.lean"]
            ),
            ("lake", "env", "lean", "Poincare/Test.lean"),
        )
        with self.assertRaises(SecurityError):
            lean_acceptance_argv(["bash", "-lc", "lake build"])

    def test_snapshot_cli_writes_deterministic_hashes_once(self) -> None:
        _run("git", "init", cwd=self.root)
        task = _task("a" * 40, "snapshot-task")
        task_path = self.root / "task.json"
        task_path.write_text(json.dumps(task), encoding="utf-8")
        output = self.root / "snapshot"
        stdout = StringIO()
        with redirect_stdout(stdout):
            status = cli_main(
                [
                    "snapshot",
                    "--task-json",
                    str(task_path),
                    "--worktree",
                    str(self.root),
                    "--output-dir",
                    str(output),
                ]
            )
        self.assertEqual(status, 0)
        rendered = json.loads(stdout.getvalue())
        self.assertEqual(rendered["context_files"], 1)
        self.assertTrue((output / "prompt.md").is_file())
        self.assertTrue((output / "context-manifest.json").is_file())

    def test_tool_cli_rejects_unsupervised_broker_before_capability_or_stdin(self) -> None:
        stdout = StringIO()
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop("HARNESS_PI_BROKER_PROCESS", None)
            os.environ.pop("HARNESS_PI_PARENT_PID", None)
            with redirect_stdout(stdout):
                status = cli_main(
                    [
                        "tool",
                        "--capability",
                        "/definitely/not/read.json",
                        "--capability-sha256",
                        "0" * 64,
                        "--tool",
                        "git_diff",
                        "--call-id",
                        "unsupervised-probe",
                    ]
                )
        self.assertEqual(status, 2)
        reply = json.loads(stdout.getvalue())
        self.assertFalse(reply["ok"])
        self.assertRegex(reply["error"], "supervised broker marker")

    def test_run_limited_times_out_after_child_closes_both_output_pipes(self) -> None:
        pid_path = self.root / "limited.pid"
        script = self.root / "close-pipes.py"
        script.write_text(
            textwrap.dedent(
                f"""\
                import os
                import pathlib
                import time
                pathlib.Path({str(pid_path)!r}).write_text(str(os.getpid()))
                os.close(1)
                os.close(2)
                time.sleep(30)
                """
            ),
            encoding="utf-8",
        )
        before = time.monotonic()
        result = run_limited(
            [os.sys.executable, str(script)],
            cwd=self.root,
            env={"PATH": os.environ.get("PATH", "/usr/bin:/bin")},
            timeout_seconds=0.25,
            output_limit_bytes=1024,
        )
        self.assertTrue(result.timed_out)
        self.assertLess(time.monotonic() - before, 3)
        pid = int(pid_path.read_text())
        with self.assertRaises(ProcessLookupError):
            os.kill(pid, 0)

    @unittest.skipUnless(
        sys.platform == "linux" and Path("/proc/self/stat").is_file(),
        "requires Linux prctl parent-death supervision and /proc",
    )
    def test_engine_parent_death_kills_pi_and_guarded_broker_descendant(self) -> None:
        """An abrupt engine death must not orphan Pi or its guarded broker."""

        source_root = Path(__file__).resolve().parents[4]
        artifact_dir = self.root / "parent-death-artifacts"
        artifact_dir.mkdir()
        pi_pid_path = self.root / "pi.pid"
        broker_pid_path = self.root / "broker.pid"
        ready_path = self.root / "guards-ready"

        broker_script = self.root / "guarded-broker.py"
        broker_script.write_text(
            textwrap.dedent(
                """\
                import os
                import pathlib
                import sys
                import time

                from harness.v2.pi.security import arm_parent_death_guard

                expected_parent = int(sys.argv[1])
                pid_path = pathlib.Path(sys.argv[2])
                arm_parent_death_guard(expected_parent)
                pid_path.write_text(str(os.getpid()), encoding="utf-8")
                while True:
                    time.sleep(1)
                """
            ),
            encoding="utf-8",
        )
        pi_script = self.root / "fake-pi-with-broker.py"
        pi_script.write_text(
            textwrap.dedent(
                f"""\
                import os
                import pathlib
                import subprocess
                import sys
                import time

                pathlib.Path({str(pi_pid_path)!r}).write_text(
                    str(os.getpid()), encoding="utf-8"
                )
                broker = subprocess.Popen(
                    [
                        sys.executable,
                        {str(broker_script)!r},
                        str(os.getpid()),
                        {str(broker_pid_path)!r},
                    ],
                    stdin=subprocess.DEVNULL,
                    shell=False,
                )
                deadline = time.monotonic() + 10
                while (
                    not pathlib.Path({str(broker_pid_path)!r}).is_file()
                    and time.monotonic() < deadline
                ):
                    time.sleep(0.02)
                if not pathlib.Path({str(broker_pid_path)!r}).is_file():
                    broker.kill()
                    raise SystemExit(31)
                pathlib.Path({str(ready_path)!r}).write_text(
                    "ready\\n", encoding="utf-8"
                )
                while True:
                    time.sleep(1)
                """
            ),
            encoding="utf-8",
        )
        engine_script = self.root / "engine-parent.py"
        engine_script.write_text(
            textwrap.dedent(
                f"""\
                import os
                import sys
                import time
                from pathlib import Path

                from harness.v2.pi.engine import _run_pi_process

                class LiveStore:
                    def get_job(self, job_id):
                        return {{
                            "job": {{
                                "state": "running",
                                "task_id": "parent-death-task",
                                "task_revision": 1,
                                "workspace": {{"lease_owner": "test-owner"}},
                            }},
                            "runtime": {{
                                "lease_active": True,
                                "lease_token": 1,
                                "scopes": [{{
                                    "path": "Poincare/Test.lean",
                                    "active": True,
                                    "owner": "test-owner",
                                    "lease_token": 1,
                                }}],
                            }},
                        }}

                    def get_task(self, task_id):
                        return {{"task": {{"revision": 1, "status": "active"}}}}

                capability = {{
                    "job_id": "parent-death-job",
                    "task_id": "parent-death-task",
                    "task_revision": 1,
                    "lease_owner": "test-owner",
                    "lease_token": 1,
                    "allowed_paths": ["Poincare/Test.lean"],
                    "deadline_epoch": time.time() + 60,
                }}
                _run_pi_process(
                    argv=[sys.executable, {str(pi_script)!r}],
                    env={{
                        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                        "PYTHONPATH": {str(source_root)!r},
                        "PYTHONNOUSERSITE": "1",
                    }},
                    worktree=Path({str(self.root)!r}),
                    prompt=b"bounded parent-death test\\n",
                    artifact_dir=Path({str(artifact_dir)!r}),
                    store=LiveStore(),
                    capability=capability,
                    disk_budget_mb=64,
                    token_budget=128,
                )
                """
            ),
            encoding="utf-8",
        )

        engine = subprocess.Popen(
            [sys.executable, str(engine_script)],
            cwd=self.root,
            env={
                "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                "PYTHONPATH": str(source_root),
                "PYTHONNOUSERSITE": "1",
            },
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            shell=False,
        )
        pi_pid: int | None = None

        def force_cleanup() -> None:
            if engine.poll() is None:
                engine.kill()
                try:
                    engine.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    pass
            if pi_pid is not None:
                try:
                    os.killpg(pi_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            for stream in (engine.stdout, engine.stderr):
                if stream is not None:
                    stream.close()

        self.addCleanup(force_cleanup)
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline and not ready_path.is_file():
            if engine.poll() is not None:
                break
            time.sleep(0.02)
        if not ready_path.is_file():
            stdout, stderr = engine.communicate(timeout=2)
            self.fail(
                "engine did not arm both parent-death guards: "
                f"stdout={stdout!r} stderr={stderr!r}"
            )

        pi_pid = int(pi_pid_path.read_text(encoding="utf-8"))
        broker_pid = int(broker_pid_path.read_text(encoding="utf-8"))

        def process_state(pid: int) -> str | None:
            try:
                raw = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
            except FileNotFoundError:
                return None
            close = raw.rfind(")")
            if close < 0:
                return "?"
            fields = raw[close + 2 :].split()
            return fields[0] if fields else "?"

        self.assertNotIn(process_state(pi_pid), {None, "Z", "X"})
        self.assertNotIn(process_state(broker_pid), {None, "Z", "X"})
        os.kill(engine.pid, signal.SIGKILL)
        self.assertEqual(engine.wait(timeout=3), -int(signal.SIGKILL))

        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            states = (process_state(pi_pid), process_state(broker_pid))
            if all(state in {None, "Z", "X"} for state in states):
                break
            time.sleep(0.02)
        else:
            self.fail(
                "engine death left supervised processes running: "
                f"Pi={process_state(pi_pid)!r} broker={process_state(broker_pid)!r}"
            )

    def test_bubblewrap_argv_is_read_only_networkless_and_hides_git(self) -> None:
        worktree = self.root / "sandbox-worktree"
        control = self.root / "control"
        tools_dir = self.root / "tools"
        cache = self.root / "cache"
        worktree.mkdir()
        control.mkdir()
        tools_dir.mkdir()
        (tools_dir / "bin").mkdir()
        cache.mkdir()
        (worktree / ".git").write_text("gitdir: /not-mounted/common\n")
        (worktree / "Poincare").mkdir()
        (worktree / "Poincare/Test.lean").write_text("theorem x : True := by trivial\n")
        (worktree / "lake-manifest.json").write_text(
            json.dumps(
                {
                    "version": "1.1.0",
                    "packagesDir": ".lake/packages",
                    "lakeDir": ".lake",
                    "packages": [
                        {
                            "type": "git",
                            "name": "mathlib",
                            "scope": "",
                            "inherited": False,
                            "configFile": "lakefile.lean",
                            "manifestFile": "lake-manifest.json",
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        bwrap = tools_dir / "bwrap"
        lake = tools_dir / "bin/lake"
        lean = tools_dir / "bin/lean"
        for executable in (bwrap, lake, lean):
            executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            executable.chmod(0o755)
        manifest = cache / ".harness-cache.json"
        manifest.write_text("{}\n", encoding="utf-8")
        manifest.chmod(0o444)
        (cache / "packages/mathlib").mkdir(parents=True)
        (cache / "build").mkdir()
        (cache / "config").mkdir()
        package_overrides = cache / ".harness-package-overrides.json"
        package_overrides.write_bytes(canonical_package_overrides(worktree))
        package_overrides.chmod(0o444)
        runtime_library = tools_dir / "libfake.so"
        runtime_library.write_bytes(b"fake runtime library")
        metadata_fingerprint = "1" * 64
        runtime_mounts = [
            {
                "source": str(runtime_library),
                "destination": "/usr/lib/libfake.so",
                "sha256": hashlib.sha256(runtime_library.read_bytes()).hexdigest(),
            }
        ]
        spec = {
            "kind": "bubblewrap",
            "profile_version": BWRAP_PROFILE_VERSION,
            "bwrap_path": str(bwrap),
            "bwrap_sha256": hashlib.sha256(bwrap.read_bytes()).hexdigest(),
            "toolchain": {
                "source": str(tools_dir),
                "destination": "/opt/lean",
                "lake_host": str(lake),
                "lake_sandbox": "/opt/lean/bin/lake",
                "lake_sha256": hashlib.sha256(lake.read_bytes()).hexdigest(),
                "lean_host": str(lean),
                "lean_sandbox": "/opt/lean/bin/lean",
                "lean_sha256": hashlib.sha256(lean.read_bytes()).hexdigest(),
            },
            "runtime_mounts": runtime_mounts,
            "runtime_symlinks": [],
            "path_env": "/opt/lean/bin",
            "worktree": str(worktree),
            "worktree_entries": [
                {"name": "Poincare", "kind": "directory"},
                {"name": "lake-manifest.json", "kind": "file"},
            ],
            "lake_cache": {
                "source": str(cache),
                "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
                "cache_tree_sha256": "0" * 64,
                "package_overrides_sha256": hashlib.sha256(
                    package_overrides.read_bytes()
                ).hexdigest(),
                "metadata_fingerprint": metadata_fingerprint,
            },
            "forbidden_host_paths": [str(control), str(worktree)],
        }
        with (
            patch(
                "harness.v2.pi.security._runtime_library_mounts",
                return_value=(runtime_mounts, []),
            ),
            patch(
                "harness.v2.pi.security._cache_entries",
                return_value=(metadata_fingerprint, 1),
            ),
            patch(
                "harness.v2.pi.security._worktree_entries",
                return_value=spec["worktree_entries"],
            ),
        ):
            argv = list(
                bubblewrap_lean_argv(
                    spec=spec,
                    worktree=worktree,
                    command=("lake", "env", "lean", "Poincare/Test.lean"),
                )
            )
        for flag in (
            "--unshare-all",
            "--unshare-user",
            "--die-with-parent",
            "--new-session",
            "--disable-userns",
            "--clearenv",
            "--cap-drop",
            "--remount-ro",
        ):
            self.assertIn(flag, argv)
        self.assertNotIn("--share-net", argv)
        self.assertNotIn("--bind", argv)
        self.assertNotIn(str(control), argv)
        self.assertIn(
            [
                "--ro-bind",
                str(worktree / "Poincare"),
                "/work/Poincare",
            ],
            [argv[index : index + 3] for index in range(len(argv) - 2)],
        )
        self.assertIn(
            ["--ro-bind", str(cache), "/work/.lake"],
            [argv[index : index + 3] for index in range(len(argv) - 2)],
        )
        self.assertIn(
            ["--chdir", "/work"],
            [argv[index : index + 2] for index in range(len(argv) - 1)],
        )
        self.assertNotIn(str(worktree / ".git"), argv)
        self.assertEqual(
            argv[-5:],
            [
                "/opt/lean/bin/lake",
                "--packages=/work/.lake/.harness-package-overrides.json",
                "env",
                "/opt/lean/bin/lean",
                "Poincare/Test.lean",
            ],
        )

    def test_lake_cache_accepts_only_fully_dereferenced_read_only_files(self) -> None:
        source = self.root / "source.olean"
        source.write_bytes(b"compiled Lean object")
        cache = self.root / "dereferenced-cache"
        cache.mkdir()
        destination = cache / "Mathlib.olean"
        shutil.copy2(source, destination, follow_symlinks=True)
        destination.chmod(0o444)
        cache.chmod(0o555)
        try:
            digest = lake_cache_tree_digest(cache)
            self.assertRegex(digest, r"^[0-9a-f]{64}$")
            self.assertTrue(destination.is_file())
            self.assertFalse(destination.is_symlink())
        finally:
            cache.chmod(0o755)
            destination.chmod(0o644)

    def test_lake_cache_rejects_absolute_escaping_broken_and_internal_symlinks(self) -> None:
        external = self.root / "external.olean"
        external.write_bytes(b"outside")
        targets = {
            "absolute": str(external.resolve()),
            "escaping": "../external.olean",
            "broken": "missing.olean",
            "internal": "real.olean",
        }
        for label, target in targets.items():
            with self.subTest(label=label):
                cache = self.root / f"symlink-cache-{label}"
                cache.mkdir()
                regular = cache / "real.olean"
                regular.write_bytes(b"inside")
                regular.chmod(0o444)
                (cache / "linked.olean").symlink_to(target)
                cache.chmod(0o555)
                try:
                    with self.assertRaisesRegex(SecurityError, "symlink"):
                        lake_cache_tree_digest(cache)
                finally:
                    cache.chmod(0o755)
                    regular.chmod(0o644)


@unittest.skipUnless(
    os.environ.get("PI_08010_BIN"),
    "set PI_08010_BIN to run the actual pinned Pi extension integration",
)
@unittest.skip(
    "obsolete unsandboxed extension fixture; actual Pi now requires the full Linux sealed-install/bwrap/RPC deployment"
)
class ActualPiExtensionTest(unittest.TestCase):
    def test_08010_loads_extension_and_resolves_system_prompt_file(self) -> None:
        pi_bin = Path(os.environ["PI_08010_BIN"]).resolve(strict=True)
        version = subprocess.run(
            [str(pi_bin), "-v"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        self.assertEqual(version, PI_VERSION)

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            agent_dir = root / "agent"
            session_dir = root / "sessions"
            pycache_dir = agent_dir / "pycache"
            agent_dir.mkdir()
            session_dir.mkdir()
            pycache_dir.mkdir()
            source_root = Path(__file__).resolve().parents[4]
            for relative in TRUSTED_CODE_PATHS:
                source = source_root / relative
                destination = root / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
            extension = root / "harness/v2/pi/extension.ts"
            extension_hash = hashlib.sha256(extension.read_bytes()).hexdigest()
            system_prompt = root / "system-prompt.md"
            system_prompt.write_text(SYSTEM_PROMPT + "\n", encoding="utf-8")
            system_prompt_hash = hashlib.sha256(system_prompt.read_bytes()).hexdigest()

            server = _NoDnsServer(("127.0.0.1", 0), _SSEHandler)
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            _SSEState.requests = []
            thread.start()
            self.addCleanup(server.server_close)
            self.addCleanup(lambda: thread.join(timeout=2))
            self.addCleanup(server.shutdown)
            endpoint = f"http://127.0.0.1:{server.server_address[1]}/v1"

            capability = {
                "schema_version": "poincare.pi-capability.v1",
                "job_id": "actual-pi-load-test",
                "control_root": str(root),
                "backend": {
                    "kind": "leanstral",
                    "model": MODEL,
                    "model_revision": REVISION,
                    "endpoint": endpoint,
                    "sampling": {"max_tokens": 64, "temperature": 0},
                },
                "extension_sha256": extension_hash,
                "system_prompt_sha256": system_prompt_hash,
                "trusted_code": _trusted_manifest_without_git_check(root),
            }
            capability_path = root / "capability.json"
            capability_path.write_text(
                json.dumps(capability, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            capability_hash = hashlib.sha256(capability_path.read_bytes()).hexdigest()
            session_id = str(uuid.uuid4())
            argv = [
                str(pi_bin),
                "--mode",
                "json",
                "--provider",
                "harness-leanstral",
                "--model",
                MODEL,
                "--session-id",
                session_id,
                "--session-dir",
                str(session_dir),
                "--name",
                "actual-pi-load-test",
                "--no-builtin-tools",
                "--tools",
                ",".join(TOOL_NAMES),
                "--extension",
                str(extension),
                "--no-extensions",
                "--no-skills",
                "--no-prompt-templates",
                "--no-themes",
                "--no-context-files",
                "--no-approve",
                "--offline",
                "--system-prompt",
                str(system_prompt),
            ]
            safe_env = {
                "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
                "HOME": str(root),
                "LANG": "C.UTF-8",
                "TMPDIR": str(root),
                "PYTHONPATH": str(Path(__file__).resolve().parents[4]),
                "PYTHONPYCACHEPREFIX": str(pycache_dir),
                "PYTHONSAFEPATH": "1",
                "PYTHONNOUSERSITE": "1",
                "PI_CODING_AGENT_DIR": str(agent_dir),
                "PI_OFFLINE": "1",
                "PI_SKIP_VERSION_CHECK": "1",
                "PI_TELEMETRY": "0",
                "NO_PROXY": "127.0.0.1",
                "no_proxy": "127.0.0.1",
                "HARNESS_PI_CAPABILITY": str(capability_path),
                "HARNESS_PI_CAPABILITY_SHA256": capability_hash,
                "HARNESS_PI_EXTENSION_PATH": str(extension),
                "HARNESS_PI_EXTENSION_SHA256": extension_hash,
                "HARNESS_PI_SYSTEM_PROMPT_PATH": str(system_prompt),
                "HARNESS_PI_SYSTEM_PROMPT_SHA256": system_prompt_hash,
                "HARNESS_PI_PYTHON": os.path.realpath(os.sys.executable),
                "HARNESS_PI_CONTEXT_WINDOW": "200000",
            }
            result = subprocess.run(
                argv,
                cwd=root,
                env=safe_env,
                input="# bounded test\n",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                check=False,
                text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            events = [json.loads(line) for line in result.stdout.splitlines() if line]
            self.assertEqual(events[0]["type"], "session")
            self.assertTrue(any(event["type"] == "agent_settled" for event in events))
            assistant = [
                event["message"]
                for event in events
                if event["type"] == "message_end"
                and event.get("message", {}).get("role") == "assistant"
            ][-1]
            self.assertEqual(assistant["stopReason"], "stop")
            self.assertEqual(len(_SSEState.requests), 1)
            request = _SSEState.requests[0]
            # The OpenAI-compatible client still serializes Pi's fixed
            # non-secret placeholder. Ambient LEANSTRAL_API_KEY is never
            # inherited or interpolated into the provider.
            self.assertEqual(request["authorization"], "Bearer unused")
            self.assertEqual(request["payload"].get("max_tokens"), 64)
            self.assertEqual(request["payload"].get("temperature"), 0)
            for unsupported in (
                "top_p",
                "top_k",
                "reasoning_effort",
                "max_completion_tokens",
            ):
                self.assertNotIn(unsupported, request["payload"])
            system_messages = [
                message["content"]
                for message in request["payload"]["messages"]
                if message.get("role") == "system"
            ]
            self.assertEqual(system_messages, [SYSTEM_PROMPT + "\n"])
            tool_names = sorted(
                item["function"]["name"] for item in request["payload"].get("tools", [])
            )
            self.assertEqual(tool_names, sorted(TOOL_NAMES))


if __name__ == "__main__":
    unittest.main()
