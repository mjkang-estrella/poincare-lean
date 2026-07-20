"""One-fresh-Pi-session execution engine for a claimed Harness v2 Job."""

from __future__ import annotations

import errno
import hashlib
import inspect
import json
import math
import os
import re
import secrets
import selectors
import signal
import stat
import subprocess
import tempfile
import time
import uuid
from contextlib import ExitStack
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Callable
from urllib.parse import urlsplit, urlunsplit

from harness.v2.runtime.store import HarnessError, HarnessStore
from harness.v2.worker.artifacts import canonical_json_bytes
from harness.v2.worker.client import LeanstralConfig, check_health

from . import PROVIDER_NAME, TOOL_NAMES
from .broker import BrokerError, BrokerSession, _git, _validate_live
from .integrity import IntegrityError, attest_trusted_code
from .install import (
    PiInstallError,
    canonical_manifest_bytes as canonical_install_manifest_bytes,
    install_manifest_sha256,
    verify_sealed_install_files,
)
from .journal import (
    CommittedPatch,
    PatchJournalError,
    ReplayObservation,
    replay_committed_patches,
    verify_patch_journal,
)
from .quota import PiQuotaError, SharedArtifactQuota
from .rpc import RpcError, UnixRpcServer
from .security import (
    SecurityError,
    _parent_death_preexec,
    acquire_build_job_lock,
    audit_pi_bubblewrap,
    audit_sparse_lean_bubblewrap,
    build_sparse_lean_snapshot,
    bubblewrap_pi_argv,
    bubblewrap_sparse_lean_argv,
    lean_acceptance_argv,
    path_is_allowed,
    remove_sparse_lean_snapshot,
    run_limited,
    validate_patch,
)
from .snapshot import PiPromptSnapshot, SnapshotError, build_snapshot


class PiEngineError(RuntimeError):
    """Raised when a Pi Job cannot start or its evidence is invalid."""


class _FinalDiffAuditError(PiEngineError):
    def __init__(self, message: str, *, patch: bytes, audit: dict[str, Any]) -> None:
        super().__init__(message)
        self.patch = patch
        self.audit = audit


SYSTEM_PROMPT = (
    "You are the bounded Leanstral proof worker for one immutable Harness v2 Job. "
    "Use only the six scoped tools. Codex alone controls worktrees, gates, acceptance, "
    "commits, and services. Follow the complete Task contract in the user prompt. "
    "Work tersely: inspect only necessary context, apply the smallest scoped patch early, "
    "and iterate with lean_check instead of narrating analysis. For apply_patch_scoped, "
    "include diff --git headers and exact unified-diff hunk line counts; prefer separate "
    "small hunks when that makes the counts obvious."
)
MESSAGE_EVENTS = {"message_start", "message_update", "message_end"}
TOOL_EVENTS = {"tool_execution_start", "tool_execution_update", "tool_execution_end"}
PROMPT_WRITE_TIMEOUT_SECONDS = 30.0
PI_PRIVATE_SETTINGS_BYTES = b'{"compaction":{"enabled":false}}'
PI_STREAM_EVIDENCE_MAX_BYTES = 1024 * 1024 * 1024


@dataclass(frozen=True)
class PiRunResult:
    job_id: str
    success: bool
    exit_reason: str
    process_returncode: int
    events: int
    messages: int
    tool_events: int
    output_tokens: int
    session_artifact: str | None
    final_report_artifact: str
    patch_artifact: str
    result_artifact: str


@dataclass
class _EventState:
    expected_session_id: str = ""
    expected_prompt_sha256: str = ""
    expected_prompt_size_bytes: int = 0
    expected_provider: str = ""
    expected_model: str = ""
    expected_cwd: str = "/runtime"
    event_count: int = 0
    message_count: int = 0
    tool_event_count: int = 0
    output_tokens: int = 0
    saw_session_header: bool = False
    saw_agent_settled: bool = False
    last_assistant: dict[str, Any] | None = None
    active_tools: dict[str, str] | None = None
    assistant_message_active: bool = False
    inflight_output_tokens: int = 0
    phase: str = "expect_session"
    active_message_role: str | None = None
    active_message_sha256: str | None = None
    last_assistant_sha256: str | None = None
    expected_tool_calls: dict[str, str] | None = None
    completed_tool_calls: set[str] | None = None
    completed_tool_results: set[str] | None = None
    current_agent_assistant_count: int = 0
    agent_run_count: int = 0
    saw_initial_user: bool = False
    retry_active: bool = False

    def __post_init__(self) -> None:
        if self.active_tools is None:
            self.active_tools = {}
        if self.expected_tool_calls is None:
            self.expected_tool_calls = {}
        if self.completed_tool_calls is None:
            self.completed_tool_calls = set()
        if self.completed_tool_results is None:
            self.completed_tool_results = set()


def _sparse_lean_acceptance_commands(task: dict[str, Any]) -> list[list[str]]:
    """Select every exact Lean-file gate accepted by the shared broker parser."""

    selected: list[list[str]] = []
    for command in task["acceptance"]["commands"]:
        try:
            lean_acceptance_argv(command)
        except SecurityError:
            continue
        selected.append(list(command))
    return selected


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _write_sealed_input(directory: Path, name: str, data: bytes) -> Path:
    if name in {"", ".", ".."} or "/" in name or "\x00" in name:
        raise PiEngineError("sealed Pi input name is unsafe")
    target = directory / name
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(target, flags, 0o400)
    except OSError as exc:
        raise PiEngineError(f"cannot create sealed Pi input {name}: {exc}") from exc
    try:
        remaining = memoryview(data)
        while remaining:
            written = os.write(descriptor, remaining)
            if written <= 0:
                raise PiEngineError(f"short write creating sealed Pi input {name}")
            remaining = remaining[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    if target.is_symlink() or not target.is_file() or target.stat().st_mode & 0o222:
        raise PiEngineError(f"sealed Pi input is not immutable: {name}")
    return target


def _public_pi_config(
    *,
    job: dict[str, Any],
    session_id: str,
    extension_sha256: str,
    output_token_budget: int,
    system_prompt_sha256: str,
    prompt_sha256: str,
    prompt_size_bytes: int,
    settings_sha256: str,
) -> dict[str, Any]:
    return {
        "schema_version": "poincare.pi-public-config.v2",
        "job_id": job["id"],
        "session_id": session_id,
        "backend": job["backend"],
        "extension_sha256": extension_sha256,
        "output_token_budget": output_token_budget,
        "prompt_sha256": prompt_sha256,
        "prompt_size_bytes": prompt_size_bytes,
        "system_prompt_path": "/sealed/system-prompt.md",
        "system_prompt_sha256": system_prompt_sha256,
        "settings_path": "/sealed/agent/settings.json",
        "settings_sha256": settings_sha256,
        "broker": {
            "socket_env": "HARNESS_PI_BROKER_SOCKET",
            "token_env": "HARNESS_PI_BROKER_TOKEN",
        },
    }


def _normalize_endpoint(raw: str) -> str:
    parsed = urlsplit(raw.rstrip("/"))
    if (
        parsed.scheme not in {"http", "https"}
        or not parsed.netloc
        or parsed.username is not None
        or parsed.password is not None
        or parsed.query
        or parsed.fragment
    ):
        raise PiEngineError("Leanstral endpoint must be credential-free HTTP(S)")
    path = parsed.path.rstrip("/")
    if not path.endswith("/v1"):
        path += "/v1"
    return urlunsplit((parsed.scheme, parsed.netloc, path, "", ""))


def _resolved_directory(path: str | Path, label: str) -> Path:
    lexical = Path(path).expanduser().absolute()
    if lexical.is_symlink():
        raise PiEngineError(f"{label} must not be a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise PiEngineError(f"cannot resolve {label}: {exc}") from exc
    if not resolved.is_dir():
        raise PiEngineError(f"{label} is not a directory")
    return resolved


def _read_sealed_file(
    raw_path: str | Path, *, label: str, maximum_bytes: int
) -> tuple[Path, bytes]:
    lexical = Path(raw_path).expanduser().absolute()
    if lexical.is_symlink():
        raise PiEngineError(f"{label} must not be a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise PiEngineError(f"cannot resolve {label}: {exc}") from exc
    if resolved != lexical or not resolved.is_file():
        raise PiEngineError(f"{label} must be a canonical regular file")
    metadata = resolved.stat(follow_symlinks=False)
    if metadata.st_mode & 0o222:
        raise PiEngineError(f"{label} must be sealed read-only")
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(resolved, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size > maximum_bytes:
            raise PiEngineError(f"{label} is not a bounded regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, maximum_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
            if total > maximum_bytes:
                raise PiEngineError(f"{label} exceeds {maximum_bytes} bytes")
        after = os.fstat(descriptor)
        if (
            before.st_dev,
            before.st_ino,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise PiEngineError(f"{label} changed while being read")
    finally:
        os.close(descriptor)
    return resolved, b"".join(chunks)


def _verify_sealed_pi_install(
    *, manifest_path: str | Path, dependency_graph_path: str | Path
) -> tuple[dict[str, Any], bytes, str, Path, Path]:
    sealed_path, raw_manifest = _read_sealed_file(
        manifest_path, label="sealed Pi install manifest", maximum_bytes=64 * 1024 * 1024
    )
    graph_path, graph = _read_sealed_file(
        dependency_graph_path,
        label="sealed Pi dependency graph",
        maximum_bytes=64 * 1024 * 1024,
    )
    try:
        verified = verify_sealed_install_files(sealed_path, graph_path)
        if verified.get("npm_dependency_graph") is None:
            raise PiEngineError("production Pi manifest must attest the full npm dependency graph")
        if canonical_install_manifest_bytes(verified) != raw_manifest:
            raise PiEngineError("sealed Pi install manifest is not canonical JSON")
    except (KeyError, TypeError, PiInstallError) as exc:
        raise PiEngineError(f"Pi distribution attestation failed: {exc}") from exc
    return verified, graph, install_manifest_sha256(verified), sealed_path, graph_path


def _validated_sampling(
    task: dict[str, Any], job: dict[str, Any]
) -> tuple[int, float]:
    """Return the only sampling values Pi is allowed to send to vLLM."""

    sampling = job.get("backend", {}).get("sampling")
    if not isinstance(sampling, dict) or set(sampling) != {
        "max_tokens",
        "temperature",
    }:
        raise PiEngineError(
            "Pi backend sampling must contain exactly max_tokens and temperature"
        )
    max_tokens = sampling["max_tokens"]
    if (
        isinstance(max_tokens, bool)
        or not isinstance(max_tokens, int)
        or max_tokens < 1
        or max_tokens > task["budget"]["max_output_tokens"]
    ):
        raise PiEngineError("Pi max_tokens is invalid or exceeds the Task budget")
    temperature = sampling["temperature"]
    if (
        isinstance(temperature, bool)
        or not isinstance(temperature, (int, float))
        or not math.isfinite(float(temperature))
        or not 0 <= float(temperature) <= 2
    ):
        raise PiEngineError("Pi temperature must be a finite number between 0 and 2")
    return max_tokens, float(temperature)


def _call_health_checker(
    checker: Callable[..., Any], config: LeanstralConfig, artifact_dir: Path
) -> Any:
    """Support the production checker and artifact-aware test/legacy wrappers."""

    try:
        parameters = inspect.signature(checker).parameters.values()
    except (TypeError, ValueError):
        parameters = ()
    artifact_aware = any(
        item.name == "artifact_dir" or item.kind == inspect.Parameter.VAR_KEYWORD
        for item in parameters
    )
    if artifact_aware:
        return checker(config, artifact_dir=artifact_dir)
    return checker(config)


def _validate_records(
    *,
    store: HarnessStore,
    job_id: str,
    lease_owner: str,
    lease_token: int,
    control_root: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], Path, Path]:
    try:
        payload = store.get_job(job_id)
    except HarnessError as exc:
        raise PiEngineError(f"cannot load Job: {exc}") from exc
    job = payload["job"]
    runtime = payload["runtime"]
    try:
        task_payload = store.get_task(job["task_id"], job["task_revision"])
        latest_task_payload = store.get_task(job["task_id"])
    except HarnessError as exc:
        raise PiEngineError(f"cannot load Task: {exc}") from exc
    task = task_payload["task"]
    latest_task = latest_task_payload["task"]
    if latest_task["revision"] != job["task_revision"]:
        raise PiEngineError("Job Task revision is stale; only the latest revision may launch")
    if job["state"] != "running" or task["status"] != "active":
        raise PiEngineError("run-job requires a running Job and active Task")
    if not runtime["lease_active"]:
        raise PiEngineError("run-job requires an active lease")
    if job["workspace"]["lease_owner"] != lease_owner or runtime["lease_token"] != lease_token:
        raise PiEngineError("lease owner or fencing token mismatch")
    expected_scopes = set(task["scope"]["allowed_paths"])
    scopes = runtime["scopes"]
    if {item["path"] for item in scopes} != expected_scopes or any(
        not item["active"]
        or item["owner"] != lease_owner
        or item["lease_token"] != lease_token
        for item in scopes
    ):
        raise PiEngineError("Job does not hold its exact Task file scopes")
    if (
        job["task_revision"] != task["revision"]
        or job["workspace"]["base_commit"] != task["base_commit"]
    ):
        raise PiEngineError("Task revision or base commit mismatch")
    backend = job["backend"]
    if backend["kind"] != "leanstral":
        raise PiEngineError("Pi Job backend must be leanstral")
    _validated_sampling(task, job)
    expected_endpoint = os.environ.get("LEANSTRAL_BASE_URL", "")
    expected_model = os.environ.get("LEANSTRAL_MODEL", "")
    expected_revision = os.environ.get("LEANSTRAL_MODEL_REVISION", "")
    if not expected_endpoint or not expected_model or not expected_revision:
        raise PiEngineError(
            "LEANSTRAL_BASE_URL, LEANSTRAL_MODEL, and LEANSTRAL_MODEL_REVISION are required"
        )
    if (
        _normalize_endpoint(backend["endpoint"]) != _normalize_endpoint(expected_endpoint)
        or backend["model"] != expected_model
        or backend["model_revision"] != expected_revision
    ):
        raise PiEngineError("Job backend endpoint/model/revision does not match pinned environment")

    worktree = _resolved_directory(job["workspace"]["worktree"], "Job worktree")
    top = Path(_git(worktree, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    head = _git(worktree, "rev-parse", "HEAD").decode().strip()
    branch = _git(worktree, "symbolic-ref", "--quiet", "--short", "HEAD").decode().strip()
    if top != worktree or head != task["base_commit"] or branch != job["workspace"]["branch"]:
        raise PiEngineError("worktree root, branch, or HEAD does not match the Job")
    status = _git(worktree, "status", "--porcelain", "--untracked-files=all")
    if status:
        raise PiEngineError("fresh Pi Job worktree must be clean before launch")

    artifact_dir = _resolved_directory(runtime["artifact_directory"], "Job artifact directory")
    expected_artifact = (
        control_root / Path(*PurePosixPath(job["artifacts"]["directory"]).parts)
    ).resolve(strict=True)
    if artifact_dir != expected_artifact:
        raise PiEngineError("Job artifact directory escaped the control repository")
    return task, job, runtime, worktree, artifact_dir


def _write_snapshot(
    *,
    snapshot: PiPromptSnapshot,
    job: dict[str, Any],
    artifact_store: Any,
) -> None:
    if (
        snapshot.prompt_sha256 != job["artifacts"]["prompt_sha256"]
        or snapshot.context_sha256 != job["artifacts"]["context_sha256"]
    ):
        raise PiEngineError(
            "Pi prompt/context snapshot hash differs from immutable Job; create a fresh Job with `snapshot` output"
        )
    artifact_store.write_once(
        "prompt.md", snapshot.prompt.encode("utf-8"), allow_identical_existing=True
    )
    artifact_store.write_once(
        "context-manifest.json",
        canonical_json_bytes(snapshot.manifest),
        allow_identical_existing=True,
    )


def _readable_paths(task: dict[str, Any], worktree: Path) -> list[str]:
    paths = list(task["context"]["files"])
    for scope in task["scope"]["allowed_paths"]:
        if any(marker in scope for marker in "*?["):
            continue
        candidate = worktree / Path(*PurePosixPath(scope).parts)
        if candidate.is_file() and not candidate.is_symlink() and scope not in paths:
            paths.append(scope)
    return sorted(paths)


def _build_capability(
    *,
    task: dict[str, Any],
    job: dict[str, Any],
    state_dir: Path,
    control_root: Path,
    artifact_dir: Path,
    worktree: Path,
    lease_owner: str,
    lease_token: int,
    extension_sha256: str,
    system_prompt_sha256: str,
    session_id: str,
    launched_at: float,
    lean_timeout_seconds: int,
    artifact_quota_bytes: int,
    trusted_code: dict[str, Any],
    lean_scratch_root: Path,
    sparse_lean: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": "poincare.pi-capability.v1",
        "session_id": session_id,
        "job_id": job["id"],
        "task_id": task["id"],
        "task_revision": task["revision"],
        "state_dir": str(state_dir),
        "control_root": str(control_root),
        "artifact_dir": str(artifact_dir),
        "worktree": str(worktree),
        "base_commit": task["base_commit"],
        "branch": job["workspace"]["branch"],
        "lease_owner": lease_owner,
        "lease_token": lease_token,
        "allowed_paths": task["scope"]["allowed_paths"],
        "forbidden_paths": task["scope"]["forbidden_paths"],
        "readable_paths": _readable_paths(task, worktree),
        "acceptance_commands": task["acceptance"]["commands"],
        "forbidden_added_tokens": task["acceptance"]["forbidden_added_tokens"],
        "backend": job["backend"],
        "prompt_sha256": job["artifacts"]["prompt_sha256"],
        "context_sha256": job["artifacts"]["context_sha256"],
        "launched_at_epoch": launched_at,
        "deadline_epoch": launched_at + task["budget"]["wall_clock_minutes"] * 60,
        "lean_timeout_seconds": lean_timeout_seconds,
        "artifact_quota_bytes": artifact_quota_bytes,
        "extension_sha256": extension_sha256,
        "system_prompt_sha256": system_prompt_sha256,
        "trusted_code": trusted_code,
        "lean_scratch_root": str(lean_scratch_root),
        "sparse_lean": sparse_lean,
    }


def _append_line(handle: Any, raw: bytes) -> None:
    if isinstance(handle, _QuotaAppender):
        handle.quota.append(handle.relative_path, raw)
        return
    handle.write(raw)
    handle.flush()
    os.fsync(handle.fileno())


@dataclass(frozen=True)
class _QuotaAppender:
    quota: SharedArtifactQuota
    relative_path: str


def _message_text(message: dict[str, Any]) -> str:
    content = message.get("content")
    if isinstance(content, str):
        return content
    if not isinstance(content, list):
        return ""
    return "\n".join(
        item.get("text", "")
        for item in content
        if isinstance(item, dict) and item.get("type") == "text" and isinstance(item.get("text"), str)
    )


def _assistant_output_usage(message: dict[str, Any], *, final: bool) -> int:
    usage = message.get("usage")
    if not isinstance(usage, dict):
        raise PiEngineError("Pi assistant message is missing provider usage")
    output = usage.get("output")
    if (
        isinstance(output, bool)
        or not isinstance(output, int)
        or output < 0
        or (final and output == 0)
    ):
        qualifier = "final " if final else ""
        raise PiEngineError(
            f"Pi {qualifier}assistant message has missing or invalid output-token usage"
        )
    return output


def _message_sha256(message: dict[str, Any]) -> str:
    try:
        return _sha256(canonical_json_bytes(message))
    except (TypeError, ValueError) as exc:
        raise PiEngineError("Pi message is not canonical JSON") from exc


def _exact_user_prompt(message: dict[str, Any], state: _EventState) -> None:
    content = message.get("content")
    if (
        message.get("role") != "user"
        or not isinstance(content, list)
        or len(content) != 1
        or not isinstance(content[0], dict)
        or content[0].get("type") != "text"
        or not isinstance(content[0].get("text"), str)
    ):
        raise PiEngineError("Pi initial user message changed the canonical prompt encoding")
    prompt = content[0]["text"].encode("utf-8")
    if (
        len(prompt) != state.expected_prompt_size_bytes
        or _sha256(prompt) != state.expected_prompt_sha256
    ):
        raise PiEngineError("Pi initial user message does not match the Job prompt hash")


def _validate_assistant_identity(message: dict[str, Any], state: _EventState) -> None:
    if (
        message.get("role") != "assistant"
        or message.get("provider") != state.expected_provider
        or message.get("model") != state.expected_model
        or message.get("api") != "openai-completions"
        or not isinstance(message.get("content"), list)
    ):
        raise PiEngineError("Pi assistant message changed the pinned provider/model identity")


def _assistant_tool_calls(message: dict[str, Any]) -> dict[str, str]:
    calls: dict[str, str] = {}
    for part in message.get("content", []):
        if not isinstance(part, dict) or part.get("type") != "toolCall":
            continue
        call_id = part.get("id")
        name = part.get("name")
        if not isinstance(call_id, str) or not isinstance(name, str):
            raise PiEngineError("Pi assistant emitted a malformed tool call")
        if name not in TOOL_NAMES:
            raise PiEngineError(f"Pi assistant requested a non-allowlisted tool: {name}")
        if call_id in calls:
            raise PiEngineError("Pi assistant reused a tool-call ID in one turn")
        calls[call_id] = name
    return calls


def _last_assistant_sha256(messages: Any) -> str | None:
    if not isinstance(messages, list):
        raise PiEngineError("Pi agent_end lacks its completed message list")
    for message in reversed(messages):
        if isinstance(message, dict) and message.get("role") == "assistant":
            return _message_sha256(message)
    return None


def _consume_event(
    raw: bytes,
    *,
    state: _EventState,
    messages_handle: Any,
    tools_handle: Any,
    token_budget: int,
) -> None:
    try:
        event = json.loads(
            raw.decode("utf-8"),
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"non-JSON constant: {value}")
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise PiEngineError("Pi JSON mode emitted a non-JSON line") from exc
    if not isinstance(event, dict) or not isinstance(event.get("type"), str):
        raise PiEngineError("Pi JSON event is not an object with a type")
    event_type = event["type"]
    if state.phase == "settled":
        raise PiEngineError("Pi emitted an event after agent_settled")
    state.event_count += 1
    if "compact" in event_type.lower():
        raise PiEngineError(f"Pi attempted a forbidden compaction path: {event_type}")

    allowed_events = {
        "session",
        "agent_start",
        "turn_start",
        *MESSAGE_EVENTS,
        *TOOL_EVENTS,
        "turn_end",
        "agent_end",
        "agent_settled",
        "auto_retry_start",
        "auto_retry_end",
    }
    if event_type not in allowed_events:
        raise PiEngineError(f"Pi JSON stream emitted an unknown event: {event_type}")

    if event_type == "session":
        if state.phase != "expect_session" or state.event_count != 1:
            raise PiEngineError("Pi emitted a duplicate or out-of-order session header")
        if (
            event.get("version") != 3
            or event.get("id") != state.expected_session_id
            or event.get("cwd") != state.expected_cwd
            or not isinstance(event.get("timestamp"), str)
            or not event["timestamp"]
            or event.get("parentSession") is not None
        ):
            raise PiEngineError("Pi session header does not match the fresh sealed Job session")
        state.saw_session_header = True
        state.phase = "expect_agent_start"
        return

    if state.phase == "expect_session":
        raise PiEngineError("Pi JSON stream did not start with a session header")

    if event_type == "agent_start":
        if state.phase not in {"expect_agent_start", "expect_retry_agent_start"}:
            raise PiEngineError("Pi emitted agent_start out of order")
        if state.phase == "expect_retry_agent_start" and not state.retry_active:
            raise PiEngineError("Pi retry agent started without an active retry")
        state.agent_run_count += 1
        state.current_agent_assistant_count = 0
        state.phase = "expect_turn_start"
        return

    if event_type == "turn_start":
        if state.phase not in {"expect_turn_start", "after_turn"}:
            raise PiEngineError("Pi emitted turn_start out of order")
        if state.agent_run_count == 1 and not state.saw_initial_user:
            state.phase = "expect_initial_user_start"
        else:
            state.phase = "expect_assistant_start"
        return

    if event_type in MESSAGE_EVENTS:
        _append_line(messages_handle, raw)
        state.message_count += 1
        message = event.get("message")
        if not isinstance(message, dict):
            raise PiEngineError("Pi message event lacks a message object")

        if event_type == "message_start" and state.phase == "expect_initial_user_start":
            _exact_user_prompt(message, state)
            state.active_message_role = "user"
            state.active_message_sha256 = _message_sha256(message)
            state.phase = "expect_initial_user_end"
            return
        if event_type == "message_end" and state.phase == "expect_initial_user_end":
            _exact_user_prompt(message, state)
            if (
                state.active_message_role != "user"
                or _message_sha256(message) != state.active_message_sha256
            ):
                raise PiEngineError("Pi changed the initial user message during its lifecycle")
            state.active_message_role = None
            state.active_message_sha256 = None
            state.saw_initial_user = True
            state.phase = "expect_assistant_start"
            return

        if (
            event_type == "message_start"
            and state.phase == "after_assistant_message"
            and message.get("role") == "toolResult"
        ):
            assert state.expected_tool_calls is not None
            assert state.completed_tool_calls is not None
            assert state.completed_tool_results is not None
            call_id = message.get("toolCallId")
            tool_name = message.get("toolName")
            if (
                not isinstance(call_id, str)
                or not isinstance(tool_name, str)
                or state.expected_tool_calls.get(call_id) != tool_name
                or call_id not in state.completed_tool_calls
                or call_id in state.completed_tool_results
            ):
                raise PiEngineError("Pi emitted an unmatched tool-result message")
            state.active_message_role = "toolResult"
            state.active_message_sha256 = _message_sha256(message)
            state.phase = "in_tool_result_message"
            return
        if event_type == "message_end" and state.phase == "in_tool_result_message":
            assert state.expected_tool_calls is not None
            assert state.completed_tool_results is not None
            call_id = message.get("toolCallId")
            tool_name = message.get("toolName")
            if (
                state.active_message_role != "toolResult"
                or not isinstance(call_id, str)
                or state.expected_tool_calls.get(call_id) != tool_name
                or _message_sha256(message) != state.active_message_sha256
            ):
                raise PiEngineError("Pi changed a tool-result message during its lifecycle")
            state.completed_tool_results.add(call_id)
            state.active_message_role = None
            state.active_message_sha256 = None
            state.phase = "after_assistant_message"
            return

        if event_type == "message_start":
            if state.phase != "expect_assistant_start" or state.assistant_message_active:
                raise PiEngineError("Pi started an assistant message out of order")
            _validate_assistant_identity(message, state)
            state.assistant_message_active = True
            state.active_message_role = "assistant"
            state.inflight_output_tokens = _assistant_output_usage(message, final=False)
            state.phase = "in_assistant_message"
        elif event_type == "message_update":
            if state.phase != "in_assistant_message" or not state.assistant_message_active:
                raise PiEngineError("Pi updated an assistant message that was not started")
            _validate_assistant_identity(message, state)
            output = _assistant_output_usage(message, final=False)
            if output < state.inflight_output_tokens:
                raise PiEngineError("Pi assistant streaming usage moved backwards")
            state.inflight_output_tokens = output
        else:
            if state.phase != "in_assistant_message" or not state.assistant_message_active:
                raise PiEngineError("Pi ended an assistant message that was not started")
            _validate_assistant_identity(message, state)
            output = _assistant_output_usage(message, final=True)
            if output < state.inflight_output_tokens:
                raise PiEngineError("Pi final assistant usage moved backwards")
            calls = _assistant_tool_calls(message)
            stop_reason = message.get("stopReason")
            if calls and stop_reason not in {"toolUse", "length"}:
                raise PiEngineError("Pi assistant tool calls have an inconsistent stopReason")
            if not calls and stop_reason == "toolUse":
                raise PiEngineError("Pi assistant reported toolUse without tool calls")
            state.output_tokens += output
            state.inflight_output_tokens = 0
            state.assistant_message_active = False
            state.active_message_role = None
            state.last_assistant = message
            state.last_assistant_sha256 = _message_sha256(message)
            state.current_agent_assistant_count += 1
            assert state.expected_tool_calls is not None
            assert state.completed_tool_calls is not None
            assert state.completed_tool_results is not None
            state.expected_tool_calls.clear()
            state.expected_tool_calls.update(calls)
            state.completed_tool_calls.clear()
            state.completed_tool_results.clear()
            state.phase = "after_assistant_message"
        if state.output_tokens + state.inflight_output_tokens > token_budget:
            raise PiEngineError("Pi session exceeded the Task output-token budget")
        return

    if event_type in TOOL_EVENTS:
        _append_line(tools_handle, raw)
        state.tool_event_count += 1
        if state.phase != "after_assistant_message":
            raise PiEngineError("Pi emitted a tool event outside its assistant turn")
        call_id = event.get("toolCallId")
        tool_name = event.get("toolName")
        if not isinstance(call_id, str) or not isinstance(tool_name, str):
            raise PiEngineError("Pi tool event lacks string call ID/name")
        if tool_name not in TOOL_NAMES:
            raise PiEngineError(f"Pi executed a non-allowlisted tool: {tool_name}")
        assert state.active_tools is not None
        assert state.expected_tool_calls is not None
        assert state.completed_tool_calls is not None
        if state.expected_tool_calls.get(call_id) != tool_name:
            raise PiEngineError("Pi executed a tool call not declared by the assistant")
        if event_type == "tool_execution_start":
            if call_id in state.active_tools or call_id in state.completed_tool_calls:
                raise PiEngineError("Pi emitted duplicate tool_execution_start")
            state.active_tools[call_id] = tool_name
        elif event_type == "tool_execution_update":
            if state.active_tools.get(call_id) != tool_name:
                raise PiEngineError("Pi emitted an unpaired tool_execution_update")
        else:
            if state.active_tools.pop(call_id, None) != tool_name:
                raise PiEngineError("Pi emitted an unpaired tool_execution_end")
            state.completed_tool_calls.add(call_id)
        return

    if event_type == "turn_end":
        if state.phase != "after_assistant_message":
            raise PiEngineError("Pi emitted turn_end before a completed assistant message")
        assert state.active_tools is not None
        assert state.expected_tool_calls is not None
        assert state.completed_tool_calls is not None
        assert state.completed_tool_results is not None
        if (
            state.active_tools
            or set(state.expected_tool_calls) != state.completed_tool_calls
            or set(state.expected_tool_calls) != state.completed_tool_results
        ):
            raise PiEngineError("Pi ended a turn with incomplete tool lifecycles")
        message = event.get("message")
        if (
            not isinstance(message, dict)
            or _message_sha256(message) != state.last_assistant_sha256
        ):
            raise PiEngineError("Pi turn_end does not reference the just-completed assistant")
        tool_results = event.get("toolResults")
        if not isinstance(tool_results, list):
            raise PiEngineError("Pi turn_end lacks its tool-result list")
        observed_results: dict[str, str] = {}
        for result in tool_results:
            if (
                not isinstance(result, dict)
                or result.get("role") != "toolResult"
                or not isinstance(result.get("toolCallId"), str)
                or not isinstance(result.get("toolName"), str)
            ):
                raise PiEngineError("Pi turn_end contains a malformed tool result")
            call_id = result["toolCallId"]
            if call_id in observed_results:
                raise PiEngineError("Pi turn_end contains duplicate tool results")
            observed_results[call_id] = result["toolName"]
        if observed_results != state.expected_tool_calls:
            raise PiEngineError("Pi turn_end tool results do not match the assistant calls")
        state.expected_tool_calls.clear()
        state.completed_tool_calls.clear()
        state.completed_tool_results.clear()
        state.phase = "after_turn"
        return

    if event_type == "agent_end":
        if state.phase != "after_turn" or state.current_agent_assistant_count < 1:
            raise PiEngineError("Pi emitted agent_end without a fresh completed turn")
        if _last_assistant_sha256(event.get("messages")) != state.last_assistant_sha256:
            raise PiEngineError("Pi agent_end reused a stale assistant result")
        will_retry = event.get("willRetry")
        if not isinstance(will_retry, bool):
            raise PiEngineError("Pi agent_end lacks its retry decision")
        state.phase = "after_agent_retry" if will_retry else "after_agent_final"
        return

    if event_type == "auto_retry_start":
        if state.phase != "after_agent_retry" or state.retry_active:
            raise PiEngineError("Pi emitted auto_retry_start out of order")
        if (
            isinstance(event.get("attempt"), bool)
            or not isinstance(event.get("attempt"), int)
            or event["attempt"] < 1
            or isinstance(event.get("maxAttempts"), bool)
            or not isinstance(event.get("maxAttempts"), int)
            or event["maxAttempts"] < event["attempt"]
        ):
            raise PiEngineError("Pi emitted a malformed retry boundary")
        state.retry_active = True
        state.phase = "expect_retry_agent_start"
        return

    if event_type == "auto_retry_end":
        if (
            not state.retry_active
            or state.phase not in {
                "after_assistant_message",
                "after_turn",
                "after_agent_final",
            }
            or not isinstance(event.get("success"), bool)
        ):
            raise PiEngineError("Pi emitted auto_retry_end out of order")
        state.retry_active = False
        return

    if event_type == "agent_settled":
        if (
            state.phase != "after_agent_final"
            or state.assistant_message_active
            or state.active_tools
            or state.retry_active
            or state.current_agent_assistant_count < 1
        ):
            raise PiEngineError("Pi settled before the current agent run completed")
        state.saw_agent_settled = True
        state.phase = "settled"
        return

    raise PiEngineError(f"Pi event was not consumed by the strict state machine: {event_type}")


def _lease_valid(store: HarnessStore, capability: dict[str, Any]) -> bool:
    try:
        payload = store.get_job(capability["job_id"])
        latest_task = store.get_task(capability["task_id"])["task"]
    except HarnessError:
        return False
    job = payload["job"]
    runtime = payload["runtime"]
    scopes = runtime["scopes"]
    expected_scopes = set(capability["allowed_paths"])
    return bool(
        job["state"] == "running"
        and job["task_id"] == capability["task_id"]
        and job["task_revision"] == capability["task_revision"]
        and latest_task["revision"] == capability["task_revision"]
        and latest_task["status"] == "active"
        and runtime["lease_active"]
        and job["workspace"]["lease_owner"] == capability["lease_owner"]
        and runtime["lease_token"] == capability["lease_token"]
        and len(scopes) == len(expected_scopes)
        and {item["path"] for item in scopes} == expected_scopes
        and all(
            item["active"]
            and item["owner"] == capability["lease_owner"]
            and item["lease_token"] == capability["lease_token"]
            for item in scopes
        )
    )


def _validate_commit_fence_state(
    connection: Any, capability: dict[str, Any]
) -> None:
    """Validate the exact success authority inside one BEGIN IMMEDIATE snapshot."""

    job = connection.execute(
        """
        SELECT job_id, task_id, task_revision, state, lease_owner,
               lease_generation, lease_expires_at
        FROM jobs WHERE job_id = ?
        """,
        (capability["job_id"],),
    ).fetchone()
    latest = connection.execute(
        """
        SELECT task_id, revision, state FROM tasks
        WHERE task_id = ? ORDER BY revision DESC LIMIT 1
        """,
        (capability["task_id"],),
    ).fetchone()
    now = time.time()
    if (
        job is None
        or latest is None
        or job["job_id"] != capability["job_id"]
        or job["task_id"] != capability["task_id"]
        or job["task_revision"] != capability["task_revision"]
        or job["state"] != "running"
        or job["lease_owner"] != capability["lease_owner"]
        or job["lease_generation"] != capability["lease_token"]
        or job["lease_expires_at"] is None
        or float(job["lease_expires_at"]) <= now
        or latest["revision"] != capability["task_revision"]
        or latest["state"] != "active"
    ):
        raise PiEngineError("commit-time Job/Task/lease fence is no longer valid")
    leases = connection.execute(
        """
        SELECT scope, owner, generation, expires_at
        FROM file_leases WHERE job_id = ? ORDER BY scope
        """,
        (capability["job_id"],),
    ).fetchall()
    expected = sorted(capability["allowed_paths"])
    if [row["scope"] for row in leases] != expected or any(
        row["owner"] != capability["lease_owner"]
        or row["generation"] != capability["lease_token"]
        or float(row["expires_at"]) <= now
        for row in leases
    ):
        raise PiEngineError("commit-time file-scope lease fence is no longer exact")


def _terminate_group(process: subprocess.Popen[bytes], force: bool = False) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL if force else signal.SIGTERM)
    except OSError:
        pass


def _cleanup_pi_process(process: subprocess.Popen[bytes]) -> None:
    """Unconditionally terminate the Pi process group and reap its leader."""

    if process.poll() is None:
        _terminate_group(process)
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            _terminate_group(process, force=True)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
    # The leader can exit while a broker or another descendant still holds the
    # process group.  Kill that group as the final containment boundary.
    _terminate_group(process, force=True)
    try:
        process.wait(timeout=1)
    except subprocess.TimeoutExpired as exc:
        raise PiEngineError("Pi process leader could not be killed and reaped") from exc


def _run_pi_process(
    *,
    argv: list[str],
    env: dict[str, str],
    worktree: Path,
    prompt: bytes,
    artifact_dir: Path,
    store: HarnessStore,
    capability: dict[str, Any],
    disk_budget_mb: int,
    token_budget: int,
    artifact_quota: SharedArtifactQuota | None = None,
) -> tuple[int, str, _EventState]:
    try:
        prompt_text = prompt.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise PiEngineError("canonical Pi prompt is not valid UTF-8") from exc
    if not prompt or prompt_text != prompt_text.strip():
        raise PiEngineError("canonical Pi prompt is not stable under Pi stdin trimming")
    if _sha256(prompt) != capability.get("prompt_sha256"):
        raise PiEngineError("canonical Pi prompt does not match the sealed capability")
    backend = capability.get("backend")
    if not isinstance(backend, dict) or not isinstance(backend.get("model"), str):
        raise PiEngineError("Pi capability lacks its pinned backend model")
    session_id = capability.get("session_id")
    if not isinstance(session_id, str) or not session_id:
        raise PiEngineError("Pi capability lacks its fresh session ID")
    raw_path = artifact_dir / "pi-events.jsonl"
    stderr_path = artifact_dir / "pi-stderr.log"
    messages_path = artifact_dir / "messages.jsonl"
    tools_path = artifact_dir / "tool-events.jsonl"
    for path in (raw_path, stderr_path, messages_path, tools_path):
        if path.exists() or path.is_symlink():
            raise PiEngineError(f"fresh Pi artifact already exists: {path.name}")
    quota = artifact_quota or SharedArtifactQuota(
        artifact_dir, disk_budget_mb * 1024 * 1024
    )
    # Pi 0.80.10 JSON mode repeats the cumulative assistant message in every
    # streaming update. A 16k-token proof turn can therefore exceed 256 MiB
    # even though the semantic output remains inside its frozen token budget.
    # Preserve the exact stream while retaining a hard ceiling subordinate to
    # the Job's independently enforced artifact quota.
    output_cap = min(
        PI_STREAM_EVIDENCE_MAX_BYTES,
        max(8 * 1024 * 1024, disk_budget_mb * 1024 * 1024 // 8),
    )
    process: subprocess.Popen[bytes] | None = None
    selector: selectors.BaseSelector | None = None
    event_state = _EventState(
        expected_session_id=session_id,
        expected_prompt_sha256=_sha256(prompt),
        expected_prompt_size_bytes=len(prompt),
        expected_provider=PROVIDER_NAME,
        expected_model=backend["model"],
    )
    stdout_buffer = bytearray()
    prompt_offset = 0
    prompt_last_progress_at = time.monotonic()
    total_output = 0
    exit_reason = "process_exit"
    invalid: str | None = None
    termination_started: float | None = None
    leader_exit_observed_at: float | None = None
    streams_closed_observed_at: float | None = None
    next_lease_check = time.monotonic()

    # Open every append-only evidence target before spawning Pi.  Once Popen
    # succeeds, the outer finally below owns process-group teardown and leader
    # reaping for every subsequent write, parse, selector, and validation error.
    with ExitStack() as stack:
        for relative in (
            "pi-events.jsonl",
            "pi-stderr.log",
            "messages.jsonl",
            "tool-events.jsonl",
        ):
            quota.write_once(relative, b"")
        raw_handle = _QuotaAppender(quota, "pi-events.jsonl")
        stderr_handle = _QuotaAppender(quota, "pi-stderr.log")
        messages_handle = _QuotaAppender(quota, "messages.jsonl")
        tools_handle = _QuotaAppender(quota, "tool-events.jsonl")
        try:
            # Pi leads a dedicated process group, but a process group alone does
            # not survive an abrupt engine death safely.  On Linux the audited
            # pre-exec helper arms PR_SET_PDEATHSIG(SIGKILL) and repeats the
            # exact-parent check after prctl, closing the fork/arm race.  It is
            # a no-op on platforms without Linux prctl.
            expected_engine_pid = os.getpid()
            process = subprocess.Popen(
                argv,
                cwd=worktree,
                env=env,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                shell=False,
                start_new_session=True,
                preexec_fn=_parent_death_preexec(expected_engine_pid),
            )
            if process.stdin is None or process.stdout is None or process.stderr is None:
                raise PiEngineError("Pi subprocess pipes were not created")
            selector = selectors.DefaultSelector()
            selector.register(process.stdout, selectors.EVENT_READ, "stdout")
            selector.register(process.stderr, selectors.EVENT_READ, "stderr")
            # Prompt transport is part of the supervised selector loop.  A
            # malicious or wedged Pi that never drains stdin must not pin the
            # trusted engine before lease/deadline monitoring begins.
            os.set_blocking(process.stdin.fileno(), False)
            selector.register(process.stdin, selectors.EVENT_WRITE, "stdin")

            while selector.get_map() or process.poll() is None:
                now = time.monotonic()
                if process.poll() is not None and leader_exit_observed_at is None:
                    leader_exit_observed_at = now
                    if prompt_offset != len(prompt):
                        invalid = invalid or (
                            "Pi exited before the complete canonical prompt was written"
                        )
                    if process.stdin in (key.fileobj for key in selector.get_map().values()):
                        try:
                            selector.unregister(process.stdin)
                        except KeyError:
                            pass
                        process.stdin.close()
                if (
                    leader_exit_observed_at is not None
                    and selector.get_map()
                    and now - leader_exit_observed_at >= 1
                ):
                    invalid = invalid or (
                        "Pi exited but a descendant retained its event streams"
                    )
                if now >= next_lease_check:
                    next_lease_check = now + 0.5
                    if not _lease_valid(store, capability):
                        invalid = invalid or "live Harness lease or latest Task revision was lost"
                if time.time() >= float(capability["deadline_epoch"]):
                    invalid = invalid or "Task wall-clock budget expired"
                if (
                    prompt_offset != len(prompt)
                    and now - prompt_last_progress_at >= PROMPT_WRITE_TIMEOUT_SECONDS
                ):
                    invalid = invalid or "Pi did not consume the complete canonical prompt before the transport deadline"
                if not selector.get_map() and process.poll() is None:
                    if streams_closed_observed_at is None:
                        streams_closed_observed_at = now
                    elif now - streams_closed_observed_at >= 1:
                        invalid = invalid or "Pi closed its event streams without exiting"
                else:
                    streams_closed_observed_at = None
                if invalid and termination_started is None:
                    exit_reason = invalid
                    termination_started = now
                    _terminate_group(process)
                if termination_started is not None and now - termination_started >= 2:
                    _terminate_group(process, force=True)
                if termination_started is not None and now - termination_started >= 10:
                    raise PiEngineError("Pi process group did not terminate within grace period")

                ready = selector.select(timeout=0.2) if selector.get_map() else ()
                if not selector.get_map() and process.poll() is None:
                    time.sleep(0.01)
                for key, _ in ready:
                    if key.data == "stdin":
                        try:
                            written = os.write(
                                key.fileobj.fileno(),
                                prompt[prompt_offset : prompt_offset + 65536],
                            )
                        except BlockingIOError as exc:
                            if exc.errno in {errno.EAGAIN, errno.EWOULDBLOCK}:
                                continue
                            invalid = invalid or f"Pi prompt transport failed: {exc}"
                            continue
                        except InterruptedError:
                            continue
                        except BrokenPipeError:
                            invalid = invalid or (
                                "Pi closed stdin before the complete canonical prompt was written"
                            )
                            selector.unregister(key.fileobj)
                            key.fileobj.close()
                            continue
                        except OSError as exc:
                            if exc.errno == errno.EINTR:
                                continue
                            if exc.errno in {errno.EAGAIN, errno.EWOULDBLOCK}:
                                continue
                            invalid = invalid or f"Pi prompt transport failed: {exc}"
                            selector.unregister(key.fileobj)
                            key.fileobj.close()
                            continue
                        if written <= 0:
                            invalid = invalid or (
                                "Pi prompt transport made a zero-length write before completion"
                            )
                            selector.unregister(key.fileobj)
                            key.fileobj.close()
                            continue
                        prompt_offset += written
                        prompt_last_progress_at = time.monotonic()
                        if prompt_offset > len(prompt):
                            invalid = invalid or "Pi prompt transport wrote beyond the canonical prompt"
                        if prompt_offset == len(prompt):
                            selector.unregister(key.fileobj)
                            key.fileobj.close()
                        continue
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                        continue
                    total_output += len(chunk)
                    if total_output > output_cap:
                        invalid = invalid or "Pi event/stderr output exceeded the Job evidence cap"
                        continue
                    if key.data == "stderr":
                        _append_line(stderr_handle, chunk)
                        continue
                    _append_line(raw_handle, chunk)
                    stdout_buffer.extend(chunk)
                    while b"\n" in stdout_buffer:
                        raw_line, _, remainder = stdout_buffer.partition(b"\n")
                        stdout_buffer = bytearray(remainder)
                        if not raw_line:
                            invalid = invalid or "Pi JSON stream emitted an empty line"
                            continue
                        line = raw_line + b"\n"
                        try:
                            _consume_event(
                                line,
                                state=event_state,
                                messages_handle=messages_handle,
                                tools_handle=tools_handle,
                                token_budget=token_budget,
                            )
                        except PiEngineError as exc:
                            invalid = invalid or str(exc)
            if stdout_buffer:
                invalid = invalid or "Pi JSON stream ended with a partial line"
            if prompt_offset != len(prompt):
                invalid = invalid or (
                    "Pi did not receive the complete canonical prompt"
                )
            returncode = process.wait(timeout=5)
            if invalid:
                exit_reason = invalid
            return returncode, exit_reason, event_state
        finally:
            try:
                if selector is not None:
                    selector.close()
            finally:
                if process is not None:
                    for pipe in (process.stdin, process.stdout, process.stderr):
                        if pipe is not None and not pipe.closed:
                            try:
                                pipe.close()
                            except Exception:
                                pass
                    _cleanup_pi_process(process)


def _validate_terminal(state: _EventState, returncode: int) -> tuple[bool, str, str]:
    if returncode != 0:
        return False, f"Pi exited with status {returncode}", ""
    if not state.saw_session_header:
        return False, "Pi did not emit a session header", ""
    if not state.saw_agent_settled:
        return False, "Pi did not reach agent_settled", ""
    if state.phase != "settled" or not state.saw_initial_user:
        return False, "Pi did not complete the exact prompt/session event sequence", ""
    if state.assistant_message_active:
        return False, "Pi ended with an unfinished assistant message", ""
    if state.active_tools:
        return False, "Pi ended with unpaired tool calls", ""
    if state.last_assistant is None:
        return False, "Pi emitted no completed assistant message", ""
    stop_reason = state.last_assistant.get("stopReason")
    if stop_reason != "stop":
        error = state.last_assistant.get("errorMessage")
        return False, f"final assistant stopReason={stop_reason!r}: {error or ''}".strip(), _message_text(state.last_assistant)
    return True, "agent_settled with final stopReason=stop", _message_text(state.last_assistant)


def _replay_git(
    worktree: Path,
    index_path: Path,
    arguments: tuple[str, ...],
    *,
    stdin: bytes | None = None,
    output_limit: int = 64 * 1024 * 1024,
) -> bytes:
    env = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "LANG": "C.UTF-8",
        "LC_ALL": "C",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_PAGER": "cat",
        "PAGER": "cat",
        "GIT_EXTERNAL_DIFF": "",
        "GIT_INDEX_FILE": str(index_path),
    }
    result = run_limited(
        (
            "git",
            "-c",
            "core.fsmonitor=false",
            "-c",
            f"core.hooksPath={os.devnull}",
            "-c",
            "diff.external=",
            *arguments,
        ),
        cwd=worktree,
        env=env,
        timeout_seconds=30,
        output_limit_bytes=output_limit,
        stdin=stdin,
        supervise_parent=True,
    )
    if (
        result.returncode != 0
        or result.timed_out
        or result.output_limited
        or result.guard_cancelled
    ):
        detail = result.stderr.decode("utf-8", "replace").strip()
        raise PiEngineError(
            f"isolated patch-journal replay failed: {detail or result.returncode}"
        )
    return result.stdout


def _replay_index_hashes(
    worktree: Path, index_path: Path, paths: tuple[str, ...]
) -> dict[str, str]:
    hashes: dict[str, str] = {}
    for relative in paths:
        data = _replay_git(
            worktree,
            index_path,
            ("show", "--no-ext-diff", "--no-textconv", "--format=", f":{relative}"),
            output_limit=128 * 1024 * 1024,
        )
        hashes[relative] = _sha256(data)
    return hashes


def _replay_patch_journal(
    *,
    artifact_dir: Path,
    job_id: str,
    session_id: str,
    worktree: Path,
    patch_limit: int,
) -> tuple[bytes, tuple[CommittedPatch, ...]]:
    committed = verify_patch_journal(artifact_dir, job_id, session_id)
    with tempfile.TemporaryDirectory(prefix="poincare-pi-index-") as temporary:
        index_path = Path(temporary) / "index"
        _replay_git(worktree, index_path, ("read-tree", "HEAD"))

        def apply_one(patch: CommittedPatch) -> ReplayObservation:
            before = _replay_index_hashes(worktree, index_path, patch.paths)
            _replay_git(
                worktree,
                index_path,
                ("apply", "--cached", "--whitespace=error-all", "-"),
                stdin=patch.patch,
                output_limit=256 * 1024,
            )
            after = _replay_index_hashes(worktree, index_path, patch.paths)
            return ReplayObservation(before_sha256=before, after_sha256=after)

        replayed = replay_committed_patches(committed, apply_one)
        replay_patch = _replay_git(
            worktree,
            index_path,
            (
                "diff",
                "--cached",
                "--binary",
                "--no-ext-diff",
                "--no-textconv",
                "--no-color",
                "HEAD",
                "--",
            ),
            output_limit=patch_limit,
        )
    return replay_patch, replayed


def _jsonl_objects(path: Path, label: str, maximum: int = 64 * 1024 * 1024) -> list[dict[str, Any]]:
    if path.is_symlink() or not path.is_file() or path.stat().st_size > maximum:
        raise PiEngineError(f"{label} is not a bounded regular JSONL file")
    objects: list[dict[str, Any]] = []
    try:
        raw = path.read_bytes()
        if raw and not raw.endswith(b"\n"):
            raise PiEngineError(f"{label} is truncated")
        for line in raw.splitlines():
            value = json.loads(line.decode("utf-8"))
            if not isinstance(value, dict):
                raise PiEngineError(f"{label} contains a non-object record")
            objects.append(value)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PiEngineError(f"{label} is invalid: {exc}") from exc
    return objects


def _crosscheck_tool_evidence(
    *,
    artifact_dir: Path,
    committed: tuple[CommittedPatch, ...],
) -> dict[str, Any]:
    pi_events = _jsonl_objects(artifact_dir / "tool-events.jsonl", "Pi tool event log")
    broker_events = _jsonl_objects(
        artifact_dir / "pi-broker-events.jsonl", "broker/RPC event log"
    )
    starts = [
        (event.get("toolCallId"), event.get("toolName"))
        for event in pi_events
        if event.get("type") == "tool_execution_start"
    ]
    ends = [
        (event.get("toolCallId"), event.get("toolName"))
        for event in pi_events
        if event.get("type") == "tool_execution_end"
    ]
    if starts != ends or any(
        not isinstance(call_id, str) or tool not in TOOL_NAMES
        for call_id, tool in starts
    ):
        raise PiEngineError("Pi tool start/end evidence is incomplete or inconsistent")
    terminals = [
        event
        for event in broker_events
        if event.get("event") in {"pi_tool_result", "pi_tool_error"}
    ]
    broker_calls = [
        (event.get("tool_call_id"), event.get("tool_name")) for event in terminals
    ]
    if broker_calls != starts:
        raise PiEngineError("Pi tool events disagree with serialized broker execution")
    if [event.get("sequence") for event in terminals] != list(
        range(1, len(terminals) + 1)
    ):
        raise PiEngineError("serialized broker sequence evidence is incomplete")
    if any(event.get("event") == "rpc_transport_rejected" for event in broker_events):
        raise PiEngineError("broker recorded rejected or unauthenticated transport")
    rpc_received = [
        event for event in broker_events if event.get("event") == "rpc_request_received"
    ]
    rpc_terminal = [
        event for event in broker_events if event.get("event") == "rpc_request_terminal"
    ]
    received_calls = [
        (event.get("tool_call_id"), event.get("tool_name")) for event in rpc_received
    ]
    terminal_calls = [
        (event.get("tool_call_id"), event.get("tool_name")) for event in rpc_terminal
    ]
    if received_calls != starts or terminal_calls != starts:
        raise PiEngineError("authenticated RPC evidence disagrees with Pi tool events")
    if [event.get("sequence") for event in rpc_received] != list(
        range(1, len(starts) + 1)
    ) or [event.get("sequence") for event in rpc_terminal] != list(
        range(1, len(starts) + 1)
    ):
        raise PiEngineError("authenticated RPC sequence evidence is incomplete")
    if any(event.get("response_sent") is not True for event in rpc_terminal):
        raise PiEngineError("an authenticated RPC has no proved terminal response")
    if [event.get("ok") for event in rpc_terminal] != [
        event.get("event") == "pi_tool_result" for event in terminals
    ]:
        raise PiEngineError("RPC terminal status disagrees with broker tool status")
    committed_by_call = {patch.tool_call_id: patch for patch in committed}
    successful_apply_events = [
        event
        for event in terminals
        if event.get("event") == "pi_tool_result"
        and event.get("tool_name") == "apply_patch_scoped"
    ]
    if {event.get("tool_call_id") for event in successful_apply_events} != set(
        committed_by_call
    ):
        raise PiEngineError("successful patch RPCs disagree with committed patch journal")
    for event in successful_apply_events:
        patch = committed_by_call[str(event["tool_call_id"])]
        details = event.get("details")
        if (
            not isinstance(details, dict)
            or details.get("patch_sha256") != patch.patch_sha256
            or details.get("journal_intent_sequence") != patch.intent_sequence
        ):
            raise PiEngineError("broker patch result disagrees with patch journal")
    return {
        "schema_version": "poincare.pi-tool-crosscheck.v1",
        "tool_calls": len(starts),
        "committed_patches": len(committed),
        "tool_call_ids": [call_id for call_id, _tool in starts],
        "valid": True,
    }


def _read_blocked_report(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    if path.is_symlink() or not path.is_file() or path.stat().st_size > 256 * 1024:
        raise PiEngineError("Pi blocked report is not a bounded regular file")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PiEngineError(f"Pi blocked report is invalid JSON: {exc}") from exc
    required = {
        "schema_version",
        "reported_at",
        "summary",
        "exact_lean_type_or_error",
        "attempted_routes",
        "strongest_partial_result",
    }
    if (
        not isinstance(value, dict)
        or set(value) != required
        or value.get("schema_version") != "poincare.pi-blocked.v1"
        or not all(
            isinstance(value.get(key), str) and bool(value[key].strip())
            for key in (
                "reported_at",
                "summary",
                "exact_lean_type_or_error",
                "strongest_partial_result",
            )
        )
        or not isinstance(value.get("attempted_routes"), list)
        or not value["attempted_routes"]
        or not all(
            isinstance(item, str) and bool(item.strip())
            for item in value["attempted_routes"]
        )
    ):
        raise PiEngineError("Pi blocked report does not match its canonical schema")
    return value


def _decode_nul_paths(raw: bytes, label: str) -> tuple[str, ...]:
    if not raw:
        return ()
    if not raw.endswith(b"\0"):
        raise PiEngineError(f"{label} is not NUL terminated")
    paths: list[str] = []
    for encoded in raw[:-1].split(b"\0"):
        try:
            path = encoded.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise PiEngineError(f"{label} contains a non-UTF-8 path") from exc
        if not path or "\x00" in path:
            raise PiEngineError(f"{label} contains an empty or invalid path")
        paths.append(path)
    if len(set(paths)) != len(paths):
        raise PiEngineError(f"{label} repeats a path")
    return tuple(paths)


def _parse_clean_tracked_status(
    raw: bytes, *, task: dict[str, Any]
) -> tuple[str, ...]:
    """Accept only unstaged content modifications of tracked in-scope files."""

    if not raw:
        return ()
    if not raw.endswith(b"\0"):
        raise PiEngineError("Git status evidence is not NUL terminated")
    paths: list[str] = []
    for entry in raw[:-1].split(b"\0"):
        if len(entry) < 4 or entry[2:3] != b" ":
            raise PiEngineError("Git status evidence has an invalid porcelain entry")
        status = entry[:2]
        if status != b" M":
            raise PiEngineError(
                "final diff contains staged, untracked, deleted, renamed, copied, conflicted, or unsupported changes"
            )
        try:
            path = entry[3:].decode("utf-8")
        except UnicodeDecodeError as exc:
            raise PiEngineError("Git status contains a non-UTF-8 path") from exc
        if not path_is_allowed(
            path,
            task["scope"]["allowed_paths"],
            task["scope"]["forbidden_paths"],
        ):
            raise PiEngineError(f"final diff path is outside Task scope: {path}")
        paths.append(path)
    if len(set(paths)) != len(paths):
        raise PiEngineError("Git status repeats a changed path")
    return tuple(paths)


def _capture_final_diff(
    *,
    store: HarnessStore,
    capability: dict[str, Any],
    task: dict[str, Any],
    worktree: Path,
    patch_limit: int,
    live_guard: Callable[[], bool] | None = None,
) -> tuple[bytes, dict[str, Any]]:
    """Capture and validate one exact HEAD-relative worktree snapshot."""

    guard = live_guard or (lambda: _lease_valid(store, capability))
    head_before = _git(worktree, "rev-parse", "HEAD", guard=guard).decode().strip()
    branch = _git(
        worktree,
        "symbolic-ref",
        "--quiet",
        "--short",
        "HEAD",
        guard=guard,
    ).decode().strip()
    status = _git(
        worktree,
        "status",
        "--porcelain=v1",
        "-z",
        "--untracked-files=all",
        "--ignored=no",
        guard=guard,
        limit=min(patch_limit, 8 * 1024 * 1024),
    )
    names_raw = _git(
        worktree,
        "diff",
        "--no-ext-diff",
        "--no-textconv",
        "--name-only",
        "-z",
        "HEAD",
        "--",
        guard=guard,
        limit=min(patch_limit, 8 * 1024 * 1024),
    )
    patch = _git(
        worktree,
        "diff",
        "--binary",
        "--no-ext-diff",
        "--no-textconv",
        "--no-color",
        "HEAD",
        "--",
        guard=guard,
        limit=patch_limit,
    )
    audit = {
        "schema_version": "poincare.pi-final-diff-audit.v1",
        "captured_at": _utc_now(),
        "valid": False,
        "base_commit": capability["base_commit"],
        "head": head_before,
        "branch": branch,
        "status_porcelain_v1_z_hex": status.hex(),
        "diff_name_only_z_hex": names_raw.hex(),
        "changed_paths": [],
        "patch_sha256": _sha256(patch),
        "patch_size_bytes": len(patch),
        "rejected_change_classes": [
            "staged",
            "untracked",
            "deleted",
            "renamed",
            "copied",
            "mode-only",
            "binary",
            "out-of-scope",
            "forbidden-added-token",
        ],
    }
    try:
        diff_check = _git(
            worktree,
            "diff",
            "--no-ext-diff",
            "--no-textconv",
            "--check",
            "HEAD",
            "--",
            guard=guard,
            limit=min(patch_limit, 8 * 1024 * 1024),
        )
        head_after = _git(worktree, "rev-parse", "HEAD", guard=guard).decode().strip()
        status_after = _git(
            worktree,
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--ignored=no",
            guard=guard,
            limit=min(patch_limit, 8 * 1024 * 1024),
        )
        if (
            head_before != capability["base_commit"]
            or head_after != head_before
            or branch != capability["branch"]
            or status_after != status
        ):
            raise PiEngineError(
                "worktree HEAD, branch, or status changed during final diff capture"
            )

        status_paths = _parse_clean_tracked_status(status, task=task)
        name_paths = _decode_nul_paths(names_raw, "Git diff name list")
        audit["changed_paths"] = list(name_paths)
        for path in name_paths:
            if not path_is_allowed(
                path,
                task["scope"]["allowed_paths"],
                task["scope"]["forbidden_paths"],
            ):
                raise PiEngineError(f"final diff path is outside Task scope: {path}")
        if set(status_paths) != set(name_paths):
            raise PiEngineError("Git status and HEAD diff disagree on changed paths")

        if patch:
            try:
                patch_text = patch.decode("utf-8")
            except UnicodeDecodeError as exc:
                raise PiEngineError("final patch is not UTF-8 text") from exc
            try:
                touched = validate_patch(
                    patch_text,
                    root=worktree,
                    allowed=task["scope"]["allowed_paths"],
                    forbidden=task["scope"]["forbidden_paths"],
                    forbidden_tokens=task["acceptance"]["forbidden_added_tokens"],
                    max_bytes=patch_limit,
                )
            except SecurityError as exc:
                raise PiEngineError(f"final patch audit rejected the diff: {exc}") from exc
            if set(touched) != set(name_paths):
                raise PiEngineError("validated patch headers disagree with changed paths")
        elif status_paths or name_paths:
            raise PiEngineError("Git reports changes but the exact HEAD patch is empty")
        if diff_check:
            raise PiEngineError("git diff --check unexpectedly emitted output")
        audit["head"] = head_after
        audit["diff_check_output_sha256"] = _sha256(diff_check)
        audit["valid"] = True
    except (BrokerError, PiEngineError, SecurityError, UnicodeError, OSError) as exc:
        audit["error"] = str(exc)
        raise _FinalDiffAuditError(str(exc), patch=patch, audit=audit) from exc
    return patch, audit


def _failed_diff_audit(reason: str) -> dict[str, Any]:
    return {
        "schema_version": "poincare.pi-final-diff-audit.v1",
        "captured_at": _utc_now(),
        "valid": False,
        "error": reason,
    }


def _hash_evidence(path: Path, artifact_dir: Path) -> dict[str, Any]:
    lexical = path.absolute()
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise PiEngineError(f"required Pi evidence is missing: {path.name}") from exc
    try:
        relative = resolved.relative_to(artifact_dir).as_posix()
    except ValueError as exc:
        raise PiEngineError(f"Pi evidence escaped its Job artifact directory: {path}") from exc
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(lexical, flags)
    except OSError as exc:
        raise PiEngineError(f"cannot safely open Pi evidence: {path.name}: {exc}") from exc
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode) or opened.st_nlink != 1:
            raise PiEngineError(f"Pi evidence is not a regular file: {path.name}")
        digest = hashlib.sha256()
        while chunk := os.read(descriptor, 1024 * 1024):
            digest.update(chunk)
        after_read = os.fstat(descriptor)
        lexical_stat = os.lstat(lexical)
        if stat.S_ISLNK(lexical_stat.st_mode) or (
            opened.st_dev,
            opened.st_ino,
            opened.st_size,
            opened.st_mtime_ns,
        ) != (
            lexical_stat.st_dev,
            lexical_stat.st_ino,
            lexical_stat.st_size,
            lexical_stat.st_mtime_ns,
        ) or (
            opened.st_size,
            opened.st_mtime_ns,
        ) != (
            after_read.st_size,
            after_read.st_mtime_ns,
        ):
            raise PiEngineError(f"Pi evidence changed while hashing: {path.name}")
    finally:
        os.close(descriptor)
    return {
        "path": relative,
        "sha256": digest.hexdigest(),
        "size_bytes": opened.st_size,
    }


def _seal_evidence(paths: list[Path]) -> None:
    for path in paths:
        if path.exists() and path.is_file() and not path.is_symlink():
            try:
                path.chmod(0o400)
            except OSError as exc:
                raise PiEngineError(f"cannot seal evidence read-only: {path.name}: {exc}") from exc


def _configured_integer(
    name: str, default: int, *, minimum: int, maximum: int
) -> int:
    raw = os.environ.get(name, str(default))
    if re.fullmatch(r"[0-9]+", raw) is None:
        raise PiEngineError(f"{name} must be an unsigned base-10 integer")
    try:
        value = int(raw, 10)
    except (TypeError, ValueError) as exc:
        raise PiEngineError(f"{name} must be a decimal integer") from exc
    if not minimum <= value <= maximum:
        raise PiEngineError(f"{name} is outside its safe bound")
    return value


def _configured_number(
    name: str, default: float, *, minimum: float, maximum: float
) -> float:
    raw = os.environ.get(name, str(default))
    if re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", raw) is None:
        raise PiEngineError(f"{name} must be an unsigned decimal number")
    try:
        value = float(raw)
    except (TypeError, ValueError) as exc:
        raise PiEngineError(f"{name} must be numeric") from exc
    if not math.isfinite(value) or not minimum <= value <= maximum:
        raise PiEngineError(f"{name} is outside its safe bound")
    return value


def _required_executable_environment(name: str) -> str:
    raw = os.environ.get(name, "").strip()
    if not raw:
        raise PiEngineError(f"{name} is required")
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink():
        raise PiEngineError(f"{name} must not name a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise PiEngineError(f"cannot resolve {name}: {exc}") from exc
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise PiEngineError(f"{name} must name an executable regular file")
    return str(resolved)


def _sparse_lean_configuration(
    *,
    worktree: Path,
    state_dir: Path,
    artifact_dir: Path,
    control_root: Path,
    git_common: Path,
    lean_scratch_root: Path,
    immutable_lake_cache: Path,
    base_commit: str,
    base_tree: str,
    lean_timeout_seconds: int,
) -> dict[str, Any]:
    memory_max = _configured_integer(
        "HARNESS_PI_LEAN_MEMORY_MAX_BYTES",
        8 * 1024 * 1024 * 1024,
        minimum=256 * 1024 * 1024,
        maximum=1 << 50,
    )
    return {
        "bwrap_path": _required_executable_environment("HARNESS_PI_BWRAP"),
        "systemd_run_path": _required_executable_environment(
            "HARNESS_PI_SYSTEMD_RUN"
        ),
        "git_path": _required_executable_environment("HARNESS_PI_GIT"),
        "immutable_lake_cache": str(immutable_lake_cache),
        "toolchain_roots": os.environ.get("HARNESS_PI_TOOLCHAIN_ROOTS"),
        "base_commit": base_commit,
        "base_tree": base_tree,
        "forbidden_host_paths": sorted(
            {
                str(worktree),
                str(state_dir),
                str(artifact_dir),
                str(control_root),
                str(git_common),
            }
        ),
        "memory_max_bytes": memory_max,
        "tasks_max": _configured_integer(
            "HARNESS_PI_LEAN_TASKS_MAX", 256, minimum=1, maximum=65536
        ),
        "cpu_quota_percent": _configured_number(
            "HARNESS_PI_LEAN_CPU_QUOTA_PERCENT",
            100.0,
            minimum=1.0,
            maximum=10000.0,
        ),
        "process_limits": {
            "address_space_bytes": _configured_integer(
                "HARNESS_PI_LEAN_RLIMIT_AS_BYTES",
                min(1 << 50, max(memory_max, 12 * 1024 * 1024 * 1024)),
                minimum=256 * 1024 * 1024,
                maximum=1 << 50,
            ),
            "processes": _configured_integer(
                "HARNESS_PI_LEAN_RLIMIT_NPROC", 256, minimum=1, maximum=65536
            ),
            "open_files": _configured_integer(
                "HARNESS_PI_LEAN_RLIMIT_NOFILE", 1024, minimum=16, maximum=1 << 20
            ),
            "file_size_bytes": _configured_integer(
                "HARNESS_PI_LEAN_RLIMIT_FSIZE_BYTES",
                512 * 1024 * 1024,
                minimum=1024 * 1024,
                maximum=1 << 50,
            ),
            "core_bytes": _configured_integer(
                "HARNESS_PI_LEAN_RLIMIT_CORE_BYTES",
                0,
                minimum=0,
                maximum=1 << 40,
            ),
            "cpu_seconds": _configured_integer(
                "HARNESS_PI_LEAN_RLIMIT_CPU_SECONDS",
                max(900, lean_timeout_seconds + 30),
                minimum=1,
                maximum=86400,
            ),
        },
    }


def _preflight_sparse_lean(
    *,
    state_dir: Path,
    worktree: Path,
    lean_scratch_root: Path,
    commands: list[list[str]],
    config: dict[str, Any],
    sandbox_auditor: Callable[..., dict[str, Any]],
) -> dict[str, Any]:
    preflight_dir = lean_scratch_root / "preflight"
    preflight_dir.mkdir(mode=0o700)
    snapshot: dict[str, Any] | None = None
    record: dict[str, Any] | None = None
    try:
        with acquire_build_job_lock(state_dir, timeout_seconds=5):
            try:
                snapshot = build_sparse_lean_snapshot(
                    worktree=worktree,
                    acceptance_commands=commands,
                    output_dir=preflight_dir / "source",
                    git_path=config["git_path"],
                )
                sandbox = sandbox_auditor(
                    configured_path=config["bwrap_path"],
                    systemd_run_path=config["systemd_run_path"],
                    sparse_snapshot=snapshot,
                    immutable_lake_cache=config["immutable_lake_cache"],
                    extra_toolchain_roots=config["toolchain_roots"],
                    forbidden_paths=[Path(item) for item in config["forbidden_host_paths"]],
                    base_commit=config["base_commit"],
                    base_tree=config["base_tree"],
                    memory_max_bytes=config["memory_max_bytes"],
                    tasks_max=config["tasks_max"],
                    cpu_quota_percent=config["cpu_quota_percent"],
                    process_limits=config["process_limits"],
                )
                audited_argv_sha256: list[str] = []
                for command in commands:
                    argv = bubblewrap_sparse_lean_argv(spec=sandbox, command=command)
                    audited_argv_sha256.append(
                        _sha256(canonical_json_bytes(list(argv)))
                    )
                record = {
                    "schema_version": "poincare.pi-sparse-lean-preflight.v1",
                    "checked_at": _utc_now(),
                    "snapshot_tree_sha256": snapshot["tree_sha256"],
                    "targets": snapshot["targets"],
                    "profile_version": sandbox["profile_version"],
                    "lake_cache_tree_sha256": sandbox["lake_cache"]["tree_sha256"],
                    "toolchain": sandbox["toolchain"],
                    "resources": sandbox["resources"],
                    "audited_argv_sha256": audited_argv_sha256,
                }
            finally:
                if snapshot is not None:
                    remove_sparse_lean_snapshot(
                        sparse_snapshot=snapshot, checks_root=lean_scratch_root
                    )
                preflight_dir.rmdir()
    except (SecurityError, OSError, ValueError) as exc:
        raise PiEngineError(f"sparse Lean sandbox preflight failed: {exc}") from exc
    if record is None:
        raise PiEngineError("sparse Lean sandbox preflight produced no evidence")
    return record


def _minimal_quota_failure_result(
    *,
    artifact_quota: SharedArtifactQuota,
    artifact_dir: Path,
    job_id: str,
    reason: str,
    process_returncode: int,
) -> PiRunResult:
    """Use only the reserved terminal budget after all untrusted work is reaped."""

    bounded = reason.replace("\x00", " ").replace("\r", " ").replace("\n", " ")[:2048]
    report = (
        "# Pi Job failed closed\n\n"
        "The shared artifact quota was exhausted. The Pi process and broker "
        "capabilities were closed before this minimal terminal record was written.\n\n"
        f"Reason: {bounded or 'artifact quota exhausted'}\n"
    ).encode("utf-8")
    final_artifact = artifact_quota.write_once(
        "final-report.md", report, emergency=True
    )
    manifest = {
        "schema_version": "poincare.pi-evidence-manifest.v1",
        "job_id": job_id,
        "recorded_at": _utc_now(),
        "complete": False,
        "quota_failure": True,
        "files": [
            {
                "logical_name": "final_report",
                "path": final_artifact.relative_path,
                "sha256": final_artifact.sha256,
                "size_bytes": final_artifact.size_bytes,
            }
        ],
    }
    manifest_artifact = artifact_quota.write_once(
        "evidence-manifest.json", canonical_json_bytes(manifest), emergency=True
    )
    result = {
        "schema_version": "poincare.pi-result.v1",
        "job_id": job_id,
        "recorded_at": _utc_now(),
        "success": False,
        "exit_reason": f"artifact quota exhausted: {bounded}",
        "process_returncode": process_returncode,
        "events": 0,
        "messages": 0,
        "tool_events": 0,
        "output_tokens": 0,
        "agent_settled": False,
        "final_report": final_artifact.relative_path,
        "final_report_sha256": final_artifact.sha256,
        "evidence_manifest": manifest_artifact.relative_path,
        "evidence_manifest_sha256": manifest_artifact.sha256,
        "quota_failure": True,
        "authority_note": "evidence only; Codex must independently gate and transition the Job/Task",
    }
    result_artifact = artifact_quota.write_once(
        "pi-run-result.json", canonical_json_bytes(result), emergency=True
    )
    _seal_evidence(
        [
            artifact_dir / final_artifact.relative_path,
            artifact_dir / manifest_artifact.relative_path,
            artifact_dir / result_artifact.relative_path,
        ]
    )
    return PiRunResult(
        job_id=job_id,
        success=False,
        exit_reason=result["exit_reason"],
        process_returncode=process_returncode,
        events=0,
        messages=0,
        tool_events=0,
        output_tokens=0,
        session_artifact=None,
        final_report_artifact=final_artifact.relative_path,
        patch_artifact="",
        result_artifact=result_artifact.relative_path,
    )


def run_job(
    *,
    job_id: str,
    lease_owner: str,
    lease_token: int,
    state_dir: Path | str,
    control_root: Path | str,
    pi_install_manifest: Path | str | None = None,
    pi_dependency_graph: Path | str | None = None,
    pi_bin: str | None = None,
    extension_path: Path | str | None = None,
    lean_timeout_seconds: int = 900,
    health_checker: Callable[..., Any] = check_health,
    integrity_attestor: Callable[[Path], dict[str, Any]] = attest_trusted_code,
    sandbox_auditor: Callable[..., dict[str, Any]] = audit_sparse_lean_bubblewrap,
    install_verifier: Callable[..., tuple[dict[str, Any], bytes, str, Path, Path]] = _verify_sealed_pi_install,
) -> PiRunResult:
    if not lease_owner.strip() or lease_token < 1:
        raise PiEngineError("lease owner and positive fencing token are required")
    control = _resolved_directory(control_root, "control repository")
    state = _resolved_directory(state_dir, "Harness state directory")
    store = HarnessStore(state)
    task, job, _runtime, worktree, artifact_dir = _validate_records(
        store=store,
        job_id=job_id,
        lease_owner=lease_owner,
        lease_token=lease_token,
        control_root=control,
    )
    artifact_quota = SharedArtifactQuota(
        artifact_dir, task["budget"]["disk_mb"] * 1024 * 1024
    )
    max_tokens, temperature = _validated_sampling(task, job)
    try:
        trusted_code = integrity_attestor(control)
    except (IntegrityError, OSError, ValueError) as exc:
        raise PiEngineError(f"trusted control checkout audit failed: {exc}") from exc

    if pi_bin is not None:
        raise PiEngineError(
            "arbitrary --pi-bin/version-only execution is forbidden; supply a sealed full install manifest"
        )
    if extension_path is not None:
        raise PiEngineError("arbitrary Pi extension overrides are forbidden")
    manifest_source = pi_install_manifest or os.environ.get(
        "HARNESS_PI_INSTALL_MANIFEST", ""
    )
    graph_source = pi_dependency_graph or os.environ.get(
        "HARNESS_PI_DEPENDENCY_GRAPH", ""
    )
    if not manifest_source or not graph_source:
        raise PiEngineError(
            "a sealed Pi install manifest and dependency graph are required"
        )
    try:
        (
            pi_install,
            pi_dependency_graph_bytes,
            pi_install_manifest_sha256,
            pi_install_manifest_path,
            pi_dependency_graph_path,
        ) = install_verifier(
            manifest_path=manifest_source,
            dependency_graph_path=graph_source,
        )
    except (PiEngineError, PiInstallError, OSError, ValueError) as exc:
        raise PiEngineError(f"Pi install verification failed: {exc}") from exc

    try:
        snapshot = build_snapshot(task, worktree)
    except SnapshotError as exc:
        raise PiEngineError(str(exc)) from exc
    _write_snapshot(
        snapshot=snapshot,
        job=job,
        artifact_store=artifact_quota,
    )

    canonical_extension = (control / "harness/v2/pi/extension.ts").resolve(strict=True)
    extension = canonical_extension
    if extension.is_symlink() or not extension.is_file():
        raise PiEngineError("Pi extension must be a regular non-symlink file")
    if extension.resolve(strict=True) != canonical_extension:
        raise PiEngineError("Pi extension must be the canonical control checkout extension.ts")
    extension_sha256 = _sha256_file(extension)
    version = pi_install["package"]["version"]

    git_common_raw = _git(worktree, "rev-parse", "--git-common-dir").decode().strip()
    base_tree = _git(worktree, "rev-parse", "HEAD^{tree}").decode().strip()
    if re.fullmatch(r"[0-9a-f]{40}", base_tree) is None:
        raise PiEngineError("Job base tree is not a full Git tree ID")
    git_common = Path(git_common_raw)
    if not git_common.is_absolute():
        git_common = worktree / git_common
    try:
        git_common = git_common.resolve(strict=True)
    except OSError as exc:
        raise PiEngineError(f"cannot resolve Job Git common directory: {exc}") from exc
    cache_root_raw = os.environ.get("HARNESS_PI_LAKE_CACHE_ROOT", "").strip()
    if not cache_root_raw:
        raise PiEngineError("HARNESS_PI_LAKE_CACHE_ROOT is required")
    immutable_lake_cache = (
        Path(cache_root_raw).expanduser().absolute() / job["workspace"]["base_commit"]
    )
    execution_temp = tempfile.TemporaryDirectory(prefix="poincare-pi-execution-")
    execution_root = Path(execution_temp.name).resolve(strict=True)
    lean_scratch_root = execution_root / "lean-checks"
    broker_root = execution_root / "broker"
    sealed_root = execution_root / "sealed"
    for private in (lean_scratch_root, broker_root, sealed_root):
        private.mkdir(mode=0o700)
    sparse_lean = _sparse_lean_configuration(
        worktree=worktree,
        state_dir=state,
        artifact_dir=artifact_dir,
        control_root=control,
        git_common=git_common,
        lean_scratch_root=lean_scratch_root,
        immutable_lake_cache=immutable_lake_cache,
        base_commit=job["workspace"]["base_commit"],
        base_tree=base_tree,
        lean_timeout_seconds=lean_timeout_seconds,
    )
    lean_preflight_commands = _sparse_lean_acceptance_commands(task)
    if not lean_preflight_commands:
        execution_temp.cleanup()
        raise PiEngineError("Pi Task has no sparse-auditable Lean acceptance command")
    sparse_preflight = _preflight_sparse_lean(
        state_dir=state,
        worktree=worktree,
        lean_scratch_root=lean_scratch_root,
        commands=lean_preflight_commands,
        config=sparse_lean,
        sandbox_auditor=sandbox_auditor,
    )

    health_config = LeanstralConfig(
        base_url=job["backend"]["endpoint"],
        model=job["backend"]["model"],
        model_revision=job["backend"]["model_revision"],
        api_key=None,
        timeout_seconds=min(30.0, task["budget"]["wall_clock_minutes"] * 60.0),
        max_tokens=max_tokens,
        reasoning_effort=None,
        temperature=temperature,
    )
    try:
        health_result = _call_health_checker(
            health_checker, health_config, artifact_dir
        )
    except Exception as exc:
        execution_temp.cleanup()
        raise PiEngineError(f"Leanstral health/identity check failed: {exc}") from exc

    artifact_store = artifact_quota
    health_record = {
        "schema_version": "poincare.pi-health-check.v1",
        "checked_at": _utc_now(),
        "endpoint": _normalize_endpoint(job["backend"]["endpoint"]),
        "model": job["backend"]["model"],
        "model_revision": job["backend"]["model_revision"],
        "sampling": {"max_tokens": max_tokens, "temperature": temperature},
        "status_code": getattr(health_result, "status_code", None),
        "served_model_ids": list(getattr(health_result, "served_model_ids", ())),
    }
    health_artifact = artifact_store.write_once(
        "health-check.json", canonical_json_bytes(health_record)
    )
    trusted_code_artifact = artifact_store.write_once(
        "trusted-code-manifest.json", canonical_json_bytes(trusted_code)
    )
    pi_install_artifact = artifact_store.write_once(
        "pi-install-manifest.json", canonical_install_manifest_bytes(pi_install)
    )
    sparse_preflight_artifact = artifact_store.write_once(
        "sparse-lean-preflight.json", canonical_json_bytes(sparse_preflight)
    )
    system_prompt_bytes = (SYSTEM_PROMPT + "\n").encode("utf-8")
    system_prompt_artifact = artifact_store.write_once(
        "system-prompt.md", system_prompt_bytes
    )
    system_prompt_path = artifact_dir / system_prompt_artifact.relative_path
    private_settings_bytes = PI_PRIVATE_SETTINGS_BYTES
    private_settings_artifact = artifact_store.write_once(
        "pi-settings.json", private_settings_bytes
    )
    launched_at = time.time()
    session_id = str(uuid.uuid4())
    capability = _build_capability(
        task=task,
        job=job,
        state_dir=state,
        control_root=control,
        artifact_dir=artifact_dir,
        worktree=worktree,
        lease_owner=lease_owner,
        lease_token=lease_token,
        extension_sha256=extension_sha256,
        system_prompt_sha256=system_prompt_artifact.sha256,
        session_id=session_id,
        launched_at=launched_at,
        lean_timeout_seconds=lean_timeout_seconds,
        artifact_quota_bytes=task["budget"]["disk_mb"] * 1024 * 1024,
        trusted_code=trusted_code,
        lean_scratch_root=lean_scratch_root,
        sparse_lean=sparse_lean,
    )
    capability_artifact = artifact_store.write_once(
        "pi-capability.json", canonical_json_bytes(capability)
    )
    capability_path = artifact_dir / capability_artifact.relative_path
    _validate_live(capability)

    public_config = _public_pi_config(
        job=job,
        session_id=session_id,
        extension_sha256=extension_sha256,
        output_token_budget=task["budget"]["max_output_tokens"],
        system_prompt_sha256=system_prompt_artifact.sha256,
        prompt_sha256=snapshot.prompt_sha256,
        prompt_size_bytes=len(snapshot.prompt.encode("utf-8")),
        settings_sha256=private_settings_artifact.sha256,
    )
    public_config_bytes = canonical_json_bytes(public_config)
    public_config_artifact = artifact_store.write_once(
        "pi-public-config.json", public_config_bytes
    )
    extension_bytes = extension.read_bytes()
    if _sha256(extension_bytes) != extension_sha256:
        execution_temp.cleanup()
        raise PiEngineError("canonical Pi extension changed before sealing")
    sealed_extension = _write_sealed_input(
        sealed_root, "extension.ts", extension_bytes
    )
    sealed_public_config = _write_sealed_input(
        sealed_root, "public-config.json", public_config_bytes
    )
    sealed_system_prompt = _write_sealed_input(
        sealed_root, "system-prompt.md", system_prompt_bytes
    )
    sealed_settings = _write_sealed_input(
        sealed_root, "settings.json", private_settings_bytes
    )
    artifact_store.write_once("pi-broker-events.jsonl", b"")

    pi_arguments = [
        "--mode",
        "json",
        "--provider",
        PROVIDER_NAME,
        "--model",
        job["backend"]["model"],
        "--session-id",
        session_id,
        "--session-dir",
        "/runtime/sessions",
        "--name",
        job_id,
        "--no-builtin-tools",
        "--tools",
        ",".join(TOOL_NAMES),
        "--extension",
        "/sealed/extension.ts",
        "--no-extensions",
        "--no-skills",
        "--no-prompt-templates",
        "--no-themes",
        "--no-context-files",
        "--no-approve",
        "--offline",
        "--system-prompt",
        "/sealed/system-prompt.md",
    ]
    broker_token = secrets.token_urlsafe(48)
    broker_socket = broker_root / "broker.sock"
    broker_session: BrokerSession | None = None
    rpc_server: UnixRpcServer | None = None
    pi_sandbox: dict[str, Any] | None = None
    pi_sandbox_artifact: Any | None = None
    quota_failure: str | None = None
    try:
        broker_session = BrokerSession(capability, quota=artifact_quota)
        rpc_server = UnixRpcServer(
            broker_socket,
            job_id=job_id,
            session_id=session_id,
            token=broker_token,
            execute=broker_session.execute,
            append_event=broker_session.append_rpc_event,
        ).start()
        pi_sandbox = audit_pi_bubblewrap(
            configured_path=sparse_lean["bwrap_path"],
            expected_node_attestation=pi_install["node"],
            install_root=pi_install["install_root"],
            cli_relative=pi_install["cli_js"]["relative_path"],
            expected_install_tree_sha256=pi_install["tree"]["sha256"],
            extension_path=sealed_extension,
            extension_sha256=extension_sha256,
            public_config_path=sealed_public_config,
            public_config_sha256=public_config_artifact.sha256,
            system_prompt_path=sealed_system_prompt,
            system_prompt_sha256=system_prompt_artifact.sha256,
            settings_path=sealed_settings,
            settings_sha256=private_settings_artifact.sha256,
            broker_socket=broker_socket,
            forbidden_paths=(control, state, artifact_dir, worktree, git_common),
            runtime_tmpfs_bytes=_configured_integer(
                "HARNESS_PI_RUNTIME_TMPFS_BYTES",
                64 * 1024 * 1024,
                minimum=1024 * 1024,
                maximum=1024 * 1024 * 1024,
            ),
            tmp_tmpfs_bytes=_configured_integer(
                "HARNESS_PI_TMP_TMPFS_BYTES",
                64 * 1024 * 1024,
                minimum=1024 * 1024,
                maximum=1024 * 1024 * 1024,
            ),
            run_tmpfs_bytes=_configured_integer(
                "HARNESS_PI_RUN_TMPFS_BYTES",
                1024 * 1024,
                minimum=64 * 1024,
                maximum=64 * 1024 * 1024,
            ),
        )
        argv = list(
            bubblewrap_pi_argv(
                spec=pi_sandbox,
                pi_arguments=pi_arguments,
                broker_token=broker_token,
            )
        )
        pi_sandbox_artifact = artifact_store.write_once(
            "pi-sandbox-manifest.json", canonical_json_bytes(pi_sandbox)
        )
        launch = {
            "schema_version": "poincare.pi-launch.v1",
            "job_id": job_id,
            "session_id": session_id,
            "launched_at": _utc_now(),
            "pi_package": "@earendil-works/pi-coding-agent",
            "pi_version": version,
            "pi_install_manifest": pi_install_artifact.relative_path,
            "pi_install_manifest_sha256": pi_install_manifest_sha256,
            "pi_dependency_graph_sha256": _sha256(pi_dependency_graph_bytes),
            "pi_arguments": pi_arguments,
            "guest_cwd": "/runtime",
            "base_commit": job["workspace"]["base_commit"],
            "base_tree": base_tree,
            "extension_sha256": extension_sha256,
            "public_config": public_config_artifact.relative_path,
            "public_config_sha256": public_config_artifact.sha256,
            "system_prompt_artifact": system_prompt_artifact.relative_path,
            "system_prompt_sha256": system_prompt_artifact.sha256,
            "prompt_sha256": snapshot.prompt_sha256,
            "prompt_size_bytes": len(snapshot.prompt.encode("utf-8")),
            "private_settings_artifact": private_settings_artifact.relative_path,
            "private_settings_sha256": private_settings_artifact.sha256,
            "capability_sha256": capability_artifact.sha256,
            "sampling": {"max_tokens": max_tokens, "temperature": temperature},
            "trusted_code_manifest": trusted_code_artifact.relative_path,
            "trusted_code_manifest_sha256": trusted_code_artifact.sha256,
            "trusted_code_aggregate_sha256": trusted_code["aggregate_sha256"],
            "pi_install_tree_sha256": pi_install["tree"]["sha256"],
            "pi_sandbox_manifest": pi_sandbox_artifact.relative_path,
            "pi_sandbox_manifest_sha256": pi_sandbox_artifact.sha256,
            "sparse_lean_preflight": sparse_preflight_artifact.relative_path,
            "sparse_lean_preflight_sha256": sparse_preflight_artifact.sha256,
            "health_check": health_artifact.relative_path,
            "health_check_sha256": health_artifact.sha256,
            "active_tools": list(TOOL_NAMES),
            "rpc_protocol": "poincare.pi-rpc.v1",
            "runtime_storage": "bounded private tmpfs; not authoritative evidence",
            "prompt_transport": "nonblocking supervised stdin",
            "network_residual": "host network namespace shared; no destination filter",
        }
        artifact_store.write_once("pi-launch.json", canonical_json_bytes(launch))
        returncode, process_reason, event_state = _run_pi_process(
            argv=argv,
            env={
                "PATH": "/usr/bin:/bin",
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
                "TZ": "UTC",
            },
            worktree=Path("/"),
            prompt=snapshot.prompt.encode("utf-8"),
            artifact_dir=artifact_dir,
            store=store,
            capability=capability,
            disk_budget_mb=task["budget"]["disk_mb"],
            token_budget=task["budget"]["max_output_tokens"],
            artifact_quota=artifact_quota,
        )
    except PiQuotaError as exc:
        quota_failure = str(exc)
        returncode = 70
        process_reason = "shared artifact quota exhausted"
        event_state = _EventState()
    except (BrokerError, RpcError, SecurityError, OSError) as exc:
        raise PiEngineError(f"Pi sandbox/RPC execution failed: {exc}") from exc
    finally:
        close_error: Exception | None = None
        if rpc_server is not None:
            try:
                rpc_server.close()
            except Exception as exc:
                close_error = exc
        if broker_session is not None:
            try:
                if quota_failure is None:
                    broker_session.close()
                else:
                    broker_session.dispose()
            except Exception as exc:
                broker_session.dispose()
                close_error = close_error or exc
        execution_temp.cleanup()
        if close_error is not None and quota_failure is None:
            raise PiEngineError(f"Pi broker boundary did not close cleanly: {close_error}")
    if quota_failure is not None:
        return _minimal_quota_failure_result(
            artifact_quota=artifact_quota,
            artifact_dir=artifact_dir,
            job_id=job_id,
            reason=quota_failure,
            process_returncode=returncode,
        )
    assert pi_sandbox is not None and pi_sandbox_artifact is not None
    try:
        session_closed_artifact = artifact_store.write_once(
            "pi-session-closed.json",
            canonical_json_bytes(
                {
                    "schema_version": "poincare.pi-session-closed.v1",
                    "job_id": job_id,
                    "session_id": session_id,
                    "closed_at": _utc_now(),
                    "process_returncode": returncode,
                    "process_exit_reason": process_reason,
                    "capability_sha256": capability_artifact.sha256,
                }
            ),
        )
    except PiQuotaError as exc:
        return _minimal_quota_failure_result(
            artifact_quota=artifact_quota,
            artifact_dir=artifact_dir,
            job_id=job_id,
            reason=str(exc),
            process_returncode=returncode,
        )
    terminal_success, terminal_reason, final_text = _validate_terminal(
        event_state, returncode
    )
    success = terminal_success and process_reason == "process_exit"
    exit_reason = terminal_reason if success else (
        process_reason if process_reason != "process_exit" else terminal_reason
    )

    blocked_report = _read_blocked_report(artifact_dir / "pi-blocked-report.json")
    if (
        blocked_report is not None
        and returncode == 0
        and process_reason == "process_exit"
        and event_state.saw_agent_settled
        and not event_state.active_tools
    ):
        # A terminating final tool intentionally skips the follow-up assistant
        # turn, so stopReason may remain `toolUse`. The structured blocker is
        # the canonical outcome and is never treated as a passed Job.
        success = False
        exit_reason = "worker_reported_blocked"

    session_path: Path | None = None
    session_relative: str | None = None
    session_sha256: str | None = None

    patch_limit = min(
        64 * 1024 * 1024,
        max(512 * 1024, task["budget"]["disk_mb"] * 1024 * 1024 // 2),
    )
    patch = b""
    diff_audit: dict[str, Any]
    committed_patches: tuple[CommittedPatch, ...] = ()
    tool_crosscheck: dict[str, Any] = {
        "schema_version": "poincare.pi-tool-crosscheck.v1",
        "valid": False,
    }
    journal_replay: dict[str, Any] = {
        "schema_version": "poincare.pi-journal-replay.v1",
        "valid": False,
    }
    try:
        _validate_live(capability, allow_session_closed=True)
        first_patch, first_audit = _capture_final_diff(
            store=store,
            capability=capability,
            task=task,
            worktree=worktree,
            patch_limit=patch_limit,
        )
        _validate_live(capability, allow_session_closed=True)
        second_patch, second_audit = _capture_final_diff(
            store=store,
            capability=capability,
            task=task,
            worktree=worktree,
            patch_limit=patch_limit,
        )
        stable_fields = {
            "base_commit",
            "head",
            "branch",
            "status_porcelain_v1_z_hex",
            "diff_name_only_z_hex",
            "changed_paths",
            "patch_sha256",
            "patch_size_bytes",
            "diff_check_output_sha256",
        }
        if first_patch != second_patch or any(
            first_audit.get(field) != second_audit.get(field)
            for field in stable_fields
        ):
            second_audit["valid"] = False
            second_audit["error"] = "worktree changed across final live-validation captures"
            raise _FinalDiffAuditError(
                second_audit["error"], patch=second_patch, audit=second_audit
            )
        _validate_live(capability, allow_session_closed=True)
        if not _lease_valid(store, capability):
            raise PiEngineError("final live lease or latest Task revision validation failed")
        replay_patch, committed_patches = _replay_patch_journal(
            artifact_dir=artifact_dir,
            job_id=job_id,
            session_id=session_id,
            worktree=worktree,
            patch_limit=patch_limit,
        )
        if replay_patch != second_patch:
            second_audit["valid"] = False
            second_audit["error"] = (
                "isolated patch-journal replay differs from the canonical HEAD diff"
            )
            raise _FinalDiffAuditError(
                second_audit["error"], patch=second_patch, audit=second_audit
            )
        tool_crosscheck = _crosscheck_tool_evidence(
            artifact_dir=artifact_dir,
            committed=committed_patches,
        )
        journal_replay = {
            "schema_version": "poincare.pi-journal-replay.v1",
            "valid": True,
            "committed_patches": len(committed_patches),
            "tool_call_ids": [item.tool_call_id for item in committed_patches],
            "replay_patch_sha256": _sha256(replay_patch),
            "replay_patch_size_bytes": len(replay_patch),
            "head_patch_sha256": _sha256(second_patch),
        }
        patch = second_patch
        diff_audit = second_audit
        diff_audit["stable_double_capture"] = True
        diff_audit["live_validation_count"] = 3
        diff_audit["journal_replay_matches"] = True
    except _FinalDiffAuditError as exc:
        patch = exc.patch
        diff_audit = exc.audit
        success = False
        exit_reason = f"{exit_reason}; final diff audit failed: {exc}"
    except (BrokerError, PiEngineError, IntegrityError, SecurityError, OSError) as exc:
        success = False
        exit_reason = f"{exit_reason}; final live/diff validation failed: {exc}"
        try:
            patch = _git(
                worktree,
                "diff",
                "--binary",
                "--no-ext-diff",
                "--no-textconv",
                "--no-color",
                "HEAD",
                "--",
                limit=patch_limit,
            )
        except (BrokerError, OSError) as patch_exc:
            patch = b""
            exit_reason = f"{exit_reason}; exact patch capture failed: {patch_exc}"
        diff_audit = _failed_diff_audit(str(exc))
        diff_audit["patch_sha256"] = _sha256(patch)
        diff_audit["patch_size_bytes"] = len(patch)

    patch_artifact = artifact_store.write_once("worker.patch", patch)
    journal_replay_artifact = artifact_store.write_once(
        "patch-journal-replay.json", canonical_json_bytes(journal_replay)
    )
    tool_crosscheck_artifact = artifact_store.write_once(
        "tool-crosscheck.json", canonical_json_bytes(tool_crosscheck)
    )
    diff_audit_artifact = artifact_store.write_once(
        "final-diff-audit.json", canonical_json_bytes(diff_audit)
    )
    if not final_text:
        if blocked_report is not None:
            final_text = (
                "# Pi Job blocked\n\n"
                f"{blocked_report['summary']}\n\n"
                "## Exact Lean type or error\n\n"
                f"{blocked_report['exact_lean_type_or_error']}\n\n"
                "## Strongest verified partial result\n\n"
                f"{blocked_report['strongest_partial_result']}\n"
            )
        else:
            final_text = (
                "# Pi Job final report unavailable\n\n"
                f"The bounded Pi session did not produce a valid final assistant report. Exit reason: {exit_reason}\n"
            )
    final_artifact = artifact_store.write_once(
        "final-report.md", final_text.encode("utf-8")
    )

    broker_events_path = artifact_dir / "pi-broker-events.jsonl"
    if not broker_events_path.exists():
        artifact_store.write_once("pi-broker-events.jsonl", b"")
    logical_names = {
        "pi-events.jsonl": "pi_events",
        "messages.jsonl": "messages",
        "tool-events.jsonl": "tool_events",
        "pi-stderr.log": "stderr",
        "pi-broker-events.jsonl": "broker_events",
        "worker.patch": "worker_patch",
        "final-report.md": "final_report",
        "pi-launch.json": "pi_launch",
        "pi-capability.json": "pi_capability",
        "pi-session-closed.json": "session_closed",
        "prompt.md": "prompt",
        "context-manifest.json": "context_manifest",
        "system-prompt.md": "system_prompt",
        "pi-settings.json": "private_settings",
        "health-check.json": "health_check",
        "trusted-code-manifest.json": "trusted_code_manifest",
        "pi-install-manifest.json": "pi_install_manifest",
        "pi-public-config.json": "public_config",
        "pi-sandbox-manifest.json": "pi_sandbox_manifest",
        "sparse-lean-preflight.json": "sparse_lean_preflight",
        "pi-patch-journal.jsonl": "patch_journal",
        "pi-patch-journal-seal.json": "patch_journal_seal",
        ".pi-patch-journal.lock": "patch_journal_lock",
        "patch-journal-replay.json": "patch_journal_replay",
        "tool-crosscheck.json": "tool_crosscheck",
        "final-diff-audit.json": "final_diff_audit",
        "task.json": "task_snapshot",
        "job.json": "job_snapshot",
    }
    if blocked_report is not None:
        logical_names["pi-blocked-report.json"] = "blocked_report"
    required_paths = set(logical_names)
    required_paths.difference_update(
        {"pi-blocked-report.json", "task.json", "job.json"}
    )
    allowed_directories = {"pi-tools", "pi-patch-blobs"}

    def allowed_dynamic(relative: str) -> bool:
        if re.fullmatch(
            r"pi-tools/[0-9a-f]{24}\.(?:stdout|stderr|lean-sandbox\.json)",
            relative,
        ):
            return True
        return re.fullmatch(
            r"pi-patch-blobs/[0-9]{12}-[0-9a-f]{64}\.patch", relative
        ) is not None

    evidence_targets: list[tuple[str, Path | None]] = []
    observed_paths: set[str] = set()
    for directory, dirnames, filenames in os.walk(artifact_dir, followlinks=False):
        base = Path(directory)
        for name in dirnames:
            candidate = base / name
            relative = candidate.relative_to(artifact_dir).as_posix()
            metadata = os.lstat(candidate)
            if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
                raise PiEngineError("Pi evidence tree contains an unsafe directory")
            if relative not in allowed_directories:
                raise PiEngineError(f"unexpected Pi evidence directory: {relative}")
        for name in filenames:
            candidate = base / name
            relative = candidate.relative_to(artifact_dir).as_posix()
            if relative == ".artifact.lock":
                continue
            metadata = os.lstat(candidate)
            if (
                stat.S_ISLNK(metadata.st_mode)
                or not stat.S_ISREG(metadata.st_mode)
                or metadata.st_nlink != 1
            ):
                raise PiEngineError("Pi evidence tree contains a symlink, hardlink, or special file")
            if relative not in logical_names and not allowed_dynamic(relative):
                raise PiEngineError(f"unexpected Pi evidence artifact: {relative}")
            observed_paths.add(relative)
            evidence_targets.append(
                (logical_names.get(relative, f"artifact:{relative}"), candidate)
            )
    missing_evidence = sorted(required_paths - observed_paths)
    evidence_entries: list[dict[str, Any]] = []
    evidence_paths: list[Path] = []
    for logical_name, evidence_path in evidence_targets:
        assert evidence_path is not None
        entry = _hash_evidence(evidence_path, artifact_dir)
        entry["logical_name"] = logical_name
        evidence_entries.append(entry)
        evidence_paths.append(evidence_path)
    if missing_evidence:
        success = False
        exit_reason = (
            f"{exit_reason}; required evidence missing: {', '.join(missing_evidence)}"
        )
    _seal_evidence(evidence_paths)
    evidence_manifest = {
        "schema_version": "poincare.pi-evidence-manifest.v1",
        "job_id": job_id,
        "recorded_at": _utc_now(),
        "complete": not missing_evidence,
        "files": evidence_entries,
    }
    evidence_manifest_artifact = artifact_store.write_once(
        "evidence-manifest.json",
        canonical_json_bytes(evidence_manifest),
        emergency=True,
    )
    def result_payload() -> dict[str, Any]:
        return {
            "schema_version": "poincare.pi-result.v1",
            "job_id": job_id,
            "recorded_at": _utc_now(),
            "success": success,
            "exit_reason": exit_reason,
            "process_returncode": returncode,
            "events": event_state.event_count,
            "messages": event_state.message_count,
            "tool_events": event_state.tool_event_count,
            "output_tokens": event_state.output_tokens,
            "agent_settled": event_state.saw_agent_settled,
            "final_stop_reason": (
                event_state.last_assistant.get("stopReason")
                if event_state.last_assistant is not None
                else None
            ),
            "session_artifact": session_relative,
            "session_sha256": session_sha256,
            "session_closed_artifact": session_closed_artifact.relative_path,
            "session_closed_sha256": session_closed_artifact.sha256,
            "prompt_sha256": snapshot.prompt_sha256,
            "prompt_size_bytes": len(snapshot.prompt.encode("utf-8")),
            "private_settings_sha256": private_settings_artifact.sha256,
            "output_token_budget": task["budget"]["max_output_tokens"],
            "context_sha256": snapshot.context_sha256,
            "extension_sha256": extension_sha256,
            "trusted_code_aggregate_sha256": trusted_code["aggregate_sha256"],
            "pi_sandbox_profile_version": pi_sandbox["profile_version"],
            "pi_install_manifest_sha256": pi_install_manifest_sha256,
            "pi_install_tree_sha256": pi_install["tree"]["sha256"],
            "worker_patch": patch_artifact.relative_path,
            "worker_patch_sha256": patch_artifact.sha256,
            "final_diff_audit": diff_audit_artifact.relative_path,
            "final_diff_audit_sha256": diff_audit_artifact.sha256,
            "final_report": final_artifact.relative_path,
            "final_report_sha256": final_artifact.sha256,
            "patch_journal_replay": journal_replay_artifact.relative_path,
            "patch_journal_replay_sha256": journal_replay_artifact.sha256,
            "tool_crosscheck": tool_crosscheck_artifact.relative_path,
            "tool_crosscheck_sha256": tool_crosscheck_artifact.sha256,
            "evidence_manifest": evidence_manifest_artifact.relative_path,
            "evidence_manifest_sha256": evidence_manifest_artifact.sha256,
            "evidence": evidence_entries,
            "blocked_reported": blocked_report is not None,
            "authority_note": "evidence only; Codex must independently gate and transition the Job/Task",
        }

    result_artifact: Any | None = None
    if success:
        connection = store._connect()
        try:
            with store._transaction(connection):
                _validate_commit_fence_state(connection, capability)
                if time.time() >= float(capability["deadline_epoch"]):
                    raise PiEngineError(
                        "Task wall-clock capability expired inside the commit fence"
                    )
                terminal_patch, terminal_audit = _capture_final_diff(
                    store=store,
                    capability=capability,
                    task=task,
                    worktree=worktree,
                    patch_limit=patch_limit,
                    live_guard=lambda: True,
                )
                if terminal_patch != patch or not terminal_audit.get("valid"):
                    raise PiEngineError("final HEAD diff changed inside the commit fence")
                if _sha256(terminal_patch) != patch_artifact.sha256:
                    raise PiEngineError(
                        "commit-fenced HEAD diff no longer matches worker.patch"
                    )
                final_install, _graph, final_install_sha256, _manifest_path, _graph_path = (
                    install_verifier(
                        manifest_path=pi_install_manifest_path,
                        dependency_graph_path=pi_dependency_graph_path,
                    )
                )
                if (
                    final_install_sha256 != pi_install_manifest_sha256
                    or final_install != pi_install
                ):
                    raise PiEngineError("Pi distribution changed inside the commit fence")
                if time.time() >= float(capability["deadline_epoch"]):
                    raise PiEngineError(
                        "Task wall-clock capability expired before fenced result write"
                    )
                result_artifact = artifact_store.write_once(
                    "pi-run-result.json",
                    canonical_json_bytes(result_payload()),
                    emergency=True,
                )
        except (
            BrokerError,
            HarnessError,
            PiEngineError,
            PiInstallError,
            PiQuotaError,
            IntegrityError,
            SecurityError,
            OSError,
        ) as exc:
            if result_artifact is not None or (artifact_dir / "pi-run-result.json").exists():
                raise PiEngineError(
                    f"commit-fenced success result write was indeterminate: {exc}"
                ) from exc
            success = False
            exit_reason = f"{exit_reason}; commit-time success fence failed: {exc}"
        finally:
            connection.close()
    if result_artifact is None:
        result_artifact = artifact_store.write_once(
            "pi-run-result.json",
            canonical_json_bytes(result_payload()),
            emergency=True,
        )
    _seal_evidence(
        [
            artifact_dir / evidence_manifest_artifact.relative_path,
            artifact_dir / result_artifact.relative_path,
        ]
    )
    return PiRunResult(
        job_id=job_id,
        success=success,
        exit_reason=exit_reason,
        process_returncode=returncode,
        events=event_state.event_count,
        messages=event_state.message_count,
        tool_events=event_state.tool_event_count,
        output_tokens=event_state.output_tokens,
        session_artifact=session_relative,
        final_report_artifact=final_artifact.relative_path,
        patch_artifact=patch_artifact.relative_path,
        result_artifact=result_artifact.relative_path,
    )
