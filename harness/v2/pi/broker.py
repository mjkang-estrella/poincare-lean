"""Capability broker implementing the only tools exposed to Leanstral."""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import tempfile
import threading
import time
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Callable

from harness.v2.runtime.store import HarnessError, HarnessStore
from harness.v2.worker.artifacts import canonical_json_bytes

from . import TOOL_NAMES
from .integrity import IntegrityError, verify_trusted_code
from .journal import PatchJournal, PatchJournalError
from .quota import PiQuotaError, QuotaWrite, SharedArtifactQuota
from .rpc import RPC_PROTOCOL
from .security import (
    acquire_build_job_lock,
    audit_sparse_lean_bubblewrap,
    bubblewrap_sparse_lean_argv,
    build_sparse_lean_snapshot,
    lean_acceptance_argv,
    normalize_relative,
    path_is_allowed,
    remove_sparse_lean_snapshot,
    resolve_repo_file,
    run_limited,
    sparse_lean_process_limits,
    validate_patch,
)


MAX_TOOL_INPUT_BYTES = 768 * 1024
MAX_READ_LINES = 400
MAX_READ_BYTES = 128 * 1024
MAX_SEARCH_RESULTS = 200
MAX_SEARCH_BYTES = 128 * 1024
MAX_GIT_DIFF_BYTES = 256 * 1024
MAX_LEAN_OUTPUT_BYTES = 1024 * 1024
MAX_PATCH_STATE_FILE_BYTES = 128 * 1024 * 1024
CALL_ID_RE = re.compile(r"^[A-Za-z0-9_.:-]{1,180}$")
FINAL_JOB_MARKERS = (
    "pi-session-closed.json",
    "evidence-manifest.json",
    "pi-run-result.json",
)


class BrokerError(RuntimeError):
    """Raised when a tool request or its live capability is invalid."""


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _exact_object(
    value: Any,
    *,
    required: set[str],
    optional: set[str] = frozenset(),
    label: str = "tool input",
) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BrokerError(f"{label} must be a JSON object")
    missing = required - value.keys()
    extra = value.keys() - required - optional
    if missing or extra:
        raise BrokerError(
            f"{label} fields mismatch; missing={sorted(missing)}, extra={sorted(extra)}"
        )
    return value


def _bounded_string(value: Any, label: str, maximum: int, *, nonempty: bool = True) -> str:
    if not isinstance(value, str):
        raise BrokerError(f"{label} must be a string")
    if nonempty and not value.strip():
        raise BrokerError(f"{label} must not be empty")
    if len(value.encode("utf-8")) > maximum:
        raise BrokerError(f"{label} exceeds its byte cap")
    return value


def _bounded_integer(value: Any, label: str, minimum: int, maximum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise BrokerError(f"{label} must be an integer")
    if not minimum <= value <= maximum:
        raise BrokerError(f"{label} must be between {minimum} and {maximum}")
    return value


def _load_json_file(path: Path, *, label: str, max_bytes: int) -> tuple[dict[str, Any], bytes]:
    if path.is_symlink() or not path.is_file():
        raise BrokerError(f"{label} must be a regular non-symlink file")
    data = path.read_bytes()
    if len(data) > max_bytes:
        raise BrokerError(f"{label} exceeds {max_bytes} bytes")
    try:
        value = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BrokerError(f"{label} is not a UTF-8 JSON object") from exc
    if not isinstance(value, dict):
        raise BrokerError(f"{label} is not a JSON object")
    return value, data


def _resolve_directory(raw: str, label: str) -> Path:
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink():
        raise BrokerError(f"{label} must not be a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise BrokerError(f"cannot resolve {label}: {exc}") from exc
    if not resolved.is_dir():
        raise BrokerError(f"{label} is not a directory")
    return resolved


def _git(
    root: Path,
    *arguments: str,
    limit: int = 128 * 1024,
    guard: Callable[[], bool] | None = None,
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
        cwd=root,
        env=env,
        timeout_seconds=30,
        output_limit_bytes=limit,
        guard=guard,
        supervise_parent=True,
    )
    if (
        result.timed_out
        or result.output_limited
        or result.guard_cancelled
        or result.returncode != 0
    ):
        error = result.stderr.decode("utf-8", "replace").strip()
        raise BrokerError(f"fixed git diagnostic failed: {error or result.returncode}")
    return result.stdout


def _state_lease_is_exact(
    capability: dict[str, Any],
    *,
    task: dict[str, Any],
    job: dict[str, Any],
    runtime: dict[str, Any],
) -> bool:
    """Return whether the mutable Task/Job/lease state still grants this capability."""

    allowed = capability.get("allowed_paths")
    scopes = runtime.get("scopes")
    if not isinstance(allowed, list) or not isinstance(scopes, list):
        return False
    expected_scopes = set(allowed)
    if len(expected_scopes) != len(allowed) or len(scopes) != len(expected_scopes):
        return False
    try:
        held_scopes = {item["path"] for item in scopes}
    except (KeyError, TypeError):
        return False
    return bool(
        task.get("id") == capability.get("task_id")
        and task.get("revision") == capability.get("task_revision")
        and task.get("status") == "active"
        and job.get("id") == capability.get("job_id")
        and job.get("task_id") == capability.get("task_id")
        and job.get("task_revision") == capability.get("task_revision")
        and job.get("state") == "running"
        and job.get("workspace", {}).get("lease_owner")
        == capability.get("lease_owner")
        and runtime.get("lease_active") is True
        and runtime.get("lease_token") == capability.get("lease_token")
        and held_scopes == expected_scopes
        and all(
            item.get("active") is True
            and item.get("owner") == capability.get("lease_owner")
            and item.get("lease_token") == capability.get("lease_token")
            for item in scopes
        )
    )


def _job_is_sealed(
    artifact_dir: Path, *, allow_session_closed: bool = False
) -> bool:
    """Treat any final-result marker, including a symlink, as capability closure."""

    markers = (
        FINAL_JOB_MARKERS[1:] if allow_session_closed else FINAL_JOB_MARKERS
    )
    return any(
        (artifact_dir / name).exists() or (artifact_dir / name).is_symlink()
        for name in markers
    )


def _live_guard(
    capability: dict[str, Any], *, allow_session_closed: bool = False
) -> bool:
    """Cheap fail-closed guard polled while a broker subprocess is running."""

    try:
        if time.time() >= float(capability["deadline_epoch"]):
            return False
        artifact_dir = _resolve_directory(
            capability["artifact_dir"], "Job artifact directory"
        )
        if _job_is_sealed(
            artifact_dir, allow_session_closed=allow_session_closed
        ):
            return False
        state_dir = _resolve_directory(capability["state_dir"], "state directory")
        store = HarnessStore(state_dir)
        latest = store.get_task(capability["task_id"])["task"]
        if latest.get("revision") != capability.get("task_revision"):
            return False
        job_payload = store.get_job(capability["job_id"])
        return _state_lease_is_exact(
            capability,
            task=latest,
            job=job_payload["job"],
            runtime=job_payload["runtime"],
        )
    except Exception:
        return False


def _validate_capability_shape(capability: dict[str, Any]) -> None:
    required = {
        "schema_version",
        "session_id",
        "job_id",
        "task_id",
        "task_revision",
        "state_dir",
        "control_root",
        "artifact_dir",
        "worktree",
        "base_commit",
        "branch",
        "lease_owner",
        "lease_token",
        "allowed_paths",
        "forbidden_paths",
        "readable_paths",
        "acceptance_commands",
        "forbidden_added_tokens",
        "backend",
        "prompt_sha256",
        "context_sha256",
        "launched_at_epoch",
        "deadline_epoch",
        "lean_timeout_seconds",
        "artifact_quota_bytes",
        "extension_sha256",
        "system_prompt_sha256",
        "trusted_code",
        "lean_scratch_root",
        "sparse_lean",
    }
    _exact_object(capability, required=required, label="Pi capability")
    if capability["schema_version"] != "poincare.pi-capability.v1":
        raise BrokerError("unsupported Pi capability schema")
    session_id = _bounded_string(capability["session_id"], "session_id", 180)
    if CALL_ID_RE.fullmatch(session_id) is None:
        raise BrokerError("Pi capability session ID has an invalid form")
    _bounded_integer(
        capability["artifact_quota_bytes"],
        "artifact_quota_bytes",
        1,
        1024 * 1024 * 1024 * 1024,
    )
    sparse_required = {
        "bwrap_path",
        "systemd_run_path",
        "git_path",
        "immutable_lake_cache",
        "toolchain_roots",
        "base_commit",
        "base_tree",
        "forbidden_host_paths",
        "memory_max_bytes",
        "tasks_max",
        "cpu_quota_percent",
        "process_limits",
    }
    _exact_object(
        capability["sparse_lean"],
        required=sparse_required,
        label="sparse Lean configuration",
    )
    _bounded_string(capability["lean_scratch_root"], "lean_scratch_root", 4096)


def _load_capability(path: Path, expected_sha256: str) -> dict[str, Any]:
    capability, data = _load_json_file(path, label="Pi capability", max_bytes=256 * 1024)
    if not re.fullmatch(r"[0-9a-f]{64}", expected_sha256):
        raise BrokerError("capability hash has an invalid form")
    if _sha256(data) != expected_sha256:
        raise BrokerError("Pi capability hash mismatch")
    _validate_capability_shape(capability)
    return capability


def _validate_live(
    capability: dict[str, Any], *, allow_session_closed: bool = False
) -> tuple[dict[str, Any], dict[str, Any], Path, Path]:
    if time.time() >= float(capability["deadline_epoch"]):
        raise BrokerError("Job wall-clock capability expired")
    state_dir = _resolve_directory(capability["state_dir"], "state directory")
    store = HarnessStore(state_dir)
    try:
        job_payload = store.get_job(capability["job_id"])
        task_payload = store.get_task(capability["task_id"])
    except HarnessError as exc:
        raise BrokerError(f"cannot validate live Harness state: {exc}") from exc
    job = job_payload["job"]
    runtime = job_payload["runtime"]
    task = task_payload["task"]
    if task.get("revision") != capability["task_revision"]:
        raise BrokerError("Job capability references a stale Task revision")
    comparisons = {
        "job Task ID": (job["task_id"], capability["task_id"]),
        "job Task revision": (job["task_revision"], capability["task_revision"]),
        "Task base commit": (task["base_commit"], capability["base_commit"]),
        "Job base commit": (job["workspace"]["base_commit"], capability["base_commit"]),
        "worktree": (job["workspace"]["worktree"], capability["worktree"]),
        "branch": (job["workspace"]["branch"], capability["branch"]),
        "lease owner": (job["workspace"]["lease_owner"], capability["lease_owner"]),
        "lease token": (runtime["lease_token"], capability["lease_token"]),
        "backend": (job["backend"], capability["backend"]),
        "prompt hash": (job["artifacts"]["prompt_sha256"], capability["prompt_sha256"]),
        "context hash": (job["artifacts"]["context_sha256"], capability["context_sha256"]),
        "allowed scope": (task["scope"]["allowed_paths"], capability["allowed_paths"]),
        "forbidden scope": (task["scope"]["forbidden_paths"], capability["forbidden_paths"]),
        "acceptance commands": (task["acceptance"]["commands"], capability["acceptance_commands"]),
        "forbidden tokens": (
            task["acceptance"]["forbidden_added_tokens"],
            capability["forbidden_added_tokens"],
        ),
    }
    mismatches = [label for label, values in comparisons.items() if values[0] != values[1]]
    if mismatches:
        raise BrokerError(f"live Task/Job capability mismatch: {', '.join(mismatches)}")
    if not _state_lease_is_exact(
        capability, task=task, job=job, runtime=runtime
    ):
        raise BrokerError("Job no longer holds its exact file-scope lease")

    root = _resolve_directory(capability["worktree"], "Job worktree")
    artifact_dir = _resolve_directory(capability["artifact_dir"], "Job artifact directory")
    if _job_is_sealed(
        artifact_dir, allow_session_closed=allow_session_closed
    ):
        raise BrokerError("Pi Job evidence is finalized; tool capability is closed")
    control_root = _resolve_directory(capability["control_root"], "control repository")
    try:
        verify_trusted_code(control_root, capability["trusted_code"])
    except IntegrityError as exc:
        raise BrokerError(f"trusted Harness code validation failed: {exc}") from exc
    relative_artifact = Path(*PurePosixPath(job["artifacts"]["directory"]).parts)
    if (control_root / relative_artifact).resolve(strict=True) != artifact_dir:
        raise BrokerError("Job artifact directory escaped its recorded control-plane path")
    guard = lambda: _live_guard(
        capability, allow_session_closed=allow_session_closed
    )
    top = Path(
        _git(root, "rev-parse", "--show-toplevel", guard=guard).decode().strip()
    ).resolve()
    head = _git(root, "rev-parse", "HEAD", guard=guard).decode().strip()
    branch = _git(
        root, "symbolic-ref", "--quiet", "--short", "HEAD", guard=guard
    ).decode().strip()
    if top != root or head != capability["base_commit"] or branch != capability["branch"]:
        raise BrokerError("worktree root, HEAD, or branch no longer matches the Job")
    return task, job, root, artifact_dir


def _quota_for_capability(
    capability: dict[str, Any], artifact_dir: Path
) -> SharedArtifactQuota:
    try:
        maximum = _bounded_integer(
            capability["artifact_quota_bytes"],
            "artifact_quota_bytes",
            1,
            1024 * 1024 * 1024 * 1024,
        )
        return SharedArtifactQuota(artifact_dir, maximum)
    except (KeyError, PiQuotaError) as exc:
        raise BrokerError(f"cannot establish shared Pi artifact quota: {exc}") from exc


def _quota_write_once(
    quota: SharedArtifactQuota, relative: str, data: bytes
) -> QuotaWrite:
    try:
        return quota.write_once(relative, data)
    except PiQuotaError as exc:
        raise BrokerError(f"Pi artifact write rejected: {exc}") from exc


def _paths_overlap(left: Path, right: Path) -> bool:
    try:
        left.relative_to(right)
        return True
    except ValueError:
        pass
    try:
        right.relative_to(left)
        return True
    except ValueError:
        return False


def _private_owned_directory(raw: Any, label: str) -> Path:
    value = _bounded_string(raw, label, 4096)
    if not Path(value).is_absolute() or os.path.normpath(value) != value:
        raise BrokerError(f"{label} must be a normalized absolute path")
    lexical = Path(value)
    if lexical.is_symlink():
        raise BrokerError(f"{label} must not be a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
        info = resolved.stat(follow_symlinks=False)
    except OSError as exc:
        raise BrokerError(f"cannot resolve {label}: {exc}") from exc
    if (
        resolved != lexical
        or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) & 0o700 != 0o700
        or stat.S_IMODE(info.st_mode) & 0o077
    ):
        raise BrokerError(f"{label} must be a canonical private directory owned by the Harness uid")
    return resolved


def _lean_scratch_root(capability: dict[str, Any]) -> Path:
    scratch = _private_owned_directory(
        capability["lean_scratch_root"], "Lean check scratch root"
    )
    protected = (
        _resolve_directory(capability["control_root"], "control repository"),
        _resolve_directory(capability["state_dir"], "state directory"),
        _resolve_directory(capability["artifact_dir"], "Job artifact directory"),
        _resolve_directory(capability["worktree"], "Job worktree"),
    )
    if any(_paths_overlap(scratch, item) for item in protected):
        raise BrokerError("Lean check scratch root overlaps a protected Harness path")
    return scratch


def _systemd_user_environment() -> dict[str, str]:
    runtime = Path(f"/run/user/{os.geteuid()}")
    try:
        info = os.lstat(runtime)
    except OSError as exc:
        raise BrokerError(f"cannot inspect systemd user runtime directory: {exc}") from exc
    if (
        stat.S_ISLNK(info.st_mode)
        or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) & 0o700 != 0o700
        or stat.S_IMODE(info.st_mode) & 0o077
        or runtime.resolve(strict=True) != runtime
    ):
        raise BrokerError("systemd user runtime directory is not canonical and private")
    bus = runtime / "bus"
    try:
        bus_info = os.lstat(bus)
    except OSError as exc:
        raise BrokerError(f"cannot inspect systemd user bus: {exc}") from exc
    if not stat.S_ISSOCK(bus_info.st_mode) or bus_info.st_uid != os.geteuid():
        raise BrokerError("systemd user bus is not a Harness-owned Unix socket")
    return {
        "PATH": "/nonexistent",
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "XDG_RUNTIME_DIR": str(runtime),
        "DBUS_SESSION_BUS_ADDRESS": f"unix:path={bus}",
    }


def _append_event(quota: SharedArtifactQuota, event: dict[str, Any]) -> None:
    try:
        data = (
            json.dumps(
                event,
                ensure_ascii=True,
                allow_nan=False,
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise BrokerError("Pi broker event is not canonical JSON data") from exc
    try:
        quota.append("pi-broker-events.jsonl", data)
    except PiQuotaError as exc:
        raise BrokerError(f"cannot append Pi broker event log: {exc}") from exc


def _artifact_token(call_id: str) -> str:
    return hashlib.sha256(call_id.encode("utf-8")).hexdigest()[:24]


def _safe_file_sha256(path: Path, *, label: str) -> str:
    """Hash a private regular file while detecting path and content races."""

    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise BrokerError(f"cannot open {label} safely: {exc}") from exc
    try:
        before = os.fstat(descriptor)
        lexical = os.lstat(path)
        if (
            not stat.S_ISREG(before.st_mode)
            or stat.S_ISLNK(lexical.st_mode)
            or before.st_nlink != 1
            or lexical.st_nlink != 1
            or (before.st_dev, before.st_ino) != (lexical.st_dev, lexical.st_ino)
        ):
            raise BrokerError(f"{label} is not a private regular file")
        if before.st_size > MAX_PATCH_STATE_FILE_BYTES:
            raise BrokerError(f"{label} exceeds the patch-state hashing cap")
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            total += len(chunk)
        after = os.fstat(descriptor)
        current = os.lstat(path)
        identity_before = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_nlink,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        identity_after = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        identity_current = (
            current.st_dev,
            current.st_ino,
            current.st_mode,
            current.st_nlink,
            current.st_size,
            current.st_mtime_ns,
            current.st_ctime_ns,
        )
        if total != before.st_size or identity_after != identity_before:
            raise BrokerError(f"{label} changed while being hashed")
        if identity_current != identity_after or stat.S_ISLNK(current.st_mode):
            raise BrokerError(f"{label} path changed while being hashed")
        return digest.hexdigest()
    except OSError as exc:
        raise BrokerError(f"cannot hash {label} safely: {exc}") from exc
    finally:
        os.close(descriptor)


def _scoped_sha256(root: Path, paths: tuple[str, ...]) -> dict[str, str]:
    hashes: dict[str, str] = {}
    for relative in paths:
        path = resolve_repo_file(root, relative)
        hashes[relative] = _safe_file_sha256(
            path, label=f"scoped patch path {relative}"
        )
    return hashes


def _tool_read_context(capability: dict[str, Any], root: Path, value: Any) -> dict[str, Any]:
    params = _exact_object(
        value,
        required={"path"},
        optional={"start_line", "max_lines"},
        label="read_context input",
    )
    relative = normalize_relative(_bounded_string(params["path"], "path", 1024))
    if relative not in capability["readable_paths"]:
        raise BrokerError("read_context path is not in this Task's readable context")
    start = _bounded_integer(params.get("start_line", 1), "start_line", 1, 10_000_000)
    count = _bounded_integer(params.get("max_lines", 200), "max_lines", 1, MAX_READ_LINES)
    path = resolve_repo_file(root, relative)
    if path.stat().st_size > 2 * 1024 * 1024:
        raise BrokerError("context file exceeds the per-file read cap")
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise BrokerError(f"cannot read UTF-8 context: {exc}") from exc
    selected = lines[start - 1 : start - 1 + count]
    rendered = "\n".join(f"{start + index}: {line}" for index, line in enumerate(selected))
    encoded = rendered.encode("utf-8")
    if len(encoded) > MAX_READ_BYTES:
        rendered = encoded[:MAX_READ_BYTES].decode("utf-8", "ignore") + "\n[output capped]"
    return {
        "text": rendered or "[no lines in requested range]",
        "details": {
            "path": relative,
            "start_line": start,
            "returned_lines": len(selected),
            "total_lines": len(lines),
        },
    }


def _tool_search_symbol(capability: dict[str, Any], root: Path, value: Any) -> dict[str, Any]:
    params = _exact_object(
        value,
        required={"symbol"},
        optional={"paths", "max_results"},
        label="search_symbol input",
    )
    symbol = _bounded_string(params["symbol"], "symbol", 256)
    max_results = _bounded_integer(
        params.get("max_results", 50), "max_results", 1, MAX_SEARCH_RESULTS
    )
    raw_paths = params.get("paths", capability["readable_paths"])
    if not isinstance(raw_paths, list) or len(raw_paths) > 64:
        raise BrokerError("paths must be an array with at most 64 entries")
    paths: list[str] = []
    for raw in raw_paths:
        relative = normalize_relative(_bounded_string(raw, "paths item", 1024))
        if relative not in capability["readable_paths"]:
            raise BrokerError("search_symbol path is outside readable Task context")
        if relative not in paths:
            paths.append(relative)
    results: list[str] = []
    for relative in paths:
        path = resolve_repo_file(root, relative)
        if path.stat().st_size > 2 * 1024 * 1024:
            raise BrokerError(f"search file exceeds size cap: {relative}")
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError) as exc:
            raise BrokerError(f"cannot search UTF-8 context {relative}: {exc}") from exc
        for number, line in enumerate(lines, 1):
            if symbol in line:
                results.append(f"{relative}:{number}:{line}")
                if len(results) >= max_results:
                    break
        if len(results) >= max_results:
            break
    text = "\n".join(results) or "[no literal symbol matches]"
    encoded = text.encode("utf-8")
    if len(encoded) > MAX_SEARCH_BYTES:
        text = encoded[:MAX_SEARCH_BYTES].decode("utf-8", "ignore") + "\n[output capped]"
    return {"text": text, "details": {"matches": len(results), "paths": paths}}


def _tool_apply_patch(
    capability: dict[str, Any],
    root: Path,
    journal: PatchJournal,
    call_id: str,
    value: Any,
) -> dict[str, Any]:
    params = _exact_object(value, required={"patch"}, label="apply_patch_scoped input")
    patch = _bounded_string(params["patch"], "patch", 512 * 1024)
    touched = validate_patch(
        patch,
        root=root,
        allowed=capability["allowed_paths"],
        forbidden=capability["forbidden_paths"],
        forbidden_tokens=capability["forbidden_added_tokens"],
    )
    encoded_patch = patch.encode("utf-8")
    before_sha256 = _scoped_sha256(root, touched)
    try:
        intent = journal.record_intent(call_id, touched, encoded_patch)
    except PatchJournalError as exc:
        raise BrokerError(f"cannot record scoped patch intent: {exc}") from exc
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
    }
    git_prefix = (
        "git",
        "-c",
        "core.fsmonitor=false",
        "-c",
        f"core.hooksPath={os.devnull}",
        "-c",
        "diff.external=",
    )
    guard = lambda: _live_guard(capability)
    try:
        check = run_limited(
            (*git_prefix, "apply", "--check", "--whitespace=error-all", "-"),
            cwd=root,
            env=env,
            timeout_seconds=30,
            output_limit_bytes=128 * 1024,
            stdin=encoded_patch,
            guard=guard,
            supervise_parent=True,
        )
        if (
            check.returncode != 0
            or check.timed_out
            or check.output_limited
            or check.guard_cancelled
        ):
            error = check.stderr.decode("utf-8", "replace").strip()
            reason = "live Job capability was revoked" if check.guard_cancelled else error
            raise BrokerError(f"git apply --check rejected scoped patch: {reason}")
        applied = run_limited(
            (*git_prefix, "apply", "--whitespace=error-all", "-"),
            cwd=root,
            env=env,
            timeout_seconds=30,
            output_limit_bytes=128 * 1024,
            stdin=encoded_patch,
            guard=guard,
            supervise_parent=True,
        )
        if (
            applied.returncode != 0
            or applied.timed_out
            or applied.output_limited
            or applied.guard_cancelled
        ):
            error = applied.stderr.decode("utf-8", "replace").strip()
            reason = "live Job capability was revoked" if applied.guard_cancelled else error
            raise BrokerError(f"scoped git apply failed after check: {reason}")
        changed_raw = _git(
            root,
            "diff",
            "--name-only",
            "-z",
            "--",
            limit=128 * 1024,
            guard=guard,
        )
        changed = [item.decode("utf-8") for item in changed_raw.split(b"\0") if item]
        if any(
            not path_is_allowed(
                path, capability["allowed_paths"], capability["forbidden_paths"]
            )
            for path in changed
        ):
            raise BrokerError("post-apply diff escaped Task scope")
        _validate_live(capability)
        after_sha256 = _scoped_sha256(root, touched)
        _validate_live(capability)
        try:
            journal.commit(intent, before_sha256, after_sha256)
        except PatchJournalError as exc:
            raise BrokerError(f"cannot commit scoped patch journal entry: {exc}") from exc
    except Exception as exc:
        try:
            journal.abort(intent)
        except Exception as abort_exc:
            raise BrokerError(
                f"scoped patch failed and its journal intent could not be aborted: {abort_exc}"
            ) from exc
        raise
    blob = (
        f"pi-patch-blobs/{intent.sequence:012d}-{intent.patch_sha256}.patch"
    )
    return {
        "text": f"Applied scoped patch to: {', '.join(touched)}",
        "details": {
            "touched": list(touched),
            "changed_paths": changed,
            "patch_artifact": blob,
            "patch_sha256": intent.patch_sha256,
            "journal_intent_sequence": intent.sequence,
            "before_sha256": before_sha256,
            "after_sha256": after_sha256,
        },
    }


def _tool_lean_check(
    capability: dict[str, Any],
    root: Path,
    quota: SharedArtifactQuota,
    call_id: str,
    value: Any,
) -> dict[str, Any]:
    params = _exact_object(value, required={"command_index"}, label="lean_check input")
    commands = capability["acceptance_commands"]
    index = _bounded_integer(params["command_index"], "command_index", 0, len(commands) - 1)
    argv = lean_acceptance_argv(commands[index])
    if len(argv) != 4 or argv[:3] != ("lake", "env", "lean"):
        raise BrokerError("lean_check accepts only a recorded `lake env lean FILE.lean` command")
    token = _artifact_token(call_id)
    scratch = _lean_scratch_root(capability)
    config = capability["sparse_lean"]
    if config["base_commit"] != capability["base_commit"]:
        raise BrokerError("sparse Lean configuration has the wrong base commit")
    forbidden_raw = config["forbidden_host_paths"]
    if not isinstance(forbidden_raw, list) or not forbidden_raw:
        raise BrokerError("sparse Lean forbidden_host_paths must be a nonempty array")
    forbidden_paths: list[Path] = []
    for raw in forbidden_raw:
        value_path = _bounded_string(raw, "sparse Lean forbidden path", 4096)
        if not Path(value_path).is_absolute():
            raise BrokerError("sparse Lean forbidden paths must be absolute")
        forbidden_paths.append(Path(value_path))
    if any(_paths_overlap(scratch, path.resolve(strict=True)) for path in forbidden_paths):
        raise BrokerError("Lean check scratch root overlaps a forbidden host path")

    result: Any | None = None
    sandbox: dict[str, Any] | None = None
    snapshot: dict[str, Any] | None = None
    stdout_artifact: QuotaWrite | None = None
    stderr_artifact: QuotaWrite | None = None
    manifest_artifact: QuotaWrite | None = None
    remaining = float(capability["deadline_epoch"]) - time.time()
    if remaining <= 0:
        raise BrokerError("Job wall-clock capability expired before Lean check")
    lock_timeout = min(5.0, remaining)
    with acquire_build_job_lock(
        capability["state_dir"], timeout_seconds=lock_timeout
    ):
        check_dir = Path(tempfile.mkdtemp(prefix=f"{token}-", dir=scratch))
        try:
            if check_dir.parent != scratch or check_dir.is_symlink():
                raise BrokerError("Lean check scratch child escaped its private root")
            snapshot = build_sparse_lean_snapshot(
                worktree=root,
                acceptance_commands=[argv],
                output_dir=check_dir / "source",
                git_path=config["git_path"],
            )
            _validate_live(capability)
            sandbox = audit_sparse_lean_bubblewrap(
                configured_path=config["bwrap_path"],
                systemd_run_path=config["systemd_run_path"],
                sparse_snapshot=snapshot,
                immutable_lake_cache=config["immutable_lake_cache"],
                extra_toolchain_roots=config["toolchain_roots"],
                forbidden_paths=forbidden_paths,
                base_commit=config["base_commit"],
                base_tree=config["base_tree"],
                memory_max_bytes=config["memory_max_bytes"],
                tasks_max=config["tasks_max"],
                cpu_quota_percent=config["cpu_quota_percent"],
                process_limits=config["process_limits"],
            )
            sandbox_argv = bubblewrap_sparse_lean_argv(
                spec=sandbox, command=argv
            )
            manifest_artifact = _quota_write_once(
                quota,
                f"pi-tools/{token}.lean-sandbox.json",
                canonical_json_bytes(
                    {
                        "schema_version": "poincare.pi-lean-check.v1",
                        "job_id": capability["job_id"],
                        "session_id": capability["session_id"],
                        "tool_call_id": call_id,
                        "command_index": index,
                        "argv": list(argv),
                        "snapshot": snapshot,
                        "sandbox": sandbox,
                    }
                ),
            )
            _validate_live(capability)
            remaining = float(capability["deadline_epoch"]) - time.time()
            if remaining <= 0:
                raise BrokerError("Job wall-clock capability expired before Lean execution")
            result = run_limited(
                sandbox_argv,
                cwd=check_dir,
                env=_systemd_user_environment(),
                timeout_seconds=min(
                    float(capability["lean_timeout_seconds"]), remaining
                ),
                output_limit_bytes=MAX_LEAN_OUTPUT_BYTES,
                guard=lambda: _live_guard(capability),
                supervise_parent=True,
                resource_limits=sparse_lean_process_limits(sandbox),
            )
            stdout_artifact = _quota_write_once(
                quota, f"pi-tools/{token}.stdout", result.stdout
            )
            stderr_artifact = _quota_write_once(
                quota, f"pi-tools/{token}.stderr", result.stderr
            )
        finally:
            if snapshot is not None:
                remove_sparse_lean_snapshot(
                    sparse_snapshot=snapshot, checks_root=scratch
                )
            try:
                os.rmdir(check_dir)
            except OSError as exc:
                raise BrokerError(
                    f"cannot remove private Lean check directory: {exc}"
                ) from exc
    if (
        result is None
        or sandbox is None
        or snapshot is None
        or stdout_artifact is None
        or stderr_artifact is None
        or manifest_artifact is None
    ):
        raise BrokerError("Lean check ended without complete broker evidence")
    combined = result.stdout + (b"\n" if result.stdout and result.stderr else b"") + result.stderr
    display = combined[:128 * 1024].decode("utf-8", "replace")
    if len(combined) > 128 * 1024:
        display += "\n[tool display capped; artifact retains bounded process output]"
    if result.guard_cancelled:
        raise BrokerError("Lean check was terminated because the live Job capability was revoked")
    status = (
        "passed"
        if result.returncode == 0 and not result.timed_out and not result.output_limited
        else "failed"
    )
    return {
        "text": (
            f"Lean check {status}; argv={json.dumps(list(argv))}; exit={result.returncode}; "
            f"timeout={result.timed_out}; output_limit={result.output_limited}\n{display}"
        ),
        "details": {
            "command_index": index,
            "argv": list(argv),
            "returncode": result.returncode,
            "timed_out": result.timed_out,
            "output_limited": result.output_limited,
            "duration_seconds": result.duration_seconds,
            "sandbox_profile": sandbox.get("profile_version"),
            "sparse_snapshot_sha256": snapshot["tree_sha256"],
            "sandbox_manifest_artifact": manifest_artifact.relative_path,
            "stdout_artifact": stdout_artifact.relative_path,
            "stderr_artifact": stderr_artifact.relative_path,
        },
    }


def _tool_git_diff(
    capability: dict[str, Any], root: Path, value: Any
) -> dict[str, Any]:
    params = _exact_object(
        value, required=set(), optional={"view"}, label="git_diff input"
    )
    view = params.get("view", "patch")
    commands = {
        "patch": ("diff", "--no-ext-diff", "--no-textconv", "--no-color", "--"),
        "check": ("diff", "--no-ext-diff", "--no-textconv", "--check", "--"),
        "name_only": ("diff", "--no-ext-diff", "--no-textconv", "--name-only", "--"),
        "stat": ("diff", "--no-ext-diff", "--no-textconv", "--stat", "--"),
        "status": ("status", "--short", "--branch"),
    }
    if view not in commands:
        raise BrokerError("git_diff view must be patch, check, name_only, stat, or status")
    output = _git(
        root,
        *commands[view],
        limit=MAX_GIT_DIFF_BYTES,
        guard=lambda: _live_guard(capability),
    )
    text = output.decode("utf-8", "replace") or "[no diff output]"
    return {"text": text, "details": {"view": view, "bytes": len(output)}}


def _tool_report_blocked(quota: SharedArtifactQuota, value: Any) -> dict[str, Any]:
    params = _exact_object(
        value,
        required={
            "summary",
            "exact_lean_type_or_error",
            "attempted_routes",
            "strongest_partial_result",
        },
        label="report_blocked input",
    )
    summary = _bounded_string(params["summary"], "summary", 16 * 1024)
    exact = _bounded_string(
        params["exact_lean_type_or_error"], "exact_lean_type_or_error", 64 * 1024
    )
    strongest = _bounded_string(
        params["strongest_partial_result"], "strongest_partial_result", 32 * 1024
    )
    routes = params["attempted_routes"]
    if not isinstance(routes, list) or not routes or len(routes) > 32:
        raise BrokerError("attempted_routes must be a nonempty array of at most 32 strings")
    normalized_routes = [
        _bounded_string(item, "attempted_routes item", 8 * 1024) for item in routes
    ]
    report = {
        "schema_version": "poincare.pi-blocked.v1",
        "reported_at": _utc_now(),
        "summary": summary,
        "exact_lean_type_or_error": exact,
        "attempted_routes": normalized_routes,
        "strongest_partial_result": strongest,
    }
    artifact = _quota_write_once(
        quota, "pi-blocked-report.json", canonical_json_bytes(report)
    )
    return {
        "text": "Blocked report recorded. Stop making changes and provide the required final response.",
        "details": {
            "artifact": artifact.relative_path,
            "sha256": artifact.sha256,
            "terminate": True,
        },
    }


def _execute_bound_tool(
    *,
    capability: dict[str, Any],
    root: Path,
    artifact_dir: Path,
    quota: SharedArtifactQuota,
    journal: PatchJournal,
    tool_name: str,
    call_id: str,
    value: Any,
    sequence: int | None = None,
) -> dict[str, Any]:
    if tool_name not in TOOL_NAMES:
        raise BrokerError("tool is not in the exact Harness allowlist")
    call_id = _bounded_string(call_id, "Pi tool call ID", 180)
    if CALL_ID_RE.fullmatch(call_id) is None:
        raise BrokerError("Pi tool call ID has an invalid form")
    blocked_path = artifact_dir / "pi-blocked-report.json"
    if blocked_path.exists() or blocked_path.is_symlink():
        raise BrokerError("report_blocked has already closed the Job capability")
    handlers: dict[str, Callable[[], dict[str, Any]]] = {
        "read_context": lambda: _tool_read_context(capability, root, value),
        "search_symbol": lambda: _tool_search_symbol(capability, root, value),
        "apply_patch_scoped": lambda: _tool_apply_patch(
            capability, root, journal, call_id, value
        ),
        "lean_check": lambda: _tool_lean_check(
            capability, root, quota, call_id, value
        ),
        "git_diff": lambda: _tool_git_diff(capability, root, value),
        "report_blocked": lambda: _tool_report_blocked(quota, value),
    }
    started = time.monotonic()
    try:
        _task, _job, live_root, live_artifact_dir = _validate_live(capability)
        if live_root != root or live_artifact_dir != artifact_dir:
            raise BrokerError("live broker roots changed after session creation")
        result = handlers[tool_name]()
        _validate_live(capability)
    except Exception as exc:
        event = {
                "at": _utc_now(),
                "event": "pi_tool_error",
                "job_id": capability["job_id"],
                "session_id": capability["session_id"],
                "tool_call_id": call_id,
                "tool_name": tool_name,
                "error": str(exc),
                "duration_seconds": time.monotonic() - started,
            }
        if sequence is not None:
            event["sequence"] = sequence
        try:
            _append_event(quota, event)
        except Exception as event_exc:
            raise BrokerError(
                f"tool failed and its broker error event could not be recorded: {event_exc}"
            ) from exc
        raise
    event = {
            "at": _utc_now(),
            "event": "pi_tool_result",
            "job_id": capability["job_id"],
            "session_id": capability["session_id"],
            "tool_call_id": call_id,
            "tool_name": tool_name,
            "details": result.get("details", {}),
            "duration_seconds": time.monotonic() - started,
        }
    if sequence is not None:
        event["sequence"] = sequence
    _append_event(quota, event)
    return result


class BrokerSession:
    """One serialized, in-memory capability boundary for an engine-owned RPC server."""

    def __init__(
        self,
        capability: dict[str, Any],
        *,
        quota: SharedArtifactQuota | None = None,
        journal: PatchJournal | None = None,
    ) -> None:
        try:
            frozen = json.loads(
                json.dumps(
                    capability,
                    ensure_ascii=True,
                    allow_nan=False,
                    sort_keys=True,
                    separators=(",", ":"),
                )
            )
        except (TypeError, ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise BrokerError("Pi capability is not canonical JSON data") from exc
        if not isinstance(frozen, dict):
            raise BrokerError("Pi capability must be a JSON object")
        _validate_capability_shape(frozen)
        _task, _job, root, artifact_dir = _validate_live(frozen)
        selected_quota = quota or _quota_for_capability(frozen, artifact_dir)
        try:
            quota_root = selected_quota.root.resolve(strict=True)
        except (AttributeError, OSError) as exc:
            raise BrokerError("broker quota has no valid artifact root") from exc
        if quota_root != artifact_dir:
            raise BrokerError("broker quota root does not match the Job artifact directory")
        lean_scratch = _lean_scratch_root(frozen)
        try:
            if any(lean_scratch.iterdir()):
                raise BrokerError("Lean check scratch root is not fresh and empty")
        except OSError as exc:
            raise BrokerError(f"cannot enumerate Lean check scratch root: {exc}") from exc
        try:
            selected_journal = journal or PatchJournal.create(
                artifact_dir,
                frozen["job_id"],
                frozen["session_id"],
                quota=selected_quota,
            )
        except (PatchJournalError, PiQuotaError) as exc:
            raise BrokerError(f"cannot create Pi patch journal: {exc}") from exc
        if (
            selected_journal.root != artifact_dir
            or selected_journal.job_id != frozen["job_id"]
            or selected_journal.session_id != frozen["session_id"]
        ):
            if journal is None:
                selected_journal.dispose()
            raise BrokerError("patch journal does not match the broker Job session")
        self._capability = frozen
        self._root = root
        self._artifact_dir = artifact_dir
        self._quota = selected_quota
        self._journal = selected_journal
        self._lean_scratch = lean_scratch
        self._lock = threading.Lock()
        self._seen_call_ids: set[str] = set()
        self._next_sequence = 1
        self._closed = False
        self._disposed = False

    @property
    def job_id(self) -> str:
        return str(self._capability["job_id"])

    @property
    def session_id(self) -> str:
        return str(self._capability["session_id"])

    def _execute_tool_call(
        self,
        *,
        tool_name: str,
        call_id: str,
        value: Any,
        sequence: int | None = None,
    ) -> dict[str, Any]:
        if not self._lock.acquire(blocking=False):
            raise BrokerError("parallel broker tool execution is forbidden")
        try:
            if self._closed:
                raise BrokerError("Pi broker session is closed")
            call_id = _bounded_string(call_id, "Pi tool call ID", 180)
            if CALL_ID_RE.fullmatch(call_id) is None:
                raise BrokerError("Pi tool call ID has an invalid form")
            if call_id in self._seen_call_ids:
                raise BrokerError("Pi tool call ID replay is forbidden")
            if sequence is not None:
                checked_sequence = _bounded_integer(
                    sequence, "RPC sequence", 1, 2**63 - 1
                )
                if checked_sequence != self._next_sequence:
                    raise BrokerError(
                        f"RPC sequence must be exactly {self._next_sequence}"
                    )
            else:
                checked_sequence = self._next_sequence
            # Consume request identity before any effect.  A transport failure
            # must never permit replay of a call that may already have mutated
            # the worktree or committed evidence.
            self._seen_call_ids.add(call_id)
            self._next_sequence += 1
            return _execute_bound_tool(
                capability=self._capability,
                root=self._root,
                artifact_dir=self._artifact_dir,
                quota=self._quota,
                journal=self._journal,
                tool_name=tool_name,
                call_id=call_id,
                value=value,
                sequence=checked_sequence,
            )
        finally:
            self._lock.release()

    def execute(self, request: Any) -> dict[str, Any]:
        """Execute one authenticated, token-free request supplied by ``UnixRpcServer``."""

        params = _exact_object(
            request,
            required={
                "protocol",
                "job_id",
                "session_id",
                "sequence",
                "tool_call_id",
                "tool",
                "params",
            },
            label="authenticated broker RPC request",
        )
        protocol = _bounded_string(params["protocol"], "RPC protocol", 128)
        if protocol != RPC_PROTOCOL:
            raise BrokerError("RPC request has the wrong protocol")
        if params["job_id"] != self.job_id or params["session_id"] != self.session_id:
            raise BrokerError("RPC request crosses its bound Job or session")
        return self._execute_tool_call(
            tool_name=params["tool"],
            call_id=params["tool_call_id"],
            value=params["params"],
            sequence=params["sequence"],
        )

    def append_rpc_event(self, event: dict[str, Any]) -> None:
        if not isinstance(event, dict):
            raise BrokerError("RPC event must be a JSON object")
        payload = dict(event)
        payload["job_id"] = self.job_id
        payload["session_id"] = self.session_id
        payload.setdefault("at", _utc_now())
        _append_event(self._quota, payload)

    def close(self) -> None:
        with self._lock:
            if self._closed:
                return
            self._closed = True
            try:
                if any(self._lean_scratch.iterdir()):
                    raise BrokerError("Lean check scratch root was not fully cleaned")
                self._journal.close()
            except Exception as exc:
                raise BrokerError(f"cannot seal Pi patch journal: {exc}") from exc
            finally:
                self._journal.dispose()
                self._disposed = True

    def dispose(self) -> None:
        with self._lock:
            if self._disposed:
                return
            self._closed = True
            self._journal.dispose()
            self._disposed = True

    def __enter__(self) -> "BrokerSession":
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        if exc_type is None:
            self.close()
        else:
            self.dispose()


def _open_legacy_journal(
    capability: dict[str, Any],
    artifact_dir: Path,
    quota: SharedArtifactQuota,
) -> PatchJournal:
    try:
        if (artifact_dir / ".pi-patch-journal.lock").exists():
            return PatchJournal.open_existing(
                artifact_dir,
                capability["job_id"],
                capability["session_id"],
                quota=quota,
            )
        return PatchJournal.create(
            artifact_dir,
            capability["job_id"],
            capability["session_id"],
            quota=quota,
        )
    except (PatchJournalError, PiQuotaError) as exc:
        raise BrokerError(f"cannot open legacy Pi patch journal: {exc}") from exc


def execute_tool(
    *,
    capability_path: Path,
    capability_sha256: str,
    tool_name: str,
    call_id: str,
    value: Any,
) -> dict[str, Any]:
    """Compatibility entry point; production execution uses ``BrokerSession`` RPC."""

    capability = _load_capability(capability_path, capability_sha256)
    _task, _job, root, artifact_dir = _validate_live(capability)
    quota = _quota_for_capability(capability, artifact_dir)
    journal = _open_legacy_journal(capability, artifact_dir, quota)
    try:
        result = _execute_bound_tool(
            capability=capability,
            root=root,
            artifact_dir=artifact_dir,
            quota=quota,
            journal=journal,
            tool_name=tool_name,
            call_id=call_id,
            value=value,
        )
        return {"ok": True, **result}
    finally:
        journal.dispose()


def read_tool_input() -> Any:
    chunks: list[bytes] = []
    size = 0
    while True:
        chunk = os.read(0, min(64 * 1024, MAX_TOOL_INPUT_BYTES + 1 - size))
        if not chunk:
            break
        chunks.append(chunk)
        size += len(chunk)
        if size > MAX_TOOL_INPUT_BYTES:
            raise BrokerError("tool input exceeds byte cap")
    data = b"".join(chunks)
    try:
        return json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BrokerError("tool input is not UTF-8 JSON") from exc
