"""Read-only binding of one fallback attempt to a live Harness v2 Job."""

from __future__ import annotations

import json
import sqlite3
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit, urlunsplit

from harness.v2.runtime.store import SCHEMA_VERSION, HarnessError, HarnessStore
from harness.v2.runtime.validation import RecordValidationError, validate_job

from .artifacts import canonical_json_bytes, sha256_bytes
from .snapshot import (
    MAX_TASK_BYTES,
    _git,
    _read_regular_bounded,
    _verify_repository_state,
)


class BindingError(RuntimeError):
    """Raised when fallback execution is not bound to one live Job."""


@dataclass(frozen=True)
class JobBinding:
    state_dir: Path
    task: dict[str, Any]
    job: dict[str, Any]
    runtime: dict[str, Any]
    worktree: Path
    artifact_dir: Path
    lease_owner: str
    lease_token: int
    endpoint: str
    model: str
    model_revision: str


def _check_deadline(deadline: float | None) -> None:
    if deadline is not None and time.monotonic() >= deadline:
        raise BindingError("fallback wall-clock deadline exhausted during Job binding")


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
        raise BindingError("Leanstral endpoint must be credential-free HTTP(S)")
    path = parsed.path.rstrip("/")
    if not path.endswith("/v1"):
        path += "/v1"
    return urlunsplit((parsed.scheme, parsed.netloc, path, "", ""))


def _resolved_directory(raw: str | Path, label: str) -> Path:
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink():
        raise BindingError(f"{label} must not be a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise BindingError(f"cannot resolve {label}: {exc}") from exc
    if not resolved.is_dir():
        raise BindingError(f"{label} is not a directory")
    return resolved


def _verify_snapshots(binding: JobBinding, *, deadline: float | None) -> None:
    _check_deadline(deadline)
    task_path = binding.artifact_dir / "task.json"
    task_bytes = _read_regular_bounded(
        task_path,
        maximum_bytes=MAX_TASK_BYTES,
        label="runtime Task snapshot",
        deadline=deadline,
    )
    if task_bytes != canonical_json_bytes(binding.task):
        raise BindingError("runtime Task snapshot differs from live SQLite Task")

    job_path = binding.artifact_dir / "job.json"
    job_bytes = _read_regular_bounded(
        job_path,
        maximum_bytes=MAX_TASK_BYTES,
        label="runtime Job snapshot",
        deadline=deadline,
    )
    try:
        job_snapshot = json.loads(job_bytes.decode("utf-8"))
        validate_job(job_snapshot)
    except (UnicodeDecodeError, json.JSONDecodeError, RecordValidationError) as exc:
        raise BindingError(f"runtime Job snapshot is invalid: {exc}") from exc
    if job_snapshot["state"] != "queued" or job_snapshot["gate"] != {"status": "not_run"}:
        raise BindingError("runtime Job snapshot is not the immutable queued source")
    if any(
        name in job_snapshot
        for name in ("started_at", "heartbeat_at", "finished_at", "exit_reason", "accepted_commit")
    ):
        raise BindingError("runtime Job snapshot contains lifecycle fields")
    immutable_fields = (
        "schema_version",
        "id",
        "task_id",
        "task_revision",
        "attempt",
        "backend",
        "artifacts",
    )
    if any(job_snapshot[name] != binding.job[name] for name in immutable_fields):
        raise BindingError("runtime Job snapshot differs from live immutable Job fields")
    for name in ("base_commit", "worktree", "branch"):
        if job_snapshot["workspace"][name] != binding.job["workspace"][name]:
            raise BindingError("runtime Job workspace snapshot differs from live Job")

    database = binding.state_dir / "harness.sqlite3"
    try:
        connection = sqlite3.connect(database.as_uri() + "?mode=ro", uri=True, timeout=5)
        connection.row_factory = sqlite3.Row
        registrations = {
            row["name"]: row
            for row in connection.execute(
                """
                SELECT name, path, sha256 FROM artifact_entries
                WHERE job_id = ? AND name IN ('task_snapshot', 'job_snapshot')
                """,
                (binding.job["id"],),
            ).fetchall()
        }
    except sqlite3.Error as exc:
        raise BindingError(f"cannot verify registered runtime snapshots: {exc}") from exc
    finally:
        if "connection" in locals():
            connection.close()
    expected = {
        "task_snapshot": (task_path, task_bytes),
        "job_snapshot": (job_path, job_bytes),
    }
    if set(registrations) != set(expected):
        raise BindingError("runtime Task/Job snapshot registrations are incomplete")
    for name, (path, content) in expected.items():
        row = registrations[name]
        if row["path"] != str(path) or row["sha256"] != sha256_bytes(content):
            raise BindingError(f"registered {name} path or hash does not match disk evidence")


def bind_live_job(
    *,
    job_id: str,
    state_dir: str | Path,
    lease_owner: str,
    lease_token: int,
    endpoint: str,
    model: str,
    model_revision: str,
    deadline: float | None = None,
    verify_snapshots: bool = True,
) -> JobBinding:
    _check_deadline(deadline)
    if not job_id or not lease_owner.strip():
        raise BindingError("job ID and lease owner are required")
    if isinstance(lease_token, bool) or not isinstance(lease_token, int) or lease_token < 1:
        raise BindingError("lease token must be a positive integer")
    if not model or not model_revision:
        raise BindingError("Leanstral model and model revision are required")
    normalized_endpoint = _normalize_endpoint(endpoint)
    resolved_state = _resolved_directory(state_dir, "Harness state directory")
    try:
        store = HarnessStore(resolved_state)
        if store.schema_version() != SCHEMA_VERSION:
            raise BindingError("Harness state schema is not the current executable version")
        payload = store.get_job(job_id)
        job = payload["job"]
        runtime = payload["runtime"]
        task = store.get_task(job["task_id"])["task"]
    except (HarnessError, sqlite3.Error) as exc:
        raise BindingError(f"cannot load live Harness Job: {exc}") from exc

    if job["state"] != "running" or task["status"] != "active":
        raise BindingError("fallback requires a running Job and active Task")
    if not runtime["lease_active"]:
        raise BindingError("fallback requires an active Job lease")
    if (
        job["workspace"]["lease_owner"] != lease_owner
        or runtime["lease_token"] != lease_token
    ):
        raise BindingError("lease owner or fencing token mismatch")
    expected_scopes = set(task["scope"]["allowed_paths"])
    scopes = runtime["scopes"]
    if {item["path"] for item in scopes} != expected_scopes or any(
        not item["active"]
        or item["owner"] != lease_owner
        or item["lease_token"] != lease_token
        for item in scopes
    ):
        raise BindingError("Job does not hold its exact active Task file-scope lease")
    if (
        job["task_id"] != task["id"]
        or job["task_revision"] != task["revision"]
        or job["workspace"]["base_commit"] != task["base_commit"]
    ):
        raise BindingError("Task identity, revision, or base commit differs from Job")
    backend = job["backend"]
    if backend["kind"] != "leanstral":
        raise BindingError("fallback Job backend must be leanstral")
    if (
        _normalize_endpoint(backend["endpoint"]) != normalized_endpoint
        or backend["model"] != model
        or backend["model_revision"] != model_revision
    ):
        raise BindingError("Job backend endpoint, model, or revision differs from pinned environment")
    if runtime.get("worktree_validation") != "validated":
        raise BindingError("Job worktree was not validated against persisted trusted roots")

    worktree = _resolved_directory(job["workspace"]["worktree"], "Job worktree")
    top = Path(
        _git(worktree, "rev-parse", "--show-toplevel", deadline=deadline).decode().strip()
    ).resolve()
    head = _git(worktree, "rev-parse", "HEAD", deadline=deadline).decode().strip()
    branch = _git(
        worktree,
        "symbolic-ref",
        "--quiet",
        "--short",
        "HEAD",
        deadline=deadline,
    ).decode().strip()
    if top != worktree or head != task["base_commit"] or branch != job["workspace"]["branch"]:
        raise BindingError("worktree root, branch, or HEAD differs from the live Job")
    _verify_repository_state(task, worktree, deadline=deadline)

    artifact_dir = _resolved_directory(
        runtime["artifact_directory"], "Job artifact directory"
    )
    expected_artifact = resolved_state / "jobs" / job_id
    if artifact_dir != expected_artifact:
        raise BindingError("runtime artifact directory is not the exact state/jobs/Job path")
    expected_recorded = f"harness/v2/state/jobs/{job_id}"
    if job["artifacts"]["directory"] != expected_recorded:
        raise BindingError("Job artifact record is not the canonical Harness v2 path")

    binding = JobBinding(
        state_dir=resolved_state,
        task=task,
        job=job,
        runtime=runtime,
        worktree=worktree,
        artifact_dir=artifact_dir,
        lease_owner=lease_owner,
        lease_token=lease_token,
        endpoint=normalized_endpoint,
        model=model,
        model_revision=model_revision,
    )
    if verify_snapshots:
        _verify_snapshots(binding, deadline=deadline)
    _check_deadline(deadline)
    return binding


def assert_binding_live(binding: JobBinding, *, deadline: float | None = None) -> None:
    current = bind_live_job(
        job_id=binding.job["id"],
        state_dir=binding.state_dir,
        lease_owner=binding.lease_owner,
        lease_token=binding.lease_token,
        endpoint=binding.endpoint,
        model=binding.model,
        model_revision=binding.model_revision,
        deadline=deadline,
        verify_snapshots=True,
    )
    if (
        current.task != binding.task
        or current.job["backend"] != binding.job["backend"]
        or current.job["artifacts"] != binding.job["artifacts"]
        or current.worktree != binding.worktree
        or current.artifact_dir != binding.artifact_dir
    ):
        raise BindingError("live Job binding changed during fallback execution")


__all__ = ["BindingError", "JobBinding", "assert_binding_live", "bind_live_job"]
