"""Deterministic Task and prompt snapshot construction."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import tempfile
import time
from collections.abc import Iterable
from dataclasses import dataclass, replace
from fnmatch import fnmatchcase
from pathlib import Path, PurePosixPath
from typing import Any

from harness.v2.runtime.validation import (
    RecordValidationError,
    reject_secrets,
    validate_task,
    validate_statement_context_bytes,
    validate_statement_pinned_sources,
)

from .artifacts import ArtifactStore, WrittenArtifact, canonical_json_bytes, sha256_bytes
from .secrets import secret_kind


MAX_CONTEXT_FILE_BYTES = 2 * 1024 * 1024
MAX_CONTEXT_TOTAL_BYTES = 8 * 1024 * 1024
MAX_GIT_DIAGNOSTIC_BYTES = 8 * 1024 * 1024
MAX_TASK_BYTES = 2 * 1024 * 1024


WORKER_CONTRACT = """You are Leanstral, a bounded proof worker for an unfinished Lean formalization.

Authority and safety:
- Work only on the immutable Task stated below.
- Treat every context file as read-only evidence.
- Propose proof-bearing source text or a precise blocked report; do not claim that you edited files.
- Do not merge, commit, change branches or worktrees, manage endpoints, Ray, GPUs, tmux, or other jobs.
- Do not weaken or reinterpret the frozen target.
- Do not introduce sorry, admit, axioms, postulates, native_decide, vacuous wrappers, or alternate final targets.
- A green root import is not proof of the Poincare conjecture.
- The Codex GPT orchestrator independently reviews, applies, compiles, gates, and accepts any proposal.

Return exactly these sections:
1. Analysis
2. Proposed patch (unified diff, or `NONE`)
3. Expected checks
4. Blocker (exact Lean type/error if blocked, or `NONE`)
5. Confidence and unresolved risks
"""


class SnapshotError(RuntimeError):
    """Raised for an invalid Task or unsafe context path."""


@dataclass(frozen=True)
class ContextEntry:
    path: str
    sha256: str
    size_bytes: int
    content: bytes


@dataclass(frozen=True)
class PromptSnapshot:
    task: dict[str, Any]
    prompt: str
    prompt_sha256: str
    context_sha256: str
    context_entries: tuple[ContextEntry, ...]
    artifacts: tuple[WrittenArtifact, ...]


def _check_deadline(deadline: float | None) -> None:
    if deadline is not None and time.monotonic() >= deadline:
        raise SnapshotError("fallback wall-clock deadline exhausted during snapshot")


def _read_regular_bounded(
    path: Path,
    *,
    maximum_bytes: int,
    label: str,
    deadline: float | None = None,
) -> bytes:
    absolute = path.expanduser().absolute()
    directory_flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        directory_flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        directory_flags |= os.O_NOFOLLOW
    file_flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        file_flags |= os.O_NOFOLLOW
    parent_descriptor: int | None = None
    try:
        parent_descriptor = os.open(absolute.anchor, directory_flags)
        for component in absolute.parts[1:-1]:
            child = os.open(component, directory_flags, dir_fd=parent_descriptor)
            os.close(parent_descriptor)
            parent_descriptor = child
        descriptor = os.open(
            absolute.parts[-1],
            file_flags,
            dir_fd=parent_descriptor,
        )
    except OSError as exc:
        raise SnapshotError(
            f"cannot safely open {label} without following links: {exc}"
        ) from exc
    finally:
        if parent_descriptor is not None:
            os.close(parent_descriptor)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise SnapshotError(f"{label} is not a regular file")
        if before.st_size > maximum_bytes:
            raise SnapshotError(f"{label} exceeds {maximum_bytes}-byte cap")
        chunks: list[bytes] = []
        total = 0
        while True:
            _check_deadline(deadline)
            chunk = os.read(descriptor, min(1024 * 1024, maximum_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
            if total > maximum_bytes:
                raise SnapshotError(f"{label} exceeds {maximum_bytes}-byte cap")
        after = os.fstat(descriptor)
        stable = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
        if any(getattr(before, field) != getattr(after, field) for field in stable):
            raise SnapshotError(f"{label} changed while it was read")
        try:
            lexical = os.lstat(absolute)
        except OSError as exc:
            raise SnapshotError(f"cannot re-inspect {label} after reading: {exc}") from exc
        if stat.S_ISLNK(lexical.st_mode) or (
            lexical.st_dev,
            lexical.st_ino,
        ) != (after.st_dev, after.st_ino):
            raise SnapshotError(f"{label} changed or became a symbolic link")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _reject_symlink_components(repo_root: Path, candidate: Path, label: str) -> None:
    try:
        relative = candidate.relative_to(repo_root)
    except ValueError as exc:
        raise SnapshotError(f"{label} escapes repository") from exc
    current = repo_root
    for part in relative.parts:
        current /= part
        try:
            mode = os.lstat(current).st_mode
        except OSError as exc:
            raise SnapshotError(f"cannot inspect {label}: {exc}") from exc
        if stat.S_ISLNK(mode):
            raise SnapshotError(f"{label} contains a symbolic link: {current}")


def _load_task(
    task_path: Path,
    repo_root: Path,
    *,
    deadline: float | None = None,
) -> dict[str, Any]:
    _check_deadline(deadline)
    lexical = task_path.expanduser().absolute()
    if lexical.is_symlink():
        raise SnapshotError(f"Task JSON must not be a symbolic link: {lexical}")
    resolved = lexical.resolve(strict=True)
    try:
        resolved.relative_to(repo_root)
    except ValueError as exc:
        raise SnapshotError(f"Task JSON must be inside the repository: {resolved}") from exc
    if not resolved.is_file():
        raise SnapshotError(f"Task JSON is not a regular file: {resolved}")
    try:
        data = _read_regular_bounded(
            resolved,
            maximum_bytes=MAX_TASK_BYTES,
            label=f"Task JSON {resolved}",
            deadline=deadline,
        )
        value = json.loads(data.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SnapshotError(f"cannot load Task JSON {resolved}: {exc}") from exc
    if not isinstance(value, dict):
        raise SnapshotError("Task JSON must be an object")
    return value


def _require_task_shape(task: dict[str, Any]) -> None:
    try:
        validate_task(task)
    except RecordValidationError as exc:
        raise SnapshotError(f"invalid Harness v2 Task: {exc}") from exc


def _normalize_context_path(raw: str) -> str:
    path = PurePosixPath(raw)
    if path.is_absolute() or not path.parts or any(part in {"", ".", ".."} for part in path.parts):
        raise SnapshotError(f"unsafe context path: {raw!r}")
    return path.as_posix()


def _git(
    repo_root: Path,
    *arguments: str,
    deadline: float | None = None,
) -> bytes:
    _check_deadline(deadline)
    # Do not inherit GIT_DIR, GIT_WORK_TREE, config injection, hooks, or other
    # ambient Git controls from the orchestrator shell.  The fallback only
    # needs a binary search path and deterministic locale for fixed read-only
    # repository checks.
    env = {
        "PATH": os.environ.get("PATH", os.defpath),
        "LANG": "C",
        "LC_ALL": "C",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_PAGER": "cat",
        "PAGER": "cat",
    }
    command = (
        "git",
        "-c",
        "core.fsmonitor=false",
        "-c",
        f"core.hooksPath={os.devnull}",
        "-C",
        str(repo_root),
        *arguments,
    )
    try:
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            timeout_seconds = 30.0
            if deadline is not None:
                timeout_seconds = min(timeout_seconds, max(0.001, deadline - time.monotonic()))
            result = subprocess.run(
                command,
                check=False,
                stdin=subprocess.DEVNULL,
                stdout=stdout,
                stderr=stderr,
                timeout=timeout_seconds,
                env=env,
            )
            stdout.seek(0, os.SEEK_END)
            stdout_size = stdout.tell()
            if stdout_size > MAX_GIT_DIAGNOSTIC_BYTES:
                raise SnapshotError("Git repository check exceeded its output cap")
            stdout.seek(0)
            output = stdout.read()
            stderr.seek(0)
            error_output = stderr.read(2048)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SnapshotError(f"fixed Git repository check failed: {exc}") from exc
    if result.returncode != 0:
        detail = error_output.decode("utf-8", "replace").strip()
        raise SnapshotError(f"fixed Git repository check failed: {detail or result.returncode}")
    _check_deadline(deadline)
    return output


def _dirty_paths(status: bytes) -> set[str]:
    records = status.split(b"\0")
    paths: set[str] = set()
    index = 0
    while index < len(records):
        record = records[index]
        index += 1
        if not record:
            continue
        if len(record) < 4 or record[2:3] != b" ":
            raise SnapshotError("Git status returned an unexpected porcelain record")
        try:
            paths.add(record[3:].decode("utf-8"))
        except UnicodeDecodeError as exc:
            raise SnapshotError("dirty repository path is not UTF-8") from exc
        if record[0:1] in {b"R", b"C"} or record[1:2] in {b"R", b"C"}:
            if index >= len(records) or not records[index]:
                raise SnapshotError("Git status returned an incomplete rename record")
            try:
                paths.add(records[index].decode("utf-8"))
            except UnicodeDecodeError as exc:
                raise SnapshotError("dirty repository path is not UTF-8") from exc
            index += 1
    return paths


def _scope_matches(path: str, pattern: str) -> bool:
    if fnmatchcase(path, pattern):
        return True
    if not any(character in pattern for character in "*?["):
        prefix = pattern.rstrip("/") + "/"
        return path.startswith(prefix)
    return False


def _verify_repository_state(
    task: dict[str, Any], repo_root: Path, *, deadline: float | None = None
) -> None:
    top = Path(
        _git(repo_root, "rev-parse", "--show-toplevel", deadline=deadline).decode().strip()
    ).resolve()
    if top != repo_root:
        raise SnapshotError(f"repo_root is not the Git worktree root: {repo_root}")
    head = _git(repo_root, "rev-parse", "HEAD", deadline=deadline).decode(
        "ascii", "strict"
    ).strip()
    if head != task["base_commit"]:
        raise SnapshotError(
            f"Git HEAD does not match Task base_commit: {head} != {task['base_commit']}"
        )

    tracked_raw = _git(repo_root, "ls-files", "-z", deadline=deadline)
    try:
        tracked = {item.decode("utf-8") for item in tracked_raw.split(b"\0") if item}
    except UnicodeDecodeError as exc:
        raise SnapshotError("tracked repository path is not UTF-8") from exc
    context_paths = {_normalize_context_path(raw) for raw in task["context"]["files"]}
    if task["schema_version"] == "2.1":
        context_paths.update(entry["path"] for entry in task["statement_contract"]["definition_files"])
    untracked_context = sorted(context_paths - tracked)
    if untracked_context:
        raise SnapshotError(
            "Task context must be tracked at its base commit: " + ", ".join(untracked_context)
        )

    status = _git(
        repo_root,
        "status",
        "--porcelain=v1",
        "-z",
        "--untracked-files=all",
        deadline=deadline,
    )
    dirty = _dirty_paths(status)
    allowed = task["scope"]["allowed_paths"]
    relevant = sorted(
        path
        for path in dirty
        if path in context_paths
        or any(context.startswith(path.rstrip("/") + "/") for context in context_paths)
        or any(_scope_matches(path, pattern) for pattern in allowed)
    )
    if relevant:
        raise SnapshotError(
            "Task context or allowed scope is dirty before fallback inference: "
            + ", ".join(relevant)
        )


def _read_context(
    task: dict[str, Any],
    repo_root: Path,
    *,
    deadline: float | None = None,
    exact_secrets: Iterable[str | bytes] = (),
) -> tuple[ContextEntry, ...]:
    normalized = [_normalize_context_path(raw) for raw in task["context"]["files"]]
    if len(set(normalized)) != len(normalized):
        raise SnapshotError("Task context.files contains duplicate paths")

    entries: list[ContextEntry] = []
    total_bytes = 0
    for relative in sorted(normalized):
        _check_deadline(deadline)
        candidate = repo_root / Path(*PurePosixPath(relative).parts)
        _reject_symlink_components(repo_root, candidate, f"context file {relative}")
        content = _read_regular_bounded(
            candidate,
            maximum_bytes=MAX_CONTEXT_FILE_BYTES,
            label=f"context file {relative}",
            deadline=deadline,
        )
        total_bytes += len(content)
        if total_bytes > MAX_CONTEXT_TOTAL_BYTES:
            raise SnapshotError(
                f"Task context exceeds aggregate {MAX_CONTEXT_TOTAL_BYTES}-byte cap"
            )
        try:
            decoded = content.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise SnapshotError(f"context file is not UTF-8 text: {relative}") from exc
        try:
            reject_secrets(decoded, f"context.{relative}")
        except RecordValidationError as exc:
            # Never include the matching source text in the error or artifact.
            raise SnapshotError(
                f"context file looks secret-bearing and will not be stored or sent: {relative}"
            ) from exc
        if secret_kind(content, exact_values=exact_secrets) is not None:
            raise SnapshotError(
                f"context file looks secret-bearing and will not be stored or sent: {relative}"
            )
        entries.append(
            ContextEntry(
                path=relative,
                sha256=sha256_bytes(content),
                size_bytes=len(content),
                content=content,
            )
        )
    return tuple(entries)


def _context_aggregate(entries: tuple[ContextEntry, ...]) -> str:
    digest = hashlib.sha256()
    digest.update(b"poincare-harness-v2-context\0")
    for entry in entries:
        path_bytes = entry.path.encode("utf-8")
        digest.update(len(path_bytes).to_bytes(8, "big"))
        digest.update(path_bytes)
        digest.update(len(entry.content).to_bytes(8, "big"))
        digest.update(entry.content)
    return digest.hexdigest()


def _render_prompt(
    task: dict[str, Any], entries: tuple[ContextEntry, ...], context_sha256: str
) -> str:
    objective = task["objective"]
    scope = task["scope"]
    context = task["context"]
    acceptance = task["acceptance"]
    lines = [
        "# Poincare Harness v2 Leanstral Job",
        "",
        "## Immutable worker contract",
        "",
        WORKER_CONTRACT.rstrip(),
        "",
        "## Frozen objective",
        "",
        f"Task: {task['id']} revision {task['revision']}",
        f"Base commit: {task['base_commit']}",
        f"Title: {objective.get('title', '')}",
        "Statement:",
        str(objective.get("statement", "")),
        "Frozen Lean type:",
        (json.dumps(task["statement_contract"]["declarations"], ensure_ascii=False, indent=2)
         if task["schema_version"] == "2.1" else str(objective.get("frozen_lean_type", "NOT_PROVIDED"))),
        "Deliverables:",
        json.dumps(objective.get("deliverables", []), ensure_ascii=False, indent=2),
        "",
        "## Scope",
        "",
        "Allowed paths:",
        json.dumps(scope.get("allowed_paths", []), ensure_ascii=False, indent=2),
        "Forbidden paths:",
        json.dumps(scope.get("forbidden_paths", []), ensure_ascii=False, indent=2),
        "",
        "## Named definitions",
        "",
        json.dumps(context.get("symbols", []), ensure_ascii=False, indent=2),
        "",
        "## Acceptance commands and policy",
        "",
        json.dumps(acceptance, ensure_ascii=False, indent=2, sort_keys=True),
        *(["", "Reviewed statement contract:",
           json.dumps(task["statement_contract"], ensure_ascii=False, indent=2, sort_keys=True)]
          if task["schema_version"] == "2.1" else []),
        "",
        "## Stop conditions",
        "",
        json.dumps(task["stop_conditions"], ensure_ascii=False, indent=2),
        "",
        "## Context snapshot",
        "",
        f"Aggregate SHA-256: {context_sha256}",
    ]
    for entry in entries:
        try:
            decoded = entry.content.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise SnapshotError(f"context file is not UTF-8 text: {entry.path}") from exc
        lines.extend(
            [
                "",
                f"### `{entry.path}`",
                f"SHA-256: `{entry.sha256}`; bytes: {entry.size_bytes}",
                "",
                "```lean" if entry.path.endswith(".lean") else "```text",
                decoded.rstrip("\n"),
                "```",
            ]
        )
    lines.extend(
        [
            "",
            "## Required final report format",
            "",
            "Follow the five-section format in the immutable worker contract. Do not report that any patch was applied.",
            "",
        ]
    )
    return "\n".join(lines)


def compute_prompt_snapshot(
    *,
    task: dict[str, Any],
    repo_root: Path | str,
    deadline: float | None = None,
    exact_secrets: Iterable[str | bytes] = (),
) -> PromptSnapshot:
    _check_deadline(deadline)
    pinned_secrets = tuple(exact_secrets)
    lexical_root = Path(repo_root).expanduser().absolute()
    if lexical_root.is_symlink():
        raise SnapshotError(f"repository root must not be a symbolic link: {lexical_root}")
    root = lexical_root.resolve(strict=True)
    if not root.is_dir():
        raise SnapshotError(f"repository root is not a directory: {root}")
    _require_task_shape(task)
    _verify_repository_state(task, root, deadline=deadline)
    entries = _read_context(
        task,
        root,
        deadline=deadline,
        exact_secrets=pinned_secrets,
    )
    if task["schema_version"] == "2.1":
        try:
            validate_statement_pinned_sources(task["statement_contract"], root)
            validate_statement_context_bytes(
                task["statement_contract"], {entry.path: entry.content for entry in entries}
            )
        except RecordValidationError as error:
            raise SnapshotError(str(error)) from error
    _check_deadline(deadline)
    context_sha256 = _context_aggregate(entries)
    prompt = _render_prompt(task, entries, context_sha256)
    prompt_bytes = prompt.encode("utf-8")
    if secret_kind(prompt_bytes, exact_values=pinned_secrets) is not None:
        raise SnapshotError(
            "rendered fallback prompt looks secret-bearing and will not be stored or sent"
        )
    _check_deadline(deadline)
    return PromptSnapshot(
        task=task,
        prompt=prompt,
        prompt_sha256=sha256_bytes(prompt_bytes),
        context_sha256=context_sha256,
        context_entries=entries,
        artifacts=(),
    )


def _manifest(snapshot: PromptSnapshot) -> dict[str, Any]:
    return {
        "schema_version": "2.0",
        "aggregate_sha256": snapshot.context_sha256,
        "files": [
            {"path": entry.path, "sha256": entry.sha256, "size_bytes": entry.size_bytes}
            for entry in snapshot.context_entries
        ],
    }


def persist_prompt_snapshot(
    snapshot: PromptSnapshot,
    *,
    artifact_dir: Path | str,
    deadline: float | None = None,
    allow_identical_existing: bool = False,
) -> PromptSnapshot:
    _check_deadline(deadline)
    task = snapshot.task
    store = ArtifactStore(
        artifact_dir, max_bytes=task["budget"]["disk_mb"] * 1024 * 1024
    )
    task_artifact = store.write_once(
        "task.json", canonical_json_bytes(task), allow_identical_existing=True
    )
    _check_deadline(deadline)
    manifest_artifact = store.write_once(
        "context-manifest.json",
        canonical_json_bytes(_manifest(snapshot)),
        allow_identical_existing=allow_identical_existing,
    )
    _check_deadline(deadline)
    prompt_artifact = store.write_once(
        "prompt.md",
        snapshot.prompt.encode("utf-8"),
        allow_identical_existing=allow_identical_existing,
    )
    _check_deadline(deadline)
    return replace(
        snapshot,
        artifacts=(task_artifact, manifest_artifact, prompt_artifact),
    )


def build_prompt_snapshot(
    *,
    task_path: Path | str,
    repo_root: Path | str,
    artifact_dir: Path | str,
    deadline: float | None = None,
    exact_secrets: Iterable[str | bytes] = (),
) -> PromptSnapshot:
    _check_deadline(deadline)
    root = Path(repo_root).expanduser().resolve(strict=True)
    if not root.is_dir():
        raise SnapshotError(f"repository root is not a directory: {root}")
    task = _load_task(Path(task_path), root, deadline=deadline)
    snapshot = compute_prompt_snapshot(
        task=task,
        repo_root=root,
        deadline=deadline,
        exact_secrets=exact_secrets,
    )
    return persist_prompt_snapshot(
        snapshot,
        artifact_dir=artifact_dir,
        deadline=deadline,
        allow_identical_existing=False,
    )


__all__ = [
    "ContextEntry",
    "PromptSnapshot",
    "SnapshotError",
    "build_prompt_snapshot",
    "compute_prompt_snapshot",
    "persist_prompt_snapshot",
]
