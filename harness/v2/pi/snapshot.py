"""Deterministic, bounded prompt snapshots for Pi-backed proof Jobs."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

from harness.v2.runtime.validation import RecordValidationError, validate_task


MAX_CONTEXT_FILE_BYTES = 2 * 1024 * 1024
MAX_CONTEXT_TOTAL_BYTES = 8 * 1024 * 1024

WORKER_CONTRACT = """You are Leanstral running inside one bounded Pi session for one Harness v2 Job.

Authority and safety:
- Work only on the immutable Task below and only through the six tools presented by Pi.
- You may inspect only Task context, search named Task context, apply a scoped patch, run an allowlisted Lean check, inspect the resulting git diff, or report an exact blocker.
- Never ask for or attempt shell, SSH, unrestricted filesystem access, Git commit/push/merge, branch or worktree management, worktree deletion, Docker, Ray, tmux, or model-service management.
- Do not weaken or reinterpret the frozen target. Do not add sorry, admit, axioms, postulates, native_decide, vacuous wrappers, or alternate final targets.
- A passing check is evidence for Codex to review; it is not acceptance. Only Codex may independently gate, accept, or commit the Job.
- If the Task cannot be completed within scope, call report_blocked with the exact Lean type/error, attempted routes, and strongest verified partial result, then give a concise final report.

Work iteratively: inspect the smallest necessary context, patch only the allowed file, run focused allowlisted checks, inspect the diff, and either report the result or an exact blocker.

Your final response must contain:
1. Result
2. Files changed
3. Lean checks requested and outcomes
4. Blocker (exact type/error, or NONE)
5. Confidence and unresolved risks
"""


class SnapshotError(RuntimeError):
    """Raised when a Task snapshot is invalid, unsafe, or over budget."""


@dataclass(frozen=True)
class ContextEntry:
    path: str
    sha256: str
    size_bytes: int
    content: bytes


@dataclass(frozen=True)
class PiPromptSnapshot:
    prompt: str
    prompt_sha256: str
    context_sha256: str
    manifest: dict[str, Any]
    entries: tuple[ContextEntry, ...]


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _normalize_relative(raw: str) -> str:
    path = PurePosixPath(raw)
    if (
        path.is_absolute()
        or not path.parts
        or any(part in {"", ".", ".."} for part in path.parts)
        or "\\" in raw
        or "\x00" in raw
    ):
        raise SnapshotError(f"unsafe repository-relative path: {raw!r}")
    return path.as_posix()


def _reject_symlink_chain(root: Path, candidate: Path) -> None:
    current = root
    relative = candidate.relative_to(root)
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise SnapshotError(f"context path contains a symbolic link: {relative.as_posix()}")


def validate_snapshot_task(task: Any) -> dict[str, Any]:
    try:
        return validate_task(task)
    except RecordValidationError as exc:
        raise SnapshotError(f"invalid Harness v2 Task: {exc}") from exc


def load_task_file(path: Path | str) -> dict[str, Any]:
    lexical = Path(path).expanduser().absolute()
    if lexical.is_symlink() or not lexical.is_file():
        raise SnapshotError(f"Task JSON must be a regular non-symlink file: {lexical}")
    try:
        value = json.loads(lexical.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SnapshotError(f"cannot read Task JSON {lexical}: {exc}") from exc
    return validate_snapshot_task(value)


def _read_context(task: dict[str, Any], worktree: Path) -> tuple[ContextEntry, ...]:
    raw_paths = task["context"]["files"]
    paths = [_normalize_relative(value) for value in raw_paths]
    if len(set(paths)) != len(paths):
        raise SnapshotError("Task context.files contains duplicate paths")

    entries: list[ContextEntry] = []
    total = 0
    for relative in sorted(paths):
        candidate = worktree / Path(*PurePosixPath(relative).parts)
        _reject_symlink_chain(worktree, candidate)
        try:
            resolved = candidate.resolve(strict=True)
            resolved.relative_to(worktree)
        except (OSError, ValueError) as exc:
            raise SnapshotError(f"context file escapes or is missing: {relative}") from exc
        if not resolved.is_file():
            raise SnapshotError(f"context path is not a regular file: {relative}")
        try:
            content = resolved.read_bytes()
        except OSError as exc:
            raise SnapshotError(f"cannot read context file {relative}: {exc}") from exc
        if len(content) > MAX_CONTEXT_FILE_BYTES:
            raise SnapshotError(
                f"context file exceeds {MAX_CONTEXT_FILE_BYTES} bytes: {relative}"
            )
        total += len(content)
        if total > MAX_CONTEXT_TOTAL_BYTES:
            raise SnapshotError(
                f"Task context exceeds aggregate {MAX_CONTEXT_TOTAL_BYTES}-byte cap"
            )
        entries.append(
            ContextEntry(relative, _sha256(content), len(content), content)
        )
    return tuple(entries)


def _aggregate_context(entries: tuple[ContextEntry, ...]) -> str:
    digest = hashlib.sha256()
    digest.update(b"poincare-harness-v2-context\0")
    for entry in entries:
        encoded_path = entry.path.encode("utf-8")
        digest.update(len(encoded_path).to_bytes(8, "big"))
        digest.update(encoded_path)
        digest.update(len(entry.content).to_bytes(8, "big"))
        digest.update(entry.content)
    return digest.hexdigest()


def _render_prompt(
    task: dict[str, Any], entries: tuple[ContextEntry, ...], context_sha256: str
) -> str:
    objective = task["objective"]
    lines = [
        "# Poincare Harness v2 Pi Job",
        "",
        "## Immutable worker contract",
        "",
        WORKER_CONTRACT.rstrip(),
        "",
        "## Frozen Task",
        "",
        f"Task: {task['id']} revision {task['revision']}",
        f"Base commit: {task['base_commit']}",
        f"Title: {objective['title']}",
        "Statement:",
        objective["statement"],
        "Frozen Lean type:",
        objective.get("frozen_lean_type", "NOT_PROVIDED"),
        "Deliverables:",
        json.dumps(objective["deliverables"], ensure_ascii=False, indent=2),
        "",
        "## Scope",
        "",
        "Allowed paths:",
        json.dumps(task["scope"]["allowed_paths"], ensure_ascii=False, indent=2),
        "Forbidden paths:",
        json.dumps(task["scope"]["forbidden_paths"], ensure_ascii=False, indent=2),
        "",
        "## Named symbols",
        "",
        json.dumps(task["context"]["symbols"], ensure_ascii=False, indent=2),
        "",
        "## Acceptance contract",
        "",
        json.dumps(task["acceptance"], ensure_ascii=False, indent=2, sort_keys=True),
        "",
        "`lean_check` accepts only the Lean/lake entries above, selected by zero-based command_index. Codex independently runs the full acceptance contract.",
        "",
        "## Stop conditions",
        "",
        json.dumps(task["stop_conditions"], ensure_ascii=False, indent=2),
        "",
        "## Immutable context snapshot",
        "",
        f"Aggregate SHA-256: {context_sha256}",
    ]
    for entry in entries:
        try:
            decoded = entry.content.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise SnapshotError(f"context file is not UTF-8: {entry.path}") from exc
        fence = "lean" if entry.path.endswith(".lean") else "text"
        lines.extend(
            [
                "",
                f"### `{entry.path}`",
                f"SHA-256: `{entry.sha256}`; bytes: {entry.size_bytes}",
                "",
                f"```{fence}",
                decoded.rstrip("\n"),
                "```",
            ]
        )
    # Pi 0.80.10's readPipedStdin() applies JavaScript String.trim() before it
    # constructs the initial user message.  Keep the frozen transport text
    # already canonical so the Job hash binds the bytes the model actually
    # receives instead of a pre-trim variant.
    prompt = "\n".join(lines)
    if prompt != prompt.strip():
        raise SnapshotError("rendered Pi prompt is not transport-canonical")
    return prompt


def build_snapshot(task: dict[str, Any], worktree: Path | str) -> PiPromptSnapshot:
    task = validate_snapshot_task(task)
    lexical_root = Path(worktree).expanduser().absolute()
    if lexical_root.is_symlink():
        raise SnapshotError(f"worktree must not be a symbolic link: {lexical_root}")
    try:
        root = lexical_root.resolve(strict=True)
    except OSError as exc:
        raise SnapshotError(f"cannot resolve worktree {lexical_root}: {exc}") from exc
    if not root.is_dir():
        raise SnapshotError(f"worktree is not a directory: {root}")
    entries = _read_context(task, root)
    context_sha256 = _aggregate_context(entries)
    prompt = _render_prompt(task, entries, context_sha256)
    manifest = {
        "schema_version": "2.0",
        "aggregate_sha256": context_sha256,
        "files": [
            {
                "path": entry.path,
                "sha256": entry.sha256,
                "size_bytes": entry.size_bytes,
            }
            for entry in entries
        ],
    }
    return PiPromptSnapshot(
        prompt=prompt,
        prompt_sha256=_sha256(prompt.encode("utf-8")),
        context_sha256=context_sha256,
        manifest=manifest,
        entries=entries,
    )
