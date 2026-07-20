"""Append-only artifact helpers.

Snapshot and raw HTTP files are write-once.  The event log is opened with
O_APPEND so each request/response fact is retained in order without rewriting
earlier evidence.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

import fcntl


class ArtifactError(RuntimeError):
    """Raised when append-only artifact guarantees cannot be maintained."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def _safe_relative_path(relative: str) -> Path:
    parsed = PurePosixPath(relative)
    if parsed.is_absolute() or not parsed.parts or any(part in {"", ".", ".."} for part in parsed.parts):
        raise ArtifactError(f"unsafe artifact path: {relative!r}")
    return Path(*parsed.parts)


@dataclass(frozen=True)
class WrittenArtifact:
    relative_path: str
    sha256: str
    size_bytes: int


class ArtifactStore:
    """A small append-only store rooted at one Job artifact directory.

    ``max_bytes`` is the Task artifact budget, not a free-space estimate.  It
    covers every regular file already present below the Job directory plus
    each new write or event append.  Recounting before every mutation keeps
    separate fallback invocations from silently exceeding the same budget.
    """

    def __init__(
        self,
        root: Path | str,
        *,
        max_bytes: int | None = None,
        event_context: dict[str, Any] | None = None,
    ):
        if max_bytes is not None and (
            isinstance(max_bytes, bool) or not isinstance(max_bytes, int) or max_bytes <= 0
        ):
            raise ArtifactError("artifact max_bytes must be a positive integer")
        self.max_bytes = max_bytes
        self.event_context = dict(event_context or {})
        if any(not isinstance(key, str) or not key for key in self.event_context):
            raise ArtifactError("artifact event-context keys must be nonempty strings")
        try:
            canonical_json_bytes(self.event_context)
        except (TypeError, ValueError) as exc:
            raise ArtifactError("artifact event context must be JSON serializable") from exc
        self.root = Path(root).expanduser().absolute()
        self._reject_symlink_chain(self.root)
        self.root.mkdir(parents=True, exist_ok=True)
        self._reject_symlink_chain(self.root)
        if self.root.is_symlink() or not self.root.is_dir():
            raise ArtifactError(f"artifact root is not a directory: {self.root}")
        with self._locked():
            self._ensure_budget_unlocked(0)

    @staticmethod
    def _reject_symlink_chain(path: Path) -> None:
        """Reject a symlink in any existing lexical component of ``path``."""

        current = Path(path.anchor)
        for part in path.parts[1:]:
            current = current / part
            if current.is_symlink():
                raise ArtifactError(
                    f"artifact root or parent must not be a symbolic link: {current}"
                )

    def _safe_parent(self, relpath: Path) -> Path:
        current = self.root
        for part in relpath.parent.parts:
            current = current / part
            if current.is_symlink():
                raise ArtifactError(f"artifact parent must not be a symbolic link: {current}")
            try:
                current.mkdir()
            except FileExistsError:
                if current.is_symlink() or not current.is_dir():
                    raise ArtifactError(f"artifact parent is not a safe directory: {current}")
        resolved_root = self.root.resolve(strict=True)
        resolved_parent = current.resolve(strict=True)
        try:
            resolved_parent.relative_to(resolved_root)
        except ValueError as exc:
            raise ArtifactError(f"artifact parent escapes root: {relpath.as_posix()!r}") from exc
        return current

    @contextmanager
    def _locked(self):
        lock_path = self.root / ".artifact.lock"
        flags = os.O_RDWR | os.O_CREAT
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        try:
            descriptor = os.open(lock_path, flags, 0o600)
        except OSError as exc:
            raise ArtifactError(f"cannot open safe artifact lock: {exc}") from exc
        try:
            opened = os.fstat(descriptor)
            lexical = os.lstat(lock_path)
            if (
                not stat.S_ISREG(opened.st_mode)
                or stat.S_ISLNK(lexical.st_mode)
                or (opened.st_dev, opened.st_ino) != (lexical.st_dev, lexical.st_ino)
            ):
                raise ArtifactError("artifact lock is not a stable regular file")
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            yield
        finally:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            finally:
                os.close(descriptor)

    @staticmethod
    def _read_existing(target: Path) -> bytes:
        flags = os.O_RDONLY
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        try:
            descriptor = os.open(target, flags)
        except OSError as exc:
            raise ArtifactError(f"cannot safely read existing artifact {target}: {exc}") from exc
        try:
            opened = os.fstat(descriptor)
            if not stat.S_ISREG(opened.st_mode):
                raise ArtifactError(f"artifact target is not a regular file: {target}")
            chunks: list[bytes] = []
            while chunk := os.read(descriptor, 1024 * 1024):
                chunks.append(chunk)
            lexical = os.lstat(target)
            if stat.S_ISLNK(lexical.st_mode) or (
                opened.st_dev,
                opened.st_ino,
            ) != (lexical.st_dev, lexical.st_ino):
                raise ArtifactError(f"artifact target changed while reading: {target}")
            return b"".join(chunks)
        finally:
            os.close(descriptor)

    def _current_size_unlocked(self) -> int:
        total = 0

        def walk_error(exc: OSError) -> None:
            raise ArtifactError(f"cannot inspect artifact directory: {exc}") from exc

        for directory, dirnames, filenames in os.walk(
            self.root, followlinks=False, onerror=walk_error
        ):
            base = Path(directory)
            for name in dirnames:
                candidate = base / name
                if candidate.is_symlink():
                    raise ArtifactError(
                        f"artifact directory must not contain symbolic links: {candidate}"
                    )
            for name in filenames:
                candidate = base / name
                if candidate.is_symlink() or not candidate.is_file():
                    raise ArtifactError(
                        f"artifact directory contains an unsafe file: {candidate}"
                    )
                try:
                    total += candidate.stat().st_size
                except OSError as exc:
                    raise ArtifactError(f"cannot size artifact {candidate}: {exc}") from exc
        return total

    def _ensure_budget_unlocked(self, additional_bytes: int) -> None:
        if additional_bytes < 0:
            raise ArtifactError("artifact budget accounting cannot be negative")
        if self.max_bytes is None:
            return
        current = self._current_size_unlocked()
        if current + additional_bytes > self.max_bytes:
            raise ArtifactError(
                "Task artifact disk budget exceeded: "
                f"{current} existing + {additional_bytes} new > {self.max_bytes} bytes"
            )

    def write_once(
        self,
        relative: str,
        data: bytes,
        *,
        mode: int = 0o600,
        allow_identical_existing: bool = False,
    ) -> WrittenArtifact:
        relpath = _safe_relative_path(relative)
        if relpath.as_posix() == ".artifact.lock":
            raise ArtifactError("the artifact lock path is reserved")
        with self._locked():
            target = self._safe_parent(relpath) / relpath.name
            if target.is_symlink():
                raise ArtifactError(f"artifact target must not be a symbolic link: {target}")

            # Check while holding the per-Job lock so two evidence writers
            # cannot both pass the same disk-budget recount.
            if not target.exists():
                self._ensure_budget_unlocked(len(data))

            flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            try:
                fd = os.open(target, flags, mode)
            except FileExistsError as exc:
                if target.is_symlink() or not target.is_file():
                    raise ArtifactError(f"artifact target is not a regular file: {target}") from exc
                existing = self._read_existing(target)
                if allow_identical_existing and existing == data:
                    self._ensure_budget_unlocked(0)
                    return WrittenArtifact(relative, sha256_bytes(existing), len(existing))
                qualifier = " with different content" if allow_identical_existing else ""
                raise ArtifactError(
                    f"append-only artifact already exists{qualifier}: {target}"
                ) from exc
            try:
                with os.fdopen(fd, "wb", closefd=True) as handle:
                    handle.write(data)
                    handle.flush()
                    os.fsync(handle.fileno())
            except Exception:
                # Retain partial output as evidence. Append-only means a failed
                # writer may not erase or replace bytes already placed on disk.
                raise
        return WrittenArtifact(relative, sha256_bytes(data), len(data))

    def write_json_once(self, relative: str, value: Any) -> WrittenArtifact:
        return self.write_once(relative, canonical_json_bytes(value))

    def inspect_existing(self, relative: str) -> WrittenArtifact:
        """Hash one existing regular artifact while holding the Job lock."""

        relpath = _safe_relative_path(relative)
        if relpath.as_posix() == ".artifact.lock":
            raise ArtifactError("the artifact lock path is reserved")
        with self._locked():
            target = self._safe_parent(relpath) / relpath.name
            if not target.exists() or target.is_symlink() or not target.is_file():
                raise ArtifactError(f"artifact does not exist as a safe regular file: {target}")
            content = self._read_existing(target)
        return WrittenArtifact(relative, sha256_bytes(content), len(content))

    def append_event(self, event: dict[str, Any]) -> WrittenArtifact:
        event = dict(event)
        for key, value in self.event_context.items():
            if key in event and event[key] != value:
                raise ArtifactError(f"event attempted to override bound context key {key!r}")
            event[key] = value
        data = (
            json.dumps(event, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
            + "\n"
        ).encode("utf-8")
        with self._locked():
            target = self._safe_parent(Path("events.jsonl")) / "events.jsonl"
            if target.is_symlink() or (target.exists() and not target.is_file()):
                raise ArtifactError(f"event log is not a regular file: {target}")
            self._ensure_budget_unlocked(len(data))
            flags = os.O_WRONLY | os.O_CREAT | os.O_APPEND
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            fd = os.open(target, flags, 0o600)
            try:
                written = os.write(fd, data)
                os.fsync(fd)
            finally:
                os.close(fd)
        if written != len(data):
            raise ArtifactError(f"short append to {target}: {written} of {len(data)} bytes")
        return WrittenArtifact("events.jsonl", sha256_bytes(data), len(data))
