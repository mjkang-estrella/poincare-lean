"""Shared, append-only disk quota for one Pi Job artifact tree.

All trusted Pi writers use the same ``.artifact.lock`` as ``ArtifactStore``.
The normal limit deliberately leaves a small terminal reserve so a quota
failure can still be represented by a sealed, minimal result.
"""

from __future__ import annotations

import hashlib
import os
import stat
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterator

import fcntl


class PiQuotaError(RuntimeError):
    """Raised when a Pi artifact mutation is unsafe or over budget."""


TERMINAL_RESERVE_BYTES = 64 * 1024


def _relative(raw: str) -> Path:
    parsed = PurePosixPath(raw)
    if (
        parsed.is_absolute()
        or not parsed.parts
        or any(part in {"", ".", ".."} for part in parsed.parts)
        or "\\" in raw
        or "\x00" in raw
    ):
        raise PiQuotaError(f"unsafe Pi artifact path: {raw!r}")
    if parsed.as_posix() == ".artifact.lock":
        raise PiQuotaError("the shared artifact lock path is reserved")
    return Path(*parsed.parts)


@dataclass(frozen=True)
class QuotaWrite:
    relative_path: str
    sha256: str
    size_bytes: int


class SharedArtifactQuota:
    """Serialize and account every trusted Pi artifact write.

    ``emergency=True`` is accepted only for terminal result files and consumes
    the reserve that normal stream/broker/runtime writes cannot use.
    """

    def __init__(self, root: Path, max_bytes: int) -> None:
        if isinstance(max_bytes, bool) or not isinstance(max_bytes, int) or max_bytes < 1:
            raise PiQuotaError("Pi artifact quota must be a positive integer")
        lexical = Path(root).expanduser().absolute()
        if lexical.is_symlink():
            raise PiQuotaError("Pi artifact root must not be a symlink")
        self.root = lexical.resolve(strict=True)
        if not self.root.is_dir():
            raise PiQuotaError("Pi artifact root must be a directory")
        self.max_bytes = max_bytes
        self.normal_limit = max(0, max_bytes - min(TERMINAL_RESERVE_BYTES, max_bytes // 8))
        with self._locked():
            self._check_unlocked(0, emergency=False)

    @contextmanager
    def _locked(self) -> Iterator[None]:
        lock = self.root / ".artifact.lock"
        flags = os.O_RDWR | os.O_CREAT
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        try:
            descriptor = os.open(lock, flags, 0o600)
        except OSError as exc:
            raise PiQuotaError(f"cannot open shared artifact lock: {exc}") from exc
        try:
            opened = os.fstat(descriptor)
            lexical = os.lstat(lock)
            if (
                not stat.S_ISREG(opened.st_mode)
                or stat.S_ISLNK(lexical.st_mode)
                or (opened.st_dev, opened.st_ino) != (lexical.st_dev, lexical.st_ino)
            ):
                raise PiQuotaError("shared artifact lock is unsafe")
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            yield
        finally:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            finally:
                os.close(descriptor)

    def _size_unlocked(self) -> int:
        total = 0
        for directory, dirnames, filenames in os.walk(self.root, followlinks=False):
            base = Path(directory)
            for name in dirnames:
                candidate = base / name
                if candidate.is_symlink():
                    raise PiQuotaError(f"Pi artifact tree contains a symlink: {candidate}")
            for name in filenames:
                candidate = base / name
                if candidate.is_symlink() or not candidate.is_file():
                    raise PiQuotaError(f"Pi artifact tree contains an unsafe file: {candidate}")
                total += candidate.stat(follow_symlinks=False).st_size
        return total

    def _check_unlocked(self, additional: int, *, emergency: bool) -> None:
        if additional < 0:
            raise PiQuotaError("Pi artifact quota accounting cannot be negative")
        limit = self.max_bytes if emergency else self.normal_limit
        current = self._size_unlocked()
        if current + additional > limit:
            kind = "terminal" if emergency else "normal"
            raise PiQuotaError(
                f"Pi {kind} artifact quota exceeded: {current} + {additional} > {limit} bytes"
            )

    def _target_unlocked(self, relative: str) -> Path:
        relpath = _relative(relative)
        current = self.root
        for part in relpath.parent.parts:
            current = current / part
            if current.is_symlink():
                raise PiQuotaError(f"Pi artifact parent is a symlink: {current}")
            try:
                current.mkdir(mode=0o700)
            except FileExistsError:
                if current.is_symlink() or not current.is_dir():
                    raise PiQuotaError(f"Pi artifact parent is unsafe: {current}")
        resolved = current.resolve(strict=True)
        try:
            resolved.relative_to(self.root)
        except ValueError as exc:
            raise PiQuotaError("Pi artifact parent escaped its Job directory") from exc
        return current / relpath.name

    @staticmethod
    def _fsync_directory(path: Path) -> None:
        flags = os.O_RDONLY
        if hasattr(os, "O_DIRECTORY"):
            flags |= os.O_DIRECTORY
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        descriptor = os.open(path, flags)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)

    @staticmethod
    def _file_digest(path: Path) -> tuple[str, int]:
        flags = os.O_RDONLY
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        descriptor = os.open(path, flags)
        try:
            opened = os.fstat(descriptor)
            if not stat.S_ISREG(opened.st_mode):
                raise PiQuotaError("Pi artifact digest target is not regular")
            digest = hashlib.sha256()
            size = 0
            while chunk := os.read(descriptor, 1024 * 1024):
                digest.update(chunk)
                size += len(chunk)
            after = os.fstat(descriptor)
            if (
                opened.st_dev,
                opened.st_ino,
                opened.st_size,
                opened.st_mtime_ns,
                opened.st_ctime_ns,
            ) != (
                after.st_dev,
                after.st_ino,
                after.st_size,
                after.st_mtime_ns,
                after.st_ctime_ns,
            ) or size != opened.st_size:
                raise PiQuotaError("Pi artifact changed while hashing")
            return digest.hexdigest(), size
        finally:
            os.close(descriptor)

    def append(self, relative: str, data: bytes) -> QuotaWrite:
        with self._locked():
            target = self._target_unlocked(relative)
            if target.is_symlink() or (target.exists() and not target.is_file()):
                raise PiQuotaError(f"Pi append target is unsafe: {target}")
            self._check_unlocked(len(data), emergency=False)
            flags = os.O_WRONLY | os.O_CREAT | os.O_APPEND
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            descriptor = os.open(target, flags, 0o600)
            try:
                if not stat.S_ISREG(os.fstat(descriptor).st_mode):
                    raise PiQuotaError("Pi append descriptor is not regular")
                remaining = memoryview(data)
                while remaining:
                    written = os.write(descriptor, remaining)
                    if written <= 0:
                        raise PiQuotaError("short Pi artifact append")
                    remaining = remaining[written:]
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
            self._fsync_directory(target.parent)
            digest, size = self._file_digest(target)
        return QuotaWrite(relative, digest, size)

    def write_once(
        self,
        relative: str,
        data: bytes,
        *,
        emergency: bool = False,
        mode: int = 0o600,
        allow_identical_existing: bool = False,
    ) -> QuotaWrite:
        if emergency and relative not in {
            "pi-run-result.json",
            "evidence-manifest.json",
            "final-report.md",
        }:
            raise PiQuotaError("terminal quota reserve is restricted to final result evidence")
        with self._locked():
            target = self._target_unlocked(relative)
            if target.is_symlink():
                raise PiQuotaError(f"Pi write-once target is a symlink: {target}")
            if target.exists():
                if not allow_identical_existing or not target.is_file():
                    raise PiQuotaError(f"Pi write-once artifact already exists: {target}")
                existing = target.read_bytes()
                if existing != data:
                    raise PiQuotaError(f"Pi write-once artifact changed: {target}")
                return QuotaWrite(relative, hashlib.sha256(existing).hexdigest(), len(existing))
            self._check_unlocked(len(data), emergency=emergency)
            flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            descriptor = os.open(target, flags, mode)
            try:
                with os.fdopen(descriptor, "wb", closefd=True) as handle:
                    handle.write(data)
                    handle.flush()
                    os.fsync(handle.fileno())
                self._fsync_directory(target.parent)
            except Exception:
                raise
        return QuotaWrite(relative, hashlib.sha256(data).hexdigest(), len(data))

    def assert_within_budget(self, *, emergency: bool = False) -> int:
        with self._locked():
            self._check_unlocked(0, emergency=emergency)
            return self._size_unlocked()
