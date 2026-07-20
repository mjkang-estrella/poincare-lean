"""Tamper-evident, append-only evidence for scoped Pi patch applications.

The trusted broker writes an ``intent`` before it mutates a Job worktree and
then writes exactly one ``commit`` or ``abort`` record.  Patch bytes live in
separate write-once blobs.  The JSONL journal binds those blobs in a strict
hash chain, while a write-once seal closes the journal before replay review.

This module deliberately does not execute Git or a shell.  Replay is driven by
a caller-supplied callback so the orchestrator can use its own isolated
temporary-index implementation.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import stat
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Iterator, Mapping, Protocol, Sequence


class PatchJournalError(RuntimeError):
    """Raised when patch evidence is unsafe, inconsistent, or incomplete."""


JOURNAL_PROTOCOL = "poincare.pi-patch-journal.v1"
SEAL_PROTOCOL = "poincare.pi-patch-journal-seal.v1"
JOURNAL_NAME = "pi-patch-journal.jsonl"
BLOB_DIRECTORY = "pi-patch-blobs"
LOCK_NAME = ".pi-patch-journal.lock"
SEAL_NAME = "pi-patch-journal-seal.json"
ZERO_SHA256 = "0" * 64
MAX_PATCH_BYTES = 8 * 1024 * 1024
MAX_JOURNAL_BYTES = 64 * 1024 * 1024
MAX_ENTRY_BYTES = 1024 * 1024
_ENTRY_DOMAIN = b"poincare-harness-v2-patch-entry-v1\0"
_SEAL_DOMAIN = b"poincare-harness-v2-patch-seal-v1\0"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")

_COMMON_KEYS = {
    "protocol",
    "job_id",
    "session_id",
    "sequence",
    "tool_call_id",
    "paths",
    "patch_sha256",
    "prior_entry_sha256",
    "entry_sha256",
    "state",
}
_COMMIT_KEYS = _COMMON_KEYS | {"before_sha256", "after_sha256"}
_SEAL_KEYS = {
    "protocol",
    "job_id",
    "session_id",
    "entry_count",
    "final_entry_sha256",
    "journal_sha256",
    "seal_sha256",
}


class ArtifactWriter(Protocol):
    """The subset of ``SharedArtifactQuota`` used by the journal."""

    def append(self, relative: str, data: bytes) -> object: ...

    def write_once(
        self,
        relative: str,
        data: bytes,
        *,
        emergency: bool = False,
        mode: int = 0o600,
        allow_identical_existing: bool = False,
    ) -> object: ...


@dataclass(frozen=True)
class PatchIntent:
    """Opaque-enough handle required to resolve one journalled intent."""

    job_id: str
    session_id: str
    sequence: int
    tool_call_id: str
    paths: tuple[str, ...]
    patch_sha256: str


@dataclass(frozen=True)
class CommittedPatch:
    """One verified committed patch and its expected filesystem hashes."""

    intent_sequence: int
    commit_sequence: int
    tool_call_id: str
    paths: tuple[str, ...]
    patch_sha256: str
    before_sha256: dict[str, str]
    after_sha256: dict[str, str]
    patch: bytes


@dataclass(frozen=True)
class ReplayObservation:
    """Hashes observed by the caller immediately before and after replay."""

    before_sha256: Mapping[str, str]
    after_sha256: Mapping[str, str]


@dataclass(frozen=True)
class _ScanResult:
    entries: tuple[dict[str, Any], ...]
    pending: dict[str, Any] | None
    used_tool_call_ids: frozenset[str]
    blobs: dict[int, bytes]
    raw_journal: bytes

    @property
    def next_sequence(self) -> int:
        return len(self.entries) + 1

    @property
    def final_entry_sha256(self) -> str:
        if not self.entries:
            return ZERO_SHA256
        return str(self.entries[-1]["entry_sha256"])


def _canonical_json(payload: Mapping[str, Any]) -> bytes:
    try:
        return json.dumps(
            payload,
            ensure_ascii=True,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise PatchJournalError("patch journal record is not canonical JSON") from exc


def _object_without_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise PatchJournalError(f"patch journal JSON repeats key: {key}")
        result[key] = value
    return result


def _parse_canonical_json(raw: bytes, *, label: str) -> dict[str, Any]:
    try:
        text = raw.decode("utf-8", "strict")
        payload = json.loads(text, object_pairs_hook=_object_without_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PatchJournalError(f"{label} is not valid UTF-8 JSON") from exc
    if not isinstance(payload, dict):
        raise PatchJournalError(f"{label} must be a JSON object")
    if _canonical_json(payload) != raw:
        raise PatchJournalError(f"{label} is not in canonical JSON form")
    return payload


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _require_sha256(value: Any, label: str) -> str:
    if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
        raise PatchJournalError(f"{label} must be a lowercase SHA-256 digest")
    return value


def _require_identifier(value: Any, label: str) -> str:
    if (
        not isinstance(value, str)
        or not value
        or len(value.encode("utf-8")) > 512
        or any(ord(character) < 0x20 or ord(character) == 0x7F for character in value)
    ):
        raise PatchJournalError(f"{label} must be a nonempty bounded identifier")
    return value


def _normalize_path(raw: Any) -> str:
    if not isinstance(raw, str) or not raw or "\x00" in raw or "\\" in raw:
        raise PatchJournalError("journal paths must be nonempty POSIX relative paths")
    parsed = PurePosixPath(raw)
    if (
        parsed.is_absolute()
        or raw.startswith("~")
        or not parsed.parts
        or any(part in {"", ".", ".."} for part in parsed.parts)
    ):
        raise PatchJournalError(f"unsafe journal path: {raw!r}")
    normalized = parsed.as_posix()
    if normalized != raw or len(raw.encode("utf-8")) > 4096:
        raise PatchJournalError(f"journal path is not normalized: {raw!r}")
    return normalized


def _normalize_paths(raw: Any) -> tuple[str, ...]:
    if not isinstance(raw, (list, tuple)) or not raw or len(raw) > 256:
        raise PatchJournalError("paths must be a nonempty bounded array")
    paths = tuple(_normalize_path(item) for item in raw)
    if len(set(paths)) != len(paths):
        raise PatchJournalError("paths must not contain duplicates")
    return paths


def _normalize_hash_map(
    raw: Mapping[str, str] | Any,
    paths: tuple[str, ...],
    label: str,
) -> dict[str, str]:
    if not isinstance(raw, Mapping):
        raise PatchJournalError(f"{label} must be an object")
    if any(not isinstance(key, str) for key in raw):
        raise PatchJournalError(f"{label} contains a non-string path")
    if set(raw) != set(paths) or len(raw) != len(paths):
        raise PatchJournalError(f"{label} must contain exactly the journalled paths")
    return {path: _require_sha256(raw[path], f"{label}[{path}]") for path in paths}


def _entry_digest(entry_without_digest: Mapping[str, Any]) -> str:
    return _sha256(_ENTRY_DOMAIN + _canonical_json(entry_without_digest))


def _seal_digest(seal_without_digest: Mapping[str, Any]) -> str:
    return _sha256(_SEAL_DOMAIN + _canonical_json(seal_without_digest))


def _blob_name(intent_sequence: int, patch_sha256: str) -> str:
    return f"{intent_sequence:012d}-{patch_sha256}.patch"


def _safe_directory_fd(path: Path, label: str) -> tuple[Path, int]:
    lexical = Path(path).expanduser().absolute()
    try:
        metadata = os.lstat(lexical)
    except OSError as exc:
        raise PatchJournalError(f"cannot inspect {label}: {exc}") from exc
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
        raise PatchJournalError(f"{label} must be a real directory")
    flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(lexical, flags)
    except OSError as exc:
        raise PatchJournalError(f"cannot open {label} safely: {exc}") from exc
    opened = os.fstat(descriptor)
    current = os.lstat(lexical)
    if (
        not stat.S_ISDIR(opened.st_mode)
        or stat.S_ISLNK(current.st_mode)
        or (opened.st_dev, opened.st_ino) != (current.st_dev, current.st_ino)
    ):
        os.close(descriptor)
        raise PatchJournalError(f"{label} changed while being opened")
    return lexical.resolve(strict=True), descriptor


def _safe_open_regular(
    directory_fd: int,
    name: str,
    flags: int,
    *,
    label: str,
    mode: int = 0o600,
) -> int:
    if "/" in name or not name:
        raise PatchJournalError(f"unsafe {label} name")
    requested = flags
    if hasattr(os, "O_NOFOLLOW"):
        requested |= os.O_NOFOLLOW
    if hasattr(os, "O_NONBLOCK"):
        # Opening a hostile FIFO must fail validation instead of blocking the
        # trusted broker or verifier before fstat can identify it.
        requested |= os.O_NONBLOCK
    try:
        descriptor = os.open(name, requested, mode, dir_fd=directory_fd)
    except OSError as exc:
        raise PatchJournalError(f"cannot open {label} safely: {exc}") from exc
    try:
        _assert_descriptor_matches(directory_fd, name, descriptor, label=label)
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def _assert_descriptor_matches(
    directory_fd: int,
    name: str,
    descriptor: int,
    *,
    label: str,
) -> None:
    try:
        opened = os.fstat(descriptor)
        lexical = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
    except OSError as exc:
        raise PatchJournalError(f"cannot revalidate {label}: {exc}") from exc
    if (
        not stat.S_ISREG(opened.st_mode)
        or stat.S_ISLNK(lexical.st_mode)
        or opened.st_nlink != 1
        or lexical.st_nlink != 1
        or (opened.st_dev, opened.st_ino) != (lexical.st_dev, lexical.st_ino)
    ):
        raise PatchJournalError(f"{label} is not a private regular file")


def _read_descriptor(descriptor: int, *, label: str, limit: int) -> bytes:
    before = os.fstat(descriptor)
    if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
        raise PatchJournalError(f"{label} is not a private regular file")
    if before.st_size > limit:
        raise PatchJournalError(f"{label} exceeds its byte limit")
    os.lseek(descriptor, 0, os.SEEK_SET)
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = os.read(descriptor, min(1024 * 1024, limit + 1 - total))
        if not chunk:
            break
        chunks.append(chunk)
        total += len(chunk)
        if total > limit:
            raise PatchJournalError(f"{label} exceeds its byte limit")
    after = os.fstat(descriptor)
    if (
        before.st_dev != after.st_dev
        or before.st_ino != after.st_ino
        or before.st_size != after.st_size
        or after.st_size != total
        or after.st_nlink != 1
    ):
        raise PatchJournalError(f"{label} changed while being read")
    return b"".join(chunks)


class _DirectArtifactWriter:
    """Safe test/small-deployment fallback when no shared quota is supplied."""

    def __init__(self, root: Path, root_fd: int) -> None:
        self.root = root
        self._root_fd = root_fd

    def append(self, relative: str, data: bytes) -> None:
        if relative != JOURNAL_NAME:
            raise PatchJournalError("direct append is restricted to the patch journal")
        descriptor = _safe_open_regular(
            self._root_fd,
            JOURNAL_NAME,
            os.O_WRONLY | os.O_APPEND,
            label="patch journal",
        )
        try:
            remaining = memoryview(data)
            while remaining:
                written = os.write(descriptor, remaining)
                if written <= 0:
                    raise PatchJournalError("short patch journal append")
                remaining = remaining[written:]
            os.fsync(descriptor)
            _assert_descriptor_matches(
                self._root_fd,
                JOURNAL_NAME,
                descriptor,
                label="patch journal",
            )
        finally:
            os.close(descriptor)

    def write_once(
        self,
        relative: str,
        data: bytes,
        *,
        emergency: bool = False,
        mode: int = 0o600,
        allow_identical_existing: bool = False,
    ) -> None:
        del emergency, allow_identical_existing
        parsed = PurePosixPath(relative)
        if parsed.parts == (JOURNAL_NAME,) or parsed.parts == (SEAL_NAME,):
            directory_fd = self._root_fd
            name = parsed.name
            label = "patch journal" if name == JOURNAL_NAME else "patch journal seal"
        elif len(parsed.parts) == 2 and parsed.parts[0] == BLOB_DIRECTORY:
            directory_fd = _open_blob_directory(self._root_fd)
            name = parsed.name
            label = "patch blob"
        else:
            raise PatchJournalError("direct write-once path is outside journal artifacts")
        descriptor: int | None = None
        try:
            descriptor = _safe_open_regular(
                directory_fd,
                name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                label=label,
                mode=mode,
            )
            remaining = memoryview(data)
            while remaining:
                written = os.write(descriptor, remaining)
                if written <= 0:
                    raise PatchJournalError(f"short {label} write")
                remaining = remaining[written:]
            os.fsync(descriptor)
            _assert_descriptor_matches(
                directory_fd,
                name,
                descriptor,
                label=label,
            )
        finally:
            if descriptor is not None:
                os.close(descriptor)
            if directory_fd != self._root_fd:
                os.fsync(directory_fd)
                os.close(directory_fd)


def _open_blob_directory(root_fd: int) -> int:
    flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(BLOB_DIRECTORY, flags, dir_fd=root_fd)
    except OSError as exc:
        raise PatchJournalError(f"cannot open patch blob directory safely: {exc}") from exc
    try:
        opened = os.fstat(descriptor)
        lexical = os.stat(BLOB_DIRECTORY, dir_fd=root_fd, follow_symlinks=False)
        if (
            not stat.S_ISDIR(opened.st_mode)
            or stat.S_ISLNK(lexical.st_mode)
            or (opened.st_dev, opened.st_ino) != (lexical.st_dev, lexical.st_ino)
        ):
            raise PatchJournalError("patch blob directory is unsafe")
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def _read_regular_at(directory_fd: int, name: str, *, label: str, limit: int) -> bytes:
    descriptor = _safe_open_regular(
        directory_fd,
        name,
        os.O_RDONLY,
        label=label,
    )
    try:
        data = _read_descriptor(descriptor, label=label, limit=limit)
        _assert_descriptor_matches(
            directory_fd,
            name,
            descriptor,
            label=label,
        )
        return data
    finally:
        os.close(descriptor)


def _set_read_only_at(directory_fd: int, name: str, *, label: str) -> None:
    descriptor = _safe_open_regular(
        directory_fd,
        name,
        os.O_RDONLY,
        label=label,
    )
    try:
        os.fchmod(descriptor, 0o400)
        os.fsync(descriptor)
        _assert_descriptor_matches(
            directory_fd,
            name,
            descriptor,
            label=label,
        )
    finally:
        os.close(descriptor)


def _assert_read_only_at(directory_fd: int, name: str, *, label: str) -> None:
    descriptor = _safe_open_regular(
        directory_fd,
        name,
        os.O_RDONLY,
        label=label,
    )
    try:
        if stat.S_IMODE(os.fstat(descriptor).st_mode) & 0o222:
            raise PatchJournalError(f"{label} is not immutable")
        _assert_descriptor_matches(
            directory_fd,
            name,
            descriptor,
            label=label,
        )
    finally:
        os.close(descriptor)


def _seal_exists(root_fd: int) -> bool:
    try:
        metadata = os.stat(SEAL_NAME, dir_fd=root_fd, follow_symlinks=False)
    except FileNotFoundError:
        return False
    except OSError as exc:
        raise PatchJournalError(f"cannot inspect patch journal seal: {exc}") from exc
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
        raise PatchJournalError("patch journal seal is unsafe")
    return True


def _validate_entry(
    entry: dict[str, Any],
    *,
    expected_job_id: str,
    expected_session_id: str,
    expected_sequence: int,
    expected_prior: str,
) -> None:
    state = entry.get("state")
    expected_keys = _COMMIT_KEYS if state == "commit" else _COMMON_KEYS
    if state not in {"intent", "commit", "abort"}:
        raise PatchJournalError(f"entry {expected_sequence} has an unsupported state")
    if set(entry) != expected_keys:
        raise PatchJournalError(f"entry {expected_sequence} has missing or unknown keys")
    if entry["protocol"] != JOURNAL_PROTOCOL:
        raise PatchJournalError(f"entry {expected_sequence} has the wrong protocol")
    if entry["job_id"] != expected_job_id or entry["session_id"] != expected_session_id:
        raise PatchJournalError(f"entry {expected_sequence} crosses its Job/session boundary")
    if (
        isinstance(entry["sequence"], bool)
        or not isinstance(entry["sequence"], int)
        or entry["sequence"] != expected_sequence
    ):
        raise PatchJournalError(f"entry {expected_sequence} creates a sequence gap")
    _require_identifier(entry["tool_call_id"], "tool_call_id")
    paths = _normalize_paths(entry["paths"])
    _require_sha256(entry["patch_sha256"], "patch_sha256")
    if entry["prior_entry_sha256"] != expected_prior:
        raise PatchJournalError(f"entry {expected_sequence} breaks the prior-entry chain")
    _require_sha256(entry["entry_sha256"], "entry_sha256")
    without_digest = dict(entry)
    claimed = without_digest.pop("entry_sha256")
    if _entry_digest(without_digest) != claimed:
        raise PatchJournalError(f"entry {expected_sequence} has an invalid digest")
    if state == "commit":
        _normalize_hash_map(entry["before_sha256"], paths, "before_sha256")
        _normalize_hash_map(entry["after_sha256"], paths, "after_sha256")


def _scan(root_fd: int, *, job_id: str, session_id: str) -> _ScanResult:
    raw = _read_regular_at(
        root_fd,
        JOURNAL_NAME,
        label="patch journal",
        limit=MAX_JOURNAL_BYTES,
    )
    if raw and not raw.endswith(b"\n"):
        raise PatchJournalError("patch journal is truncated")

    entries: list[dict[str, Any]] = []
    pending: dict[str, Any] | None = None
    used: set[str] = set()
    expected_prior = ZERO_SHA256
    # Splitting only on LF deliberately preserves any CR byte so CRLF or other
    # noncanonical record separators cannot be normalized by the parser.
    lines = raw[:-1].split(b"\n") if raw else []
    for index, line in enumerate(lines, start=1):
        if not line or len(line) > MAX_ENTRY_BYTES:
            raise PatchJournalError(f"patch journal entry {index} is empty or oversized")
        entry = _parse_canonical_json(line, label=f"patch journal entry {index}")
        _validate_entry(
            entry,
            expected_job_id=job_id,
            expected_session_id=session_id,
            expected_sequence=index,
            expected_prior=expected_prior,
        )
        state = entry["state"]
        if state == "intent":
            if pending is not None:
                raise PatchJournalError("patch intents are not serialized")
            if entry["tool_call_id"] in used:
                raise PatchJournalError("a tool_call_id has more than one intent")
            used.add(entry["tool_call_id"])
            pending = entry
        else:
            if pending is None:
                raise PatchJournalError(f"{state} has no unresolved intent")
            for key in ("tool_call_id", "paths", "patch_sha256"):
                if entry[key] != pending[key]:
                    raise PatchJournalError(f"{state} does not resolve the pending intent")
            pending = None
        entries.append(entry)
        expected_prior = entry["entry_sha256"]

    blob_fd = _open_blob_directory(root_fd)
    try:
        try:
            names = sorted(os.listdir(blob_fd))
        except OSError as exc:
            raise PatchJournalError(f"cannot enumerate patch blobs: {exc}") from exc
        expected_names: dict[str, tuple[int, str]] = {}
        for entry in entries:
            if entry["state"] == "intent":
                name = _blob_name(entry["sequence"], entry["patch_sha256"])
                expected_names[name] = (entry["sequence"], entry["patch_sha256"])
        if names != sorted(expected_names):
            raise PatchJournalError("patch blob directory does not exactly match journal intents")
        blobs: dict[int, bytes] = {}
        for name in names:
            sequence, expected_digest = expected_names[name]
            _assert_read_only_at(blob_fd, name, label=f"patch blob {name}")
            data = _read_regular_at(
                blob_fd,
                name,
                label=f"patch blob {name}",
                limit=MAX_PATCH_BYTES,
            )
            if not data or _sha256(data) != expected_digest:
                raise PatchJournalError(f"patch blob {name} is empty or has the wrong digest")
            blobs[sequence] = data
    finally:
        os.close(blob_fd)
    return _ScanResult(tuple(entries), pending, frozenset(used), blobs, raw)


def _seal_payload(scan: _ScanResult, *, job_id: str, session_id: str) -> dict[str, Any]:
    base: dict[str, Any] = {
        "protocol": SEAL_PROTOCOL,
        "job_id": job_id,
        "session_id": session_id,
        "entry_count": len(scan.entries),
        "final_entry_sha256": scan.final_entry_sha256,
        "journal_sha256": _sha256(scan.raw_journal),
    }
    return {**base, "seal_sha256": _seal_digest(base)}


def _verify_seal(root_fd: int, scan: _ScanResult, *, job_id: str, session_id: str) -> None:
    raw = _read_regular_at(
        root_fd,
        SEAL_NAME,
        label="patch journal seal",
        limit=16 * 1024,
    )
    if not raw.endswith(b"\n") or raw.count(b"\n") != 1:
        raise PatchJournalError("patch journal seal is truncated or has trailing data")
    payload = _parse_canonical_json(raw[:-1], label="patch journal seal")
    if set(payload) != _SEAL_KEYS:
        raise PatchJournalError("patch journal seal has missing or unknown keys")
    if payload["protocol"] != SEAL_PROTOCOL:
        raise PatchJournalError("patch journal seal has the wrong protocol")
    if payload["job_id"] != job_id or payload["session_id"] != session_id:
        raise PatchJournalError("patch journal seal crosses its Job/session boundary")
    if isinstance(payload["entry_count"], bool) or not isinstance(payload["entry_count"], int):
        raise PatchJournalError("patch journal seal has an invalid entry count")
    for key in ("final_entry_sha256", "journal_sha256", "seal_sha256"):
        _require_sha256(payload[key], key)
    without_digest = dict(payload)
    claimed = without_digest.pop("seal_sha256")
    if _seal_digest(without_digest) != claimed:
        raise PatchJournalError("patch journal seal has an invalid digest")
    expected = _seal_payload(scan, job_id=job_id, session_id=session_id)
    if payload != expected:
        raise PatchJournalError("patch journal changed after it was closed")


def _committed_patches(scan: _ScanResult) -> tuple[CommittedPatch, ...]:
    pending: dict[str, Any] | None = None
    committed: list[CommittedPatch] = []
    for entry in scan.entries:
        if entry["state"] == "intent":
            pending = entry
        elif entry["state"] == "commit":
            if pending is None:  # Defensive; _scan already enforces this.
                raise PatchJournalError("commit has no intent")
            paths = tuple(pending["paths"])
            committed.append(
                CommittedPatch(
                    intent_sequence=pending["sequence"],
                    commit_sequence=entry["sequence"],
                    tool_call_id=pending["tool_call_id"],
                    paths=paths,
                    patch_sha256=pending["patch_sha256"],
                    before_sha256=dict(entry["before_sha256"]),
                    after_sha256=dict(entry["after_sha256"]),
                    patch=scan.blobs[pending["sequence"]],
                )
            )
            pending = None
        elif entry["state"] == "abort":
            pending = None
    return tuple(committed)


class PatchJournal:
    """Single-writer patch journal for one Job and one fresh Pi session."""

    def __init__(
        self,
        root: Path,
        root_fd: int,
        lock_fd: int,
        *,
        job_id: str,
        session_id: str,
        writer: ArtifactWriter,
    ) -> None:
        self.root = root
        self._root_fd = root_fd
        self._lock_fd = lock_fd
        self.job_id = _require_identifier(job_id, "job_id")
        self.session_id = _require_identifier(session_id, "session_id")
        self._writer = writer
        self._closed = False
        self._poisoned = False
        self._disposed = False

    @classmethod
    def create(
        cls,
        artifact_dir: Path,
        job_id: str,
        session_id: str,
        *,
        quota: ArtifactWriter | None = None,
    ) -> "PatchJournal":
        expected_job = _require_identifier(job_id, "job_id")
        expected_session = _require_identifier(session_id, "session_id")
        root, root_fd = _safe_directory_fd(artifact_dir, "Job artifact directory")
        lock_fd: int | None = None
        try:
            lock_fd = _safe_open_regular(
                root_fd,
                LOCK_NAME,
                os.O_RDWR | os.O_CREAT | os.O_EXCL,
                label="patch journal lock",
            )
            os.fsync(lock_fd)
            try:
                os.mkdir(BLOB_DIRECTORY, mode=0o700, dir_fd=root_fd)
            except OSError as exc:
                raise PatchJournalError(f"cannot exclusively create patch blob directory: {exc}") from exc
            blob_fd = _open_blob_directory(root_fd)
            try:
                os.fsync(blob_fd)
            finally:
                os.close(blob_fd)
            os.fsync(root_fd)
            writer: ArtifactWriter = quota or _DirectArtifactWriter(root, root_fd)
            writer_root = getattr(writer, "root", root)
            if Path(writer_root).resolve(strict=True) != root:
                raise PatchJournalError("artifact writer root does not match the Job artifact directory")
            writer.write_once(JOURNAL_NAME, b"", mode=0o600)
            os.fsync(root_fd)
            instance = cls(
                root,
                root_fd,
                lock_fd,
                job_id=expected_job,
                session_id=expected_session,
                writer=writer,
            )
            with instance._locked():
                _scan(root_fd, job_id=instance.job_id, session_id=instance.session_id)
            lock_fd = None
            return instance
        except Exception:
            if lock_fd is not None:
                os.close(lock_fd)
            os.close(root_fd)
            raise

    @classmethod
    def open_existing(
        cls,
        artifact_dir: Path,
        job_id: str,
        session_id: str,
        *,
        quota: ArtifactWriter | None = None,
    ) -> "PatchJournal":
        expected_job = _require_identifier(job_id, "job_id")
        expected_session = _require_identifier(session_id, "session_id")
        root, root_fd = _safe_directory_fd(artifact_dir, "Job artifact directory")
        lock_fd: int | None = None
        try:
            lock_fd = _safe_open_regular(
                root_fd,
                LOCK_NAME,
                os.O_RDWR,
                label="patch journal lock",
            )
            writer: ArtifactWriter = quota or _DirectArtifactWriter(root, root_fd)
            writer_root = getattr(writer, "root", root)
            if Path(writer_root).resolve(strict=True) != root:
                raise PatchJournalError("artifact writer root does not match the Job artifact directory")
            instance = cls(
                root,
                root_fd,
                lock_fd,
                job_id=expected_job,
                session_id=expected_session,
                writer=writer,
            )
            with instance._locked():
                if _seal_exists(root_fd):
                    raise PatchJournalError("patch journal is already closed")
                _scan(root_fd, job_id=instance.job_id, session_id=instance.session_id)
            lock_fd = None
            return instance
        except Exception:
            if lock_fd is not None:
                os.close(lock_fd)
            os.close(root_fd)
            raise

    @contextmanager
    def _locked(self) -> Iterator[None]:
        if self._closed:
            raise PatchJournalError("patch journal is closed")
        if self._poisoned:
            raise PatchJournalError("patch journal writer is poisoned by a failed append")
        try:
            opened = os.fstat(self._lock_fd)
            lexical = os.stat(LOCK_NAME, dir_fd=self._root_fd, follow_symlinks=False)
        except OSError as exc:
            self._poisoned = True
            raise PatchJournalError(f"cannot validate patch journal lock: {exc}") from exc
        if (
            not stat.S_ISREG(opened.st_mode)
            or stat.S_ISLNK(lexical.st_mode)
            or opened.st_nlink != 1
            or lexical.st_nlink != 1
            or (opened.st_dev, opened.st_ino) != (lexical.st_dev, lexical.st_ino)
        ):
            self._poisoned = True
            raise PatchJournalError("patch journal lock is unsafe")
        fcntl.flock(self._lock_fd, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(self._lock_fd, fcntl.LOCK_UN)

    def _assert_writable_unlocked(self) -> _ScanResult:
        if _seal_exists(self._root_fd):
            self._closed = True
            raise PatchJournalError("patch journal is closed")
        return _scan(self._root_fd, job_id=self.job_id, session_id=self.session_id)

    def _append_unlocked(self, entry: dict[str, Any]) -> None:
        without_digest = dict(entry)
        without_digest.pop("entry_sha256", None)
        entry["entry_sha256"] = _entry_digest(without_digest)
        encoded = _canonical_json(entry) + b"\n"
        if len(encoded) > MAX_ENTRY_BYTES:
            raise PatchJournalError("patch journal entry exceeds its byte limit")
        try:
            self._writer.append(JOURNAL_NAME, encoded)
            os.fsync(self._root_fd)
            _scan(self._root_fd, job_id=self.job_id, session_id=self.session_id)
        except Exception:
            self._poisoned = True
            raise

    def record_intent(
        self,
        tool_call_id: str,
        paths: Sequence[str],
        patch: bytes,
    ) -> PatchIntent:
        tool_id = _require_identifier(tool_call_id, "tool_call_id")
        if isinstance(paths, (str, bytes)):
            raise PatchJournalError("paths must be an array, not a scalar string")
        normalized_paths = _normalize_paths(tuple(paths))
        if not isinstance(patch, bytes) or not patch or len(patch) > MAX_PATCH_BYTES:
            raise PatchJournalError("patch bytes must be nonempty and within the byte limit")
        patch_sha256 = _sha256(patch)
        with self._locked():
            scan = self._assert_writable_unlocked()
            if scan.pending is not None:
                raise PatchJournalError("the prior patch intent must be committed or aborted")
            if tool_id in scan.used_tool_call_ids:
                raise PatchJournalError("tool_call_id already has an intent")
            sequence = scan.next_sequence
            blob_name = _blob_name(sequence, patch_sha256)
            try:
                self._writer.write_once(
                    f"{BLOB_DIRECTORY}/{blob_name}",
                    patch,
                    mode=0o400,
                )
                blob_fd = _open_blob_directory(self._root_fd)
                try:
                    _set_read_only_at(
                        blob_fd,
                        blob_name,
                        label=f"patch blob {blob_name}",
                    )
                    os.fsync(blob_fd)
                finally:
                    os.close(blob_fd)
            except Exception:
                self._poisoned = True
                raise
            entry: dict[str, Any] = {
                "protocol": JOURNAL_PROTOCOL,
                "job_id": self.job_id,
                "session_id": self.session_id,
                "sequence": sequence,
                "tool_call_id": tool_id,
                "paths": list(normalized_paths),
                "patch_sha256": patch_sha256,
                "prior_entry_sha256": scan.final_entry_sha256,
                "state": "intent",
                "entry_sha256": "",
            }
            self._append_unlocked(entry)
            return PatchIntent(
                job_id=self.job_id,
                session_id=self.session_id,
                sequence=sequence,
                tool_call_id=tool_id,
                paths=normalized_paths,
                patch_sha256=patch_sha256,
            )

    def _resolve(
        self,
        intent: PatchIntent,
        *,
        state: str,
        before_sha256: Mapping[str, str] | None = None,
        after_sha256: Mapping[str, str] | None = None,
    ) -> None:
        if not isinstance(intent, PatchIntent):
            raise PatchJournalError("resolution requires a PatchIntent handle")
        with self._locked():
            scan = self._assert_writable_unlocked()
            pending = scan.pending
            expected = PatchIntent(
                job_id=self.job_id,
                session_id=self.session_id,
                sequence=pending["sequence"] if pending else -1,
                tool_call_id=pending["tool_call_id"] if pending else "missing",
                paths=tuple(pending["paths"]) if pending else ("missing",),
                patch_sha256=pending["patch_sha256"] if pending else ZERO_SHA256,
            )
            if pending is None or intent != expected:
                raise PatchJournalError("resolution does not match the pending patch intent")
            entry: dict[str, Any] = {
                "protocol": JOURNAL_PROTOCOL,
                "job_id": self.job_id,
                "session_id": self.session_id,
                "sequence": scan.next_sequence,
                "tool_call_id": intent.tool_call_id,
                "paths": list(intent.paths),
                "patch_sha256": intent.patch_sha256,
                "prior_entry_sha256": scan.final_entry_sha256,
                "state": state,
                "entry_sha256": "",
            }
            if state == "commit":
                entry["before_sha256"] = _normalize_hash_map(
                    before_sha256, intent.paths, "before_sha256"
                )
                entry["after_sha256"] = _normalize_hash_map(
                    after_sha256, intent.paths, "after_sha256"
                )
            self._append_unlocked(entry)

    def commit(
        self,
        intent: PatchIntent,
        before_sha256: Mapping[str, str],
        after_sha256: Mapping[str, str],
    ) -> None:
        self._resolve(
            intent,
            state="commit",
            before_sha256=before_sha256,
            after_sha256=after_sha256,
        )

    def abort(self, intent: PatchIntent) -> None:
        self._resolve(intent, state="abort")

    def close(self) -> None:
        with self._locked():
            scan = self._assert_writable_unlocked()
            if scan.pending is not None:
                raise PatchJournalError("cannot close with an unresolved patch intent")
            seal = _seal_payload(scan, job_id=self.job_id, session_id=self.session_id)
            encoded = _canonical_json(seal) + b"\n"
            try:
                self._writer.write_once(SEAL_NAME, encoded, mode=0o400)
                _set_read_only_at(
                    self._root_fd,
                    SEAL_NAME,
                    label="patch journal seal",
                )
                os.fsync(self._root_fd)
                _verify_seal(
                    self._root_fd,
                    scan,
                    job_id=self.job_id,
                    session_id=self.session_id,
                )
                _set_read_only_at(
                    self._root_fd,
                    JOURNAL_NAME,
                    label="patch journal",
                )
                os.fsync(self._root_fd)
            except Exception:
                self._poisoned = True
                raise
            self._closed = True

    def dispose(self) -> None:
        """Release descriptors without sealing; incomplete evidence stays visible."""

        if self._disposed:
            return
        self._disposed = True
        self._closed = True
        try:
            os.close(self._lock_fd)
        finally:
            os.close(self._root_fd)

    def __enter__(self) -> "PatchJournal":
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.dispose()


def verify_patch_journal(
    artifact_dir: Path,
    job_id: str,
    session_id: str,
    *,
    require_closed: bool = True,
) -> tuple[CommittedPatch, ...]:
    """Verify the complete chain/blob set and return committed patches in order."""

    expected_job = _require_identifier(job_id, "job_id")
    expected_session = _require_identifier(session_id, "session_id")
    _root, root_fd = _safe_directory_fd(artifact_dir, "Job artifact directory")
    lock_fd: int | None = None
    try:
        lock_fd = _safe_open_regular(
            root_fd,
            LOCK_NAME,
            os.O_RDWR,
            label="patch journal lock",
        )
        fcntl.flock(lock_fd, fcntl.LOCK_EX)
        scan = _scan(root_fd, job_id=expected_job, session_id=expected_session)
        if scan.pending is not None:
            raise PatchJournalError("patch journal has an unresolved intent")
        sealed = _seal_exists(root_fd)
        if require_closed and not sealed:
            raise PatchJournalError("patch journal is not closed")
        if sealed:
            _verify_seal(
                root_fd,
                scan,
                job_id=expected_job,
                session_id=expected_session,
            )
            _assert_read_only_at(root_fd, JOURNAL_NAME, label="patch journal")
            _assert_read_only_at(root_fd, SEAL_NAME, label="patch journal seal")
        return _committed_patches(scan)
    finally:
        if lock_fd is not None:
            try:
                fcntl.flock(lock_fd, fcntl.LOCK_UN)
            finally:
                os.close(lock_fd)
        os.close(root_fd)


def replay_committed_patches(
    patches: Sequence[CommittedPatch],
    apply_callback: Callable[[CommittedPatch], ReplayObservation],
) -> tuple[CommittedPatch, ...]:
    """Replay verified patches using trusted caller logic and check file hashes.

    The callback is responsible for applying one patch in an isolated replay
    environment and must return the hashes it observed immediately before and
    after the application.  This function never invokes a shell or Git.
    """

    replayed: list[CommittedPatch] = []
    previous_intent = 0
    seen_tool_ids: set[str] = set()
    for patch in patches:
        if not isinstance(patch, CommittedPatch):
            raise PatchJournalError("replay input contains an unverified patch type")
        paths = _normalize_paths(patch.paths)
        _require_identifier(patch.tool_call_id, "tool_call_id")
        if (
            isinstance(patch.intent_sequence, bool)
            or not isinstance(patch.intent_sequence, int)
            or isinstance(patch.commit_sequence, bool)
            or not isinstance(patch.commit_sequence, int)
            or patch.intent_sequence <= previous_intent
            or patch.commit_sequence != patch.intent_sequence + 1
            or patch.tool_call_id in seen_tool_ids
            or not isinstance(patch.patch, bytes)
            or not patch.patch
            or _sha256(patch.patch) != patch.patch_sha256
        ):
            raise PatchJournalError("committed patch order or identity is invalid")
        expected_before = _normalize_hash_map(
            patch.before_sha256, paths, "before_sha256"
        )
        expected_after = _normalize_hash_map(
            patch.after_sha256, paths, "after_sha256"
        )
        try:
            observation = apply_callback(patch)
        except Exception as exc:
            raise PatchJournalError(
                f"replay callback failed for tool call {patch.tool_call_id}"
            ) from exc
        if not isinstance(observation, ReplayObservation):
            raise PatchJournalError("replay callback must return ReplayObservation")
        observed_before = _normalize_hash_map(
            observation.before_sha256, paths, "replay before_sha256"
        )
        observed_after = _normalize_hash_map(
            observation.after_sha256, paths, "replay after_sha256"
        )
        if observed_before != expected_before or observed_after != expected_after:
            raise PatchJournalError(
                f"replay hashes disagree for tool call {patch.tool_call_id}"
            )
        replayed.append(patch)
        previous_intent = patch.intent_sequence
        seen_tool_ids.add(patch.tool_call_id)
    return tuple(replayed)


__all__ = [
    "ArtifactWriter",
    "BLOB_DIRECTORY",
    "CommittedPatch",
    "JOURNAL_NAME",
    "JOURNAL_PROTOCOL",
    "LOCK_NAME",
    "PatchIntent",
    "PatchJournal",
    "PatchJournalError",
    "ReplayObservation",
    "SEAL_NAME",
    "SEAL_PROTOCOL",
    "replay_committed_patches",
    "verify_patch_journal",
]
