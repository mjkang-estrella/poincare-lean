"""Restart-safe SQLite state and append-only evidence for Harness v2."""

from __future__ import annotations

import hashlib
import json
import os
import fcntl
import sqlite3
import stat
import subprocess
import time
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Callable, Iterator, Sequence

from .migrations import SCHEMA_VERSION, migrate
from .validation import (
    COMMIT_RE,
    GATE_STATES,
    JOB_ID_RE,
    SHA256_RE,
    RecordValidationError,
    normalize_scope,
    reject_secrets,
    scopes_overlap,
    validate_job,
    validate_task,
)


TERMINAL_JOB_STATES = {"passed", "rejected", "blocked", "interrupted"}
ACTIVE_JOB_STATES = {"preparing", "running", "reviewing"}


class HarnessError(RuntimeError):
    """Base class for an expected Harness v2 runtime error."""


class NotInitializedError(HarnessError):
    pass


class NotFoundError(HarnessError):
    pass


class ConflictError(HarnessError):
    pass


class TransitionError(HarnessError):
    pass


class LeaseError(HarnessError):
    pass


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _pretty_json(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


MAX_GATE_BYTES = 8 * 1024 * 1024
MAX_EXECUTABLE_BYTES = 256 * 1024 * 1024
DECLARATION_PROBE_ARGV = [
    "env",
    "LEAN_NUM_THREADS=1",
    "lake",
    "env",
    "lean",
    "--stdin",
]


def _attest_executable(
    value: str | os.PathLike[str], *, expected_sha256: str | None = None
) -> tuple[Path, str, tuple[int, ...]]:
    """Bind an authority executable to stable, canonical bytes and identity."""

    path = Path(value).expanduser()
    if not path.is_absolute() or Path(os.path.normpath(path)) != path:
        raise HarnessError("Git executable path must be absolute and normalized")
    try:
        if Path(os.path.realpath(path)) != path:
            raise HarnessError("Git executable path must be canonical and non-symlinked")
        before = path.lstat()
    except OSError as error:
        raise HarnessError(f"could not inspect Git executable: {error}") from error
    mode = stat.S_IMODE(before.st_mode)
    if (
        not stat.S_ISREG(before.st_mode)
        or stat.S_ISLNK(before.st_mode)
        or before.st_uid not in {0, os.geteuid()}
        or mode & 0o022
        or mode & 0o111 == 0
    ):
        raise HarnessError(
            "Git executable must be a root-or-current-user-owned, non-writable executable regular file"
        )
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise HarnessError(f"could not safely open Git executable: {error}") from error
    identity = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_uid,
        before.st_nlink,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    try:
        opened = os.fstat(descriptor)
        opened_identity = (
            opened.st_dev,
            opened.st_ino,
            opened.st_mode,
            opened.st_uid,
            opened.st_nlink,
            opened.st_size,
            opened.st_mtime_ns,
            opened.st_ctime_ns,
        )
        if opened_identity != identity:
            raise HarnessError("Git executable changed while opening")
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            total += len(chunk)
            if total > MAX_EXECUTABLE_BYTES:
                raise HarnessError("Git executable exceeds the attestation size bound")
        after = os.fstat(descriptor)
        after_identity = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_uid,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if after_identity != identity or total != opened.st_size:
            raise HarnessError("Git executable changed while hashing")
    finally:
        os.close(descriptor)
    sha256 = digest.hexdigest()
    if expected_sha256 is not None:
        if SHA256_RE.fullmatch(expected_sha256) is None:
            raise HarnessError("configured Git executable SHA-256 is invalid")
        if sha256 != expected_sha256:
            raise HarnessError("Git executable bytes do not match the configured attestation")
    return path, sha256, identity


def _read_regular_file_safely(path: Path, *, maximum_bytes: int) -> tuple[bytes, str]:
    """Read one stable non-symlink file descriptor and hash those exact bytes."""

    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise ConflictError(f"could not safely open evidence file {path}: {error}") from error
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise ConflictError(f"evidence path is not a regular file: {path}")
        if before.st_size > maximum_bytes:
            raise ConflictError(f"evidence file exceeds {maximum_bytes} bytes: {path}")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, maximum_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
            if total > maximum_bytes:
                raise ConflictError(f"evidence file exceeds {maximum_bytes} bytes: {path}")
        after = os.fstat(descriptor)
        stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
        if any(getattr(before, field) != getattr(after, field) for field in stable_fields):
            raise ConflictError(f"evidence file changed while it was read: {path}")
        path_stat = os.lstat(path)
        if stat.S_ISLNK(path_stat.st_mode) or (
            path_stat.st_dev,
            path_stat.st_ino,
        ) != (after.st_dev, after.st_ino):
            raise ConflictError(f"evidence path changed while it was read: {path}")
    finally:
        os.close(descriptor)
    content = b"".join(chunks)
    return content, _sha256_bytes(content)


def _utc_text(moment: datetime) -> str:
    return moment.astimezone(timezone.utc).isoformat(timespec="microseconds").replace(
        "+00:00", "Z"
    )


def _epoch_to_text(value: float) -> str:
    return _utc_text(datetime.fromtimestamp(value, timezone.utc))


def _reject_runtime_secrets(value: Any, path: str) -> None:
    try:
        reject_secrets(value, path)
    except RecordValidationError as error:
        raise HarnessError(str(error)) from error


def _assert_no_symlink_ancestors(path: Path) -> None:
    """Reject every existing symlink from the filesystem root through path."""

    if not path.is_absolute():
        raise HarnessError(f"path must be absolute: {path}")
    current = Path(path.anchor)
    for part in path.parts[1:]:
        current /= part
        try:
            mode = os.lstat(current).st_mode
        except FileNotFoundError:
            break
        if stat.S_ISLNK(mode):
            raise HarnessError(f"symbolic-link path component is forbidden: {current}")


def _is_within(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


def _read_relative_evidence(
    artifact_dir: Path, relative_path: str, expected_sha256: str
) -> None:
    path = Path(relative_path)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise TransitionError("gate evidence output path must be artifact-relative")
    try:
        root = artifact_dir.resolve(strict=True)
        unresolved = root / path
        _assert_no_symlink_ancestors(unresolved)
        candidate = unresolved.resolve(strict=True)
    except (HarnessError, OSError) as error:
        raise TransitionError(f"gate evidence output path is unsafe: {error}") from error
    if candidate.parent != root and root not in candidate.parents:
        raise TransitionError("gate evidence output escaped the Job artifact directory")
    try:
        _, digest = _read_regular_file_safely(candidate, maximum_bytes=MAX_GATE_BYTES)
    except ConflictError as error:
        raise TransitionError(str(error)) from error
    if digest != expected_sha256:
        raise TransitionError("gate evidence output hash does not match its exact bytes")


def _declaration_probe_source(
    task: dict[str, Any], index: int, symbol: str
) -> str:
    lines = ["import Poincare", f"#check {symbol}"]
    if index == 0:
        lines.append(
            f"#check ({symbol} : {task['objective']['frozen_lean_type']})"
        )
    return "\n".join(lines) + "\n"


def _validate_gate_document(
    document: Any,
    *,
    task: dict[str, Any],
    expected_status: str,
    accepted_commit: str,
    accepted_tree: str,
    artifact_dir: Path,
) -> dict[str, Any]:
    if not isinstance(document, dict):
        raise TransitionError("gate evidence must contain one JSON object")
    required_keys = {
        "schema_version",
        "status",
        "accepted_commit",
        "accepted_tree",
        "commands",
        "declarations",
    }
    if set(document) != required_keys:
        raise TransitionError(
            "gate evidence fields must be schema_version, status, accepted_commit, "
            "accepted_tree, commands, declarations"
        )
    if document["schema_version"] != "2.0":
        raise TransitionError("gate evidence schema_version must be '2.0'")
    if document["status"] != expected_status:
        raise TransitionError("gate evidence status does not match the recorded gate status")
    if document["accepted_commit"] != accepted_commit:
        raise TransitionError("gate evidence commit does not match the reviewed Job commit")
    if document["accepted_tree"] != accepted_tree:
        raise TransitionError("gate evidence tree does not match the reviewed commit tree")
    commands = document["commands"]
    if not isinstance(commands, list) or not commands:
        raise TransitionError("gate evidence commands must be a nonempty array")
    required_commands = task["acceptance"]["commands"]
    if len(commands) > len(required_commands):
        raise TransitionError("gate evidence contains undeclared commands")
    if expected_status == "passed" and len(commands) != len(required_commands):
        raise TransitionError("passed gate must record every Task acceptance command")
    saw_failure = False
    allowed_outcome_keys = {
        "argv",
        "status",
        "exit_code",
        "stdout_path",
        "stderr_path",
    }
    for index, outcome in enumerate(commands):
        if not isinstance(outcome, dict) or not {
            "argv",
            "status",
            "exit_code",
        }.issubset(outcome):
            raise TransitionError(f"gate command {index} lacks argv/status/exit_code")
        if set(outcome) - allowed_outcome_keys:
            raise TransitionError(f"gate command {index} has unknown outcome fields")
        if outcome["argv"] != required_commands[index]:
            raise TransitionError(f"gate command {index} does not match the Task contract")
        exit_code = outcome["exit_code"]
        if isinstance(exit_code, bool) or not isinstance(exit_code, int):
            raise TransitionError(f"gate command {index} exit_code must be an integer")
        outcome_status = outcome["status"]
        if outcome_status not in {"passed", "failed"}:
            raise TransitionError(f"gate command {index} status is invalid")
        if (outcome_status == "passed") != (exit_code == 0):
            raise TransitionError(f"gate command {index} status and exit_code disagree")
        saw_failure = saw_failure or exit_code != 0
        for path_key in ("stdout_path", "stderr_path"):
            if path_key not in outcome:
                continue
            path_text = outcome[path_key]
            if (
                not isinstance(path_text, str)
                or not path_text
                or Path(path_text).is_absolute()
                or ".." in Path(path_text).parts
            ):
                raise TransitionError(
                    f"gate command {index} {path_key} must be an artifact-relative path"
                )
    if expected_status == "passed" and saw_failure:
        raise TransitionError("passed gate contains a failed command")
    if expected_status == "failed" and not saw_failure:
        raise TransitionError("failed gate contains no failed command")

    declarations = document["declarations"]
    required_declarations = task["acceptance"].get("required_declarations", [])
    if not isinstance(declarations, list):
        raise TransitionError("gate declaration evidence must be an array")
    if len(declarations) != len(required_declarations):
        raise TransitionError(
            "gate declaration evidence must cover every required declaration exactly once"
        )
    declaration_keys = {
        "symbol",
        "source",
        "source_sha256",
        "argv",
        "status",
        "exit_code",
        "stdout_path",
        "stdout_sha256",
        "stderr_path",
        "stderr_sha256",
    }
    for index, (probe, symbol) in enumerate(
        zip(declarations, required_declarations, strict=True)
    ):
        if not isinstance(probe, dict) or set(probe) != declaration_keys:
            raise TransitionError(
                f"declaration probe {index} must contain the complete executable evidence"
            )
        if probe["symbol"] != symbol:
            raise TransitionError(
                f"declaration probe {index} does not match the Task contract"
            )
        expected_source = _declaration_probe_source(task, index, symbol)
        if probe["source"] != expected_source:
            raise TransitionError(
                f"declaration probe {index} source is not the canonical Task-bound probe"
            )
        if probe["source_sha256"] != _sha256_bytes(expected_source.encode("utf-8")):
            raise TransitionError(f"declaration probe {index} source hash is invalid")
        if probe["argv"] != DECLARATION_PROBE_ARGV:
            raise TransitionError(f"declaration probe {index} argv is invalid")
        if probe["status"] != "passed" or probe["exit_code"] != 0:
            raise TransitionError(f"declaration probe {index} did not pass")
        for stream in ("stdout", "stderr"):
            path_value = probe[f"{stream}_path"]
            digest_value = probe[f"{stream}_sha256"]
            if not isinstance(path_value, str) or not path_value:
                raise TransitionError(
                    f"declaration probe {index} {stream}_path must not be empty"
                )
            if not isinstance(digest_value, str) or SHA256_RE.fullmatch(
                digest_value
            ) is None:
                raise TransitionError(
                    f"declaration probe {index} {stream}_sha256 is invalid"
                )
            _read_relative_evidence(artifact_dir, path_value, digest_value)
    _reject_runtime_secrets(document, "gate")
    return document


class HarnessStore:
    """The small, local control-plane API used by the CLI and tests."""

    def __init__(
        self,
        state_dir: str | os.PathLike[str],
        *,
        clock: Callable[[], datetime] | None = None,
        worktree_root: str | os.PathLike[str] | None = None,
        integration_root: str | os.PathLike[str] | None = None,
        git_executable: str | os.PathLike[str] | None = None,
        git_sha256: str | None = None,
    ) -> None:
        self.state_dir = Path(state_dir).expanduser().absolute()
        self.database_path = self.state_dir / "harness.sqlite3"
        self.jobs_root = self.state_dir / "jobs"
        self.execution_locks_root = self.state_dir / "execution-locks"
        self._clock = clock or (lambda: datetime.now(timezone.utc))
        self._configured_worktree_root = (
            None if worktree_root is None else Path(worktree_root).expanduser().absolute()
        )
        self._configured_integration_root = (
            None if integration_root is None else Path(integration_root).expanduser().absolute()
        )
        configured_git = git_executable or os.environ.get("HARNESS_PI_GIT", "/usr/bin/git")
        configured_sha256 = git_sha256 or os.environ.get("HARNESS_PI_GIT_SHA256")
        (
            self._git_executable,
            self._git_sha256,
            self._git_identity,
        ) = _attest_executable(configured_git, expected_sha256=configured_sha256)

    def _now(self) -> datetime:
        moment = self._clock()
        if moment.tzinfo is None:
            raise HarnessError("runtime clock must return a timezone-aware datetime")
        return moment.astimezone(timezone.utc)

    def _validate_configured_roots(self) -> tuple[Path, Path] | None:
        worktree = self._configured_worktree_root
        integration = self._configured_integration_root
        if (worktree is None) != (integration is None):
            raise HarnessError("worktree_root and integration_root must be configured together")
        if worktree is None or integration is None:
            return None
        try:
            worktree = worktree.resolve(strict=True)
            integration = integration.resolve(strict=True)
        except OSError as error:
            raise HarnessError(f"trusted root does not exist: {error}") from error
        if not worktree.is_dir() or not integration.is_dir():
            raise HarnessError("trusted worktree and integration roots must be directories")
        state = self.state_dir.resolve(strict=False)
        if _is_within(worktree, integration) or _is_within(integration, worktree):
            raise HarnessError("trusted worktree root must be external to the integration root")
        if _is_within(worktree, state) or _is_within(state, worktree):
            raise HarnessError("trusted worktree root must be external to runtime state")
        return worktree, integration

    def _persist_or_check_roots(
        self,
        connection: sqlite3.Connection,
        configured: tuple[Path, Path] | None,
    ) -> tuple[Path, Path] | None:
        with self._transaction(connection):
            row = connection.execute(
                "SELECT worktree_root, integration_root FROM runtime_config WHERE singleton = 1"
            ).fetchone()
            if row is None:
                if configured is None:
                    return None
                connection.execute(
                    """
                    INSERT INTO runtime_config(
                        singleton, worktree_root, integration_root, configured_at
                    ) VALUES (1, ?, ?, ?)
                    """,
                    (str(configured[0]), str(configured[1]), _utc_text(self._now())),
                )
                return configured
            persisted = (Path(row["worktree_root"]), Path(row["integration_root"]))
            if configured is not None and persisted != configured:
                raise ConflictError("runtime trusted roots are immutable once configured")
            return persisted

    def _runtime_roots(
        self,
        connection: sqlite3.Connection,
        *,
        required: bool,
    ) -> tuple[Path, Path] | None:
        row = connection.execute(
            "SELECT worktree_root, integration_root FROM runtime_config WHERE singleton = 1"
        ).fetchone()
        if row is None:
            if required:
                raise ConflictError(
                    "trusted worktree/integration roots are not configured; rerun init with both"
                )
            return None
        worktree = Path(row["worktree_root"])
        integration = Path(row["integration_root"])
        try:
            _assert_no_symlink_ancestors(worktree)
            _assert_no_symlink_ancestors(integration)
            resolved_worktree = worktree.resolve(strict=True)
            resolved_integration = integration.resolve(strict=True)
        except (HarnessError, OSError) as error:
            raise ConflictError(f"a configured trusted root is unsafe: {error}") from error
        if (
            resolved_worktree != worktree
            or resolved_integration != integration
            or not worktree.is_dir()
            or not integration.is_dir()
        ):
            raise ConflictError("a configured trusted root is missing")
        if _is_within(worktree, integration) or _is_within(integration, worktree):
            raise ConflictError("persisted worktree and integration roots overlap")
        return worktree, integration

    def _validate_job_worktree(
        self,
        connection: sqlite3.Connection,
        record: dict[str, Any],
        *,
        required: bool,
    ) -> bool:
        roots = self._runtime_roots(connection, required=required)
        if roots is None:
            return False
        worktree_root, integration_root = roots
        candidate = Path(record["workspace"]["worktree"])
        expected = worktree_root / record["id"]
        _assert_no_symlink_ancestors(candidate)
        resolved = candidate.resolve(strict=False)
        if resolved != expected:
            raise ConflictError(f"Job worktree must be exactly {expected}")
        if _is_within(resolved, integration_root) or _is_within(
            resolved, self.state_dir.resolve(strict=False)
        ):
            raise ConflictError("Job worktree overlaps integration or control state")
        if candidate.exists() and not candidate.is_dir():
            raise ConflictError("existing Job worktree path is not a directory")
        return True

    def _git(
        self,
        worktree: Path,
        *arguments: str,
        allowed_exit_codes: tuple[int, ...] = (0,),
    ) -> subprocess.CompletedProcess[bytes]:
        try:
            path, _sha256, identity = _attest_executable(
                self._git_executable, expected_sha256=self._git_sha256
            )
        except HarnessError as error:
            raise TransitionError(f"Git executable failed re-attestation: {error}") from error
        if path != self._git_executable or identity != self._git_identity:
            raise TransitionError("Git executable identity changed after runtime initialization")
        environment = {
            "PATH": "/usr/bin:/bin",
            "HOME": "/nonexistent",
            "LC_ALL": "C",
            "LANG": "C",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_SYSTEM": "/dev/null",
            "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_ATTR_NOSYSTEM": "1",
            "GIT_PAGER": "cat",
            "PAGER": "cat",
            "GIT_EXTERNAL_DIFF": "",
        }
        try:
            result = subprocess.run(
                [
                    str(self._git_executable),
                    "-c",
                    "core.fsmonitor=false",
                    "-c",
                    "core.hooksPath=/dev/null",
                    "-c",
                    "diff.external=",
                    "-C",
                    str(worktree),
                    *arguments,
                ],
                check=False,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=15,
                env=environment,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise TransitionError(f"could not verify reviewed Git state: {error}") from error
        if result.returncode not in allowed_exit_codes:
            detail = result.stderr[:512].decode("utf-8", errors="replace").strip()
            raise TransitionError(
                f"reviewed Git state check failed ({result.returncode}): {detail}"
            )
        return result

    def _git_text(self, worktree: Path, *arguments: str) -> str:
        result = self._git(worktree, *arguments)
        if len(result.stdout) > 4096:
            raise TransitionError("reviewed Git identity output is unexpectedly large")
        return result.stdout.decode("utf-8", errors="strict").strip()

    def _validate_reviewed_commit(
        self,
        connection: sqlite3.Connection,
        row: sqlite3.Row,
        task: dict[str, Any],
        accepted_commit: str,
    ) -> str:
        self._validate_job_worktree(
            connection, json.loads(row["source_json"]), required=True
        )
        worktree = Path(json.loads(row["source_json"])["workspace"]["worktree"])
        if not worktree.is_dir():
            raise TransitionError("review requires the trusted Job worktree to exist")
        roots = self._runtime_roots(connection, required=True)
        assert roots is not None
        _, integration = roots
        try:
            worktree_top = Path(
                self._git_text(worktree, "rev-parse", "--show-toplevel")
            ).resolve(strict=True)
            integration_top = Path(
                self._git_text(integration, "rev-parse", "--show-toplevel")
            ).resolve(strict=True)
            worktree_common_text = self._git_text(
                worktree, "rev-parse", "--path-format=absolute", "--git-common-dir"
            )
            integration_common_text = self._git_text(
                integration, "rev-parse", "--path-format=absolute", "--git-common-dir"
            )
            worktree_common = Path(worktree_common_text).resolve(strict=True)
            integration_common = Path(integration_common_text).resolve(strict=True)
        except (OSError, UnicodeError) as error:
            raise TransitionError(f"could not resolve reviewed Git identity: {error}") from error
        if worktree_top != worktree.resolve(strict=True):
            raise TransitionError("Job workspace is not the top level of its Git worktree")
        if integration_top != integration.resolve(strict=True):
            raise TransitionError("configured integration root is not a Git top level")
        if worktree_common != integration_common:
            raise TransitionError("Job worktree does not belong to the integration repository")
        resolved_commit = self._git_text(
            worktree, "rev-parse", "--verify", f"{accepted_commit}^{{commit}}"
        )
        if resolved_commit != accepted_commit:
            raise TransitionError("reviewed commit does not resolve exactly")
        head = self._git_text(worktree, "rev-parse", "--verify", "HEAD^{commit}")
        if head != accepted_commit:
            raise TransitionError("reviewed commit must be the exact Job worktree HEAD")
        ancestor = self._git(
            worktree,
            "merge-base",
            "--is-ancestor",
            task["base_commit"],
            accepted_commit,
            allowed_exit_codes=(0, 1),
        )
        if ancestor.returncode != 0:
            raise TransitionError("reviewed commit is not descended from the Task base commit")
        status = self._git(worktree, "status", "--porcelain=v1", "--untracked-files=all")
        if status.stdout:
            raise TransitionError("reviewed Job worktree must be clean at its accepted commit")
        tree = self._git_text(
            worktree, "rev-parse", "--verify", f"{accepted_commit}^{{tree}}"
        )
        if COMMIT_RE.fullmatch(tree) is None:
            raise TransitionError("reviewed commit tree has an invalid object ID")
        return tree

    def _connect(self, *, require_initialized: bool = True) -> sqlite3.Connection:
        _assert_no_symlink_ancestors(self.state_dir)
        database_paths = (
            self.database_path,
            Path(str(self.database_path) + "-wal"),
            Path(str(self.database_path) + "-shm"),
        )
        if self.state_dir.is_symlink() or any(path.is_symlink() for path in database_paths):
            raise HarnessError("state directory and SQLite files must not be symbolic links")
        if require_initialized and not self.database_path.is_file():
            raise NotInitializedError(
                f"Harness state is not initialized at {self.state_dir}; run init first"
            )
        connection = sqlite3.connect(
            self.database_path,
            timeout=10.0,
            isolation_level=None,
        )
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("PRAGMA busy_timeout = 10000")
        return connection

    @contextmanager
    def _transaction(self, connection: sqlite3.Connection) -> Iterator[None]:
        try:
            connection.execute("BEGIN IMMEDIATE")
        except sqlite3.Error as error:
            raise HarnessError(f"could not acquire SQLite write transaction: {error}") from error
        try:
            yield
        except Exception:
            try:
                connection.rollback()
            except sqlite3.Error:
                pass
            raise
        else:
            try:
                connection.commit()
            except sqlite3.Error as error:
                raise HarnessError(f"could not commit SQLite transaction: {error}") from error

    def initialize(self) -> dict[str, Any]:
        _assert_no_symlink_ancestors(self.state_dir)
        configured_roots = self._validate_configured_roots()
        if self.state_dir.exists() and not self.state_dir.is_dir():
            raise HarnessError(f"state path is not a directory: {self.state_dir}")
        for sqlite_path in (
            self.database_path,
            Path(str(self.database_path) + "-wal"),
            Path(str(self.database_path) + "-shm"),
        ):
            if sqlite_path.is_symlink():
                raise HarnessError(f"SQLite path must not be a symbolic link: {sqlite_path}")
        self.state_dir.mkdir(parents=True, exist_ok=True, mode=0o700)
        for directory, label in (
            (self.jobs_root, "jobs"),
            (self.execution_locks_root, "execution-locks"),
        ):
            _assert_no_symlink_ancestors(directory)
            if directory.exists() and not directory.is_dir():
                raise HarnessError(f"{label} path is not a directory: {directory}")
            directory.mkdir(exist_ok=True, mode=0o700)
            if directory.is_symlink():
                raise HarnessError(f"{label} directory must not be a symbolic link")
        os.chmod(self.state_dir, 0o700)
        os.chmod(self.jobs_root, 0o700)
        os.chmod(self.execution_locks_root, 0o700)
        connection = self._connect(require_initialized=False)
        try:
            for attempt in range(40):
                try:
                    connection.execute("PRAGMA journal_mode = WAL")
                    break
                except sqlite3.OperationalError as error:
                    if (
                        "locked" not in str(error).lower()
                        and "busy" not in str(error).lower()
                    ) or attempt == 39:
                        raise HarnessError(
                            f"could not initialize SQLite journal mode: {error}"
                        ) from error
                    time.sleep(min(0.01 * (attempt + 1), 0.1))
            connection.execute("PRAGMA synchronous = FULL")
            version = migrate(connection, _utc_text(self._now()))
            roots = self._persist_or_check_roots(connection, configured_roots)
        finally:
            if connection is not None:
                connection.close()
        for sqlite_path in (
            self.database_path,
            Path(str(self.database_path) + "-wal"),
            Path(str(self.database_path) + "-shm"),
        ):
            if sqlite_path.exists():
                os.chmod(sqlite_path, 0o600)
        return {
            "state_dir": str(self.state_dir),
            "database": str(self.database_path),
            "schema_version": version,
            "worktree_root": None if roots is None else str(roots[0]),
            "integration_root": None if roots is None else str(roots[1]),
        }

    def schema_version(self) -> int:
        connection = self._connect()
        try:
            row = connection.execute(
                "SELECT MAX(version) AS version FROM schema_migrations"
            ).fetchone()
            if row is None or row["version"] is None:
                raise NotInitializedError("database has no applied schema migration")
            return int(row["version"])
        finally:
            connection.close()

    @staticmethod
    def _dispatch_row(connection: sqlite3.Connection) -> sqlite3.Row:
        row = connection.execute(
            "SELECT desired_state, generation, actor, updated_at "
            "FROM dispatch_control WHERE singleton = 1"
        ).fetchone()
        if row is None:
            raise NotInitializedError("runtime dispatch control is not initialized")
        return row

    @classmethod
    def _assert_dispatch_running(cls, connection: sqlite3.Connection) -> sqlite3.Row:
        row = cls._dispatch_row(connection)
        if row["desired_state"] != "running":
            raise LeaseError("Harness dispatch is durably stopped; refusing to claim a Job")
        return row

    @classmethod
    def _assert_active_lease_dispatch_epoch(
        cls, connection: sqlite3.Connection, job: sqlite3.Row | dict[str, Any]
    ) -> sqlite3.Row:
        dispatch = cls._dispatch_row(connection)
        lease_generation = job["lease_dispatch_generation"]
        current_generation = int(dispatch["generation"])
        if (
            dispatch["desired_state"] == "running"
            and lease_generation == current_generation
        ):
            return dispatch
        if (
            dispatch["desired_state"] == "stopped"
            and job["state"] in {"running", "reviewing"}
            and lease_generation == current_generation - 1
        ):
            return dispatch
        raise LeaseError("Job lease belongs to a closed dispatch generation")

    def get_dispatch_state(self) -> dict[str, Any]:
        connection = self._connect()
        try:
            row = self._dispatch_row(connection)
            return {
                "desired_state": row["desired_state"],
                "generation": int(row["generation"]),
                "actor": row["actor"],
                "updated_at": row["updated_at"],
            }
        finally:
            connection.close()

    def set_dispatch_state(self, desired_state: str, *, actor: str) -> dict[str, Any]:
        if desired_state not in {"running", "stopped"}:
            raise TransitionError("dispatch state must be running or stopped")
        if not actor or not actor.strip():
            raise TransitionError("dispatch-state actor must not be empty")
        actor = actor.strip()
        _reject_runtime_secrets(actor, "dispatch_actor")
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            with self._transaction(connection):
                row = self._dispatch_row(connection)
                if row["desired_state"] == desired_state:
                    return {
                        "desired_state": row["desired_state"],
                        "generation": int(row["generation"]),
                        "actor": row["actor"],
                        "updated_at": row["updated_at"],
                    }
                if desired_state == "running":
                    active = connection.execute(
                        """
                        SELECT job_id, state FROM jobs
                        WHERE state IN ('preparing', 'running', 'reviewing')
                        ORDER BY created_at, job_id
                        LIMIT 1
                        """
                    ).fetchone()
                    if active is not None:
                        raise TransitionError(
                            "stopped dispatch cannot restart while active Job "
                            f"{active['job_id']} is {active['state']}"
                        )
                now = _utc_text(self._now())
                generation = int(row["generation"]) + 1
                connection.execute(
                    """
                    UPDATE dispatch_control
                    SET desired_state = ?, generation = ?, actor = ?, updated_at = ?
                    WHERE singleton = 1
                    """,
                    (desired_state, generation, actor, now),
                )
                connection.execute(
                    """
                    INSERT INTO dispatch_events(
                        from_state, to_state, generation, actor, created_at
                    ) VALUES (?, ?, ?, ?, ?)
                    """,
                    (row["desired_state"], desired_state, generation, actor, now),
                )
                return {
                    "desired_state": desired_state,
                    "generation": generation,
                    "actor": actor,
                    "updated_at": now,
                }
        finally:
            if connection is not None:
                connection.close()

    def _job_artifact_dir(self, job_id: str) -> Path:
        if JOB_ID_RE.fullmatch(job_id) is None:
            raise HarnessError("invalid Job ID")
        if not self.jobs_root.is_dir() or self.jobs_root.is_symlink():
            raise HarnessError("configured jobs root is missing or unsafe")
        path = self.jobs_root / job_id
        if path.parent != self.jobs_root:
            raise HarnessError("Job artifact path escaped the configured jobs root")
        return path

    def job_execution_lock_path(self, job_id: str) -> Path:
        """Return the canonical supervisor/runtime mutation fence for one Job."""

        if JOB_ID_RE.fullmatch(job_id) is None:
            raise HarnessError("invalid Job ID")
        root = self.execution_locks_root
        if not root.is_dir() or root.is_symlink():
            raise HarnessError("configured execution-lock root is missing or unsafe")
        try:
            _assert_no_symlink_ancestors(root)
            resolved_root = root.resolve(strict=True)
        except (HarnessError, OSError) as error:
            raise HarnessError(f"execution-lock root is unsafe: {error}") from error
        if resolved_root != root:
            raise HarnessError("execution-lock root is not canonical")
        path = root / f"{job_id}.lock"
        if path.parent != root:
            raise HarnessError("Job execution-lock path escaped runtime state")
        return path

    def _acquire_job_execution_fence(self, job_id: str) -> int:
        """Acquire the Job-wide nonblocking fence shared with its supervisor."""

        path = self.job_execution_lock_path(job_id)
        flags = os.O_RDWR | os.O_CREAT
        flags |= getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
        try:
            descriptor = os.open(path, flags, 0o600)
        except OSError as error:
            raise LeaseError(f"could not open Job execution fence: {error}") from error
        try:
            opened = os.fstat(descriptor)
            path_info = os.lstat(path)
            if (
                not stat.S_ISREG(opened.st_mode)
                or stat.S_ISLNK(path_info.st_mode)
                or opened.st_uid != os.geteuid()
                or stat.S_IMODE(opened.st_mode) != 0o600
                or opened.st_nlink != 1
                or (opened.st_dev, opened.st_ino) != (path_info.st_dev, path_info.st_ino)
            ):
                raise LeaseError("Job execution fence is not an owned 0600 single-link file")
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise LeaseError(
                    f"Job {job_id} has an in-flight supervised execution mutation"
                ) from error
            return descriptor
        except Exception:
            os.close(descriptor)
            raise

    @staticmethod
    def _release_job_execution_fence(descriptor: int) -> None:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)

    @contextmanager
    def _job_execution_fence(self, job_id: str) -> Iterator[None]:
        descriptor = self._acquire_job_execution_fence(job_id)
        try:
            yield
        finally:
            self._release_job_execution_fence(descriptor)

    def _validated_job_artifact_dir(self, row: sqlite3.Row) -> Path:
        expected = self._job_artifact_dir(row["job_id"])
        recorded = Path(row["artifact_dir"])
        if recorded != expected:
            raise ConflictError("stored Job artifact directory is outside runtime state")
        try:
            _assert_no_symlink_ancestors(expected)
            jobs_root = self.jobs_root.resolve(strict=True)
            resolved = expected.resolve(strict=True)
        except (HarnessError, OSError) as error:
            raise ConflictError(f"Job artifact directory is unsafe: {error}") from error
        if resolved != jobs_root / row["job_id"] or not resolved.is_dir():
            raise ConflictError("Job artifact directory is missing or redirected")
        return resolved

    def _write_exclusive(self, path: Path, content: bytes) -> str:
        if path.is_symlink():
            raise ConflictError(f"refusing symbolic-link artifact path: {path}")
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        try:
            descriptor = os.open(path, flags, 0o600)
        except FileExistsError:
            if not path.is_file() or path.is_symlink():
                raise ConflictError(f"artifact path is not a regular file: {path}")
            existing = path.read_bytes()
            if existing != content:
                raise ConflictError(f"append-only artifact already exists with other content: {path}")
            return _sha256_bytes(existing)
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(content)
                stream.flush()
                os.fsync(stream.fileno())
        except Exception:
            # Do not unlink a partially written artifact: the tree is append-only.
            raise
        return _sha256_bytes(content)

    def _ensure_artifact_snapshots(
        self,
        job_id: str,
        task_snapshot: dict[str, Any],
        job_snapshot: dict[str, Any],
    ) -> dict[str, tuple[Path, str]]:
        directory = self._job_artifact_dir(job_id)
        try:
            directory.mkdir(mode=0o700)
        except FileExistsError:
            if not directory.is_dir() or directory.is_symlink():
                raise ConflictError(f"unsafe existing artifact path: {directory}")
        if directory.is_symlink():
            raise ConflictError(f"artifact directory must not be a symbolic link: {directory}")
        task_path = directory / "task.json"
        job_path = directory / "job.json"
        return {
            "task_snapshot": (task_path, self._write_exclusive(task_path, _pretty_json(task_snapshot))),
            "job_snapshot": (job_path, self._write_exclusive(job_path, _pretty_json(job_snapshot))),
        }

    @staticmethod
    def _source_hash(record: dict[str, Any]) -> tuple[str, str]:
        source = _canonical_json(record)
        return source, _sha256_bytes(source.encode())

    @staticmethod
    def _latest_task_row(
        connection: sqlite3.Connection,
        task_id: str,
        revision: int | None = None,
    ) -> sqlite3.Row:
        if revision is None:
            row = connection.execute(
                "SELECT * FROM tasks WHERE task_id = ? ORDER BY revision DESC LIMIT 1",
                (task_id,),
            ).fetchone()
        else:
            row = connection.execute(
                "SELECT * FROM tasks WHERE task_id = ? AND revision = ?",
                (task_id, revision),
            ).fetchone()
        if row is None:
            suffix = "" if revision is None else f" revision {revision}"
            raise NotFoundError(f"Task {task_id}{suffix} does not exist")
        return row

    @staticmethod
    def _job_row(connection: sqlite3.Connection, job_id: str) -> sqlite3.Row:
        row = connection.execute("SELECT * FROM jobs WHERE job_id = ?", (job_id,)).fetchone()
        if row is None:
            raise NotFoundError(f"Job {job_id} does not exist")
        return row

    def _assert_dependencies_accepted(
        self, connection: sqlite3.Connection, task_record: dict[str, Any]
    ) -> None:
        for dependency in task_record["context"]["depends_on"]:
            row = connection.execute(
                "SELECT state FROM tasks WHERE task_id = ? ORDER BY revision DESC LIMIT 1",
                (dependency,),
            ).fetchone()
            if row is None:
                raise ConflictError(f"dependency Task {dependency} has not been imported")
            if row["state"] != "accepted":
                raise ConflictError(f"dependency Task {dependency} is not accepted")

    @staticmethod
    def _assert_no_nonterminal_jobs_for_task(
        connection: sqlite3.Connection,
        task_id: str,
        *,
        revision: int | None = None,
    ) -> None:
        parameters: list[Any] = [task_id]
        revision_clause = ""
        if revision is not None:
            revision_clause = " AND task_revision = ?"
            parameters.append(revision)
        placeholders = ",".join("?" for _ in TERMINAL_JOB_STATES)
        parameters.extend(sorted(TERMINAL_JOB_STATES))
        row = connection.execute(
            f"""
            SELECT job_id, state FROM jobs
            WHERE task_id = ?{revision_clause}
              AND state NOT IN ({placeholders})
            ORDER BY attempt, job_id
            LIMIT 1
            """,
            parameters,
        ).fetchone()
        if row is not None:
            suffix = "" if revision is None else f" revision {revision}"
            raise ConflictError(
                f"Task {task_id}{suffix} still has nonterminal Job "
                f"{row['job_id']} in state {row['state']}"
            )

    def _assert_no_dependency_cycle(
        self,
        connection: sqlite3.Connection,
        candidate: dict[str, Any] | None = None,
    ) -> None:
        rows = connection.execute(
            """
            SELECT t.task_id, t.source_json
            FROM tasks t
            JOIN (
                SELECT task_id, MAX(revision) AS revision FROM tasks GROUP BY task_id
            ) latest ON latest.task_id = t.task_id AND latest.revision = t.revision
            """
        ).fetchall()
        graph = {
            row["task_id"]: json.loads(row["source_json"])["context"]["depends_on"]
            for row in rows
        }
        if candidate is not None:
            graph[candidate["id"]] = candidate["context"]["depends_on"]
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(node: str) -> None:
            if node in visiting:
                raise ConflictError(f"Task dependency cycle contains {node}")
            if node in visited:
                return
            visiting.add(node)
            for child in graph.get(node, []):
                if child in graph:
                    visit(child)
            visiting.remove(node)
            visited.add(node)

        for task_id in graph:
            visit(task_id)

    def import_task(self, record: dict[str, Any]) -> dict[str, Any]:
        try:
            validate_task(record)
        except RecordValidationError as error:
            raise HarnessError(str(error)) from error
        if record["status"] != "proposed":
            raise TransitionError(
                "Tasks must be imported as proposed; runtime transitions establish later states"
            )
        if "accepted_commit" in record:
            raise TransitionError("a proposed Task cannot carry accepted_commit")
        source_json, source_sha256 = self._source_hash(record)
        connection = self._connect()
        try:
            with self._transaction(connection):
                now = _utc_text(self._now())
                cross_task_superseded: sqlite3.Row | None = None
                existing = connection.execute(
                    "SELECT * FROM tasks WHERE task_id = ? AND revision = ?",
                    (record["id"], record["revision"]),
                ).fetchone()
                if existing is not None:
                    if existing["source_sha256"] != source_sha256:
                        raise ConflictError(
                            f"Task {record['id']} revision {record['revision']} is immutable"
                        )
                    return self._task_payload(connection, existing)

                latest = connection.execute(
                    "SELECT revision FROM tasks WHERE task_id = ? ORDER BY revision DESC LIMIT 1",
                    (record["id"],),
                ).fetchone()
                if latest is None:
                    if record["revision"] != 1:
                        raise ConflictError("the first revision of a Task must be 1")
                else:
                    expected = int(latest["revision"]) + 1
                    if record["revision"] != expected:
                        raise ConflictError(f"the next Task revision must be {expected}")
                    if record.get("supersedes") != record["id"]:
                        raise ConflictError(
                            "a new revision must name its prior Task ID in supersedes"
                        )
                    self._assert_no_nonterminal_jobs_for_task(
                        connection, record["id"]
                    )
                if "supersedes" in record:
                    if record["supersedes"] != record["id"]:
                        try:
                            cross_task_superseded = self._latest_task_row(
                                connection, record["supersedes"]
                            )
                        except NotFoundError as error:
                            raise ConflictError(
                                f"superseded Task {record['supersedes']} has not been imported"
                            ) from error
                        self._assert_no_nonterminal_jobs_for_task(
                            connection, record["supersedes"]
                        )
                        if cross_task_superseded["state"] not in {
                            "proposed",
                            "ready",
                            "active",
                            "blocked",
                        }:
                            raise ConflictError(
                                "only a proposed, ready, active, or blocked Task may be superseded"
                            )
                        if cross_task_superseded["superseding_task_id"] is not None:
                            raise ConflictError(
                                f"Task {record['supersedes']} already has a replacement"
                            )
                self._assert_no_dependency_cycle(connection, record)
                connection.execute(
                    """
                    INSERT INTO tasks(
                        task_id, revision, state, base_commit, source_json,
                        source_sha256, created_at, updated_at
                    ) VALUES (?, ?, 'proposed', ?, ?, ?, ?, ?)
                    """,
                    (
                        record["id"],
                        record["revision"],
                        record["base_commit"],
                        source_json,
                        source_sha256,
                        now,
                        now,
                    ),
                )
                connection.execute(
                    """
                    INSERT INTO task_events(
                        task_id, revision, event, from_state, to_state, details_json, created_at
                    ) VALUES (?, ?, 'imported', NULL, 'proposed', '{}', ?)
                    """,
                    (record["id"], record["revision"], now),
                )
                if cross_task_superseded is not None:
                    connection.execute(
                        """
                        UPDATE tasks
                        SET state = 'superseded', superseding_task_id = ?, updated_at = ?
                        WHERE task_id = ? AND revision = ?
                        """,
                        (
                            record["id"],
                            now,
                            cross_task_superseded["task_id"],
                            cross_task_superseded["revision"],
                        ),
                    )
                    connection.execute(
                        """
                        INSERT INTO task_events(
                            task_id, revision, event, from_state, to_state,
                            details_json, created_at
                        ) VALUES (?, ?, 'state_transition', ?, 'superseded', ?, ?)
                        """,
                        (
                            cross_task_superseded["task_id"],
                            cross_task_superseded["revision"],
                            cross_task_superseded["state"],
                            _canonical_json({"superseding_task_id": record["id"]}),
                            now,
                        ),
                    )
                row = self._latest_task_row(connection, record["id"], record["revision"])
                return self._task_payload(connection, row)
        finally:
            connection.close()

    def _task_payload(
        self, connection: sqlite3.Connection, row: sqlite3.Row
    ) -> dict[str, Any]:
        document = json.loads(row["source_json"])
        document["status"] = row["state"]
        if row["accepted_commit"] is not None:
            document["accepted_commit"] = row["accepted_commit"]
        else:
            document.pop("accepted_commit", None)
        job_count = connection.execute(
            "SELECT COUNT(*) AS count FROM jobs WHERE task_id = ? AND task_revision = ?",
            (row["task_id"], row["revision"]),
        ).fetchone()["count"]
        return {
            "task": document,
            "runtime": {
                "created_at": row["created_at"],
                "updated_at": row["updated_at"],
                "job_count": job_count,
                "accepted_gate_job_id": row["accepted_gate_job_id"],
                "blocked_reason": row["blocked_reason"],
                "blocked_evidence_job_id": row["blocked_evidence_job_id"],
                "superseding_task_id": row["superseding_task_id"],
            },
        }

    def get_task(self, task_id: str, revision: int | None = None) -> dict[str, Any]:
        connection = self._connect()
        try:
            return self._task_payload(connection, self._latest_task_row(connection, task_id, revision))
        finally:
            connection.close()

    def list_tasks(
        self,
        *,
        state: str | None = None,
        all_revisions: bool = False,
    ) -> list[dict[str, Any]]:
        connection = self._connect()
        try:
            parameters: list[Any] = []
            if all_revisions:
                query = "SELECT * FROM tasks"
            else:
                query = """
                    SELECT t.* FROM tasks t
                    JOIN (
                        SELECT task_id, MAX(revision) AS revision FROM tasks GROUP BY task_id
                    ) latest ON latest.task_id = t.task_id AND latest.revision = t.revision
                """
            if state is not None:
                query += " WHERE t.state = ?" if not all_revisions else " WHERE state = ?"
                parameters.append(state)
            query += " ORDER BY task_id, revision"
            rows = connection.execute(query, parameters).fetchall()
            return [self._task_payload(connection, row) for row in rows]
        finally:
            connection.close()

    def _validate_acceptance_gate(
        self,
        connection: sqlite3.Connection,
        task_row: sqlite3.Row,
        task: dict[str, Any],
        *,
        accepted_commit: str | None,
        gate_job_id: str | None,
    ) -> sqlite3.Row:
        if accepted_commit is None or COMMIT_RE.fullmatch(accepted_commit) is None:
            raise TransitionError(
                "accepted requires --accepted-commit with a 40-character commit"
            )
        if not gate_job_id:
            raise TransitionError("accepted requires --gate-job")
        latest_revision = connection.execute(
            "SELECT MAX(revision) AS revision FROM tasks WHERE task_id = ?",
            (task_row["task_id"],),
        ).fetchone()["revision"]
        if int(latest_revision) != task_row["revision"]:
            raise TransitionError("a stale Task revision cannot be accepted")
        job = self._job_row(connection, gate_job_id)
        if (job["task_id"], job["task_revision"]) != (
            task_row["task_id"],
            task_row["revision"],
        ):
            raise TransitionError("gate Job belongs to another Task revision")
        if job["state"] != "passed" or job["gate_status"] != "passed":
            raise TransitionError("gate Job must be Codex-reviewed and passed")
        if not job["reviewer_identity"] or job["reviewer_identity"] == job["lease_owner"]:
            raise TransitionError("gate Job lacks an independent reviewer identity")
        if job["accepted_commit"] != accepted_commit:
            raise TransitionError("Task accepted commit must equal the reviewed Job commit")
        if job["accepted_tree"] is None:
            raise TransitionError("gate Job has no reviewed commit tree binding")
        accepted_tree = self._validate_reviewed_commit(
            connection, job, task, accepted_commit
        )
        if accepted_tree != job["accepted_tree"]:
            raise TransitionError("reviewed commit tree changed after Job review")
        if not job["gate_result_path"] or not job["gate_result_sha256"]:
            raise TransitionError("gate Job has no recorded gate artifact")
        artifact_dir = self._validated_job_artifact_dir(job)
        gate_path = Path(job["gate_result_path"])
        try:
            relative_gate = gate_path.relative_to(artifact_dir).as_posix()
        except ValueError as error:
            raise TransitionError(
                "recorded gate artifact escaped the Job artifact directory"
            ) from error
        checked_path, content, digest = self._gate_artifact(
            artifact_dir, relative_gate
        )
        if checked_path != gate_path:
            raise TransitionError("recorded gate artifact path was redirected")
        if digest != job["gate_result_sha256"]:
            raise TransitionError("recorded gate artifact changed after Job review")
        artifact = connection.execute(
            """
            SELECT path, sha256 FROM artifact_entries
            WHERE job_id = ? AND name = 'gate_result'
            """,
            (gate_job_id,),
        ).fetchone()
        if (
            artifact is None
            or artifact["path"] != str(gate_path)
            or artifact["sha256"] != digest
        ):
            raise TransitionError("gate artifact registration is missing or inconsistent")
        try:
            gate_document = json.loads(content.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise TransitionError(f"gate artifact is not valid UTF-8 JSON: {error}") from error
        _validate_gate_document(
            gate_document,
            task=task,
            expected_status="passed",
            accepted_commit=accepted_commit,
            accepted_tree=accepted_tree,
            artifact_dir=artifact_dir,
        )
        return job

    def transition_task(
        self,
        task_id: str,
        to_state: str,
        *,
        revision: int | None = None,
        accepted_commit: str | None = None,
        gate_job_id: str | None = None,
        blocked_reason: str | None = None,
        evidence_job_id: str | None = None,
        superseding_task_id: str | None = None,
    ) -> dict[str, Any]:
        allowed = {
            "proposed": {"ready", "superseded"},
            "ready": {"superseded"},
            "active": {"accepted", "blocked", "superseded"},
            "blocked": {"superseded"},
        }
        if blocked_reason is not None:
            _reject_runtime_secrets(blocked_reason, "blocked_reason")
        connection = self._connect()
        try:
            with self._transaction(connection):
                now = _utc_text(self._now())
                row = self._latest_task_row(connection, task_id, revision)
                from_state = row["state"]
                task = json.loads(row["source_json"])
                if from_state == to_state:
                    if to_state == "accepted" and (
                        accepted_commit != row["accepted_commit"]
                        or gate_job_id != row["accepted_gate_job_id"]
                    ):
                        raise ConflictError(
                            "accepted Task retry does not match its recorded commit and gate Job"
                        )
                    if to_state == "accepted":
                        self._validate_acceptance_gate(
                            connection,
                            row,
                            task,
                            accepted_commit=accepted_commit,
                            gate_job_id=gate_job_id,
                        )
                    if to_state == "blocked" and (
                        blocked_reason is None
                        or blocked_reason.strip() != row["blocked_reason"]
                        or evidence_job_id != row["blocked_evidence_job_id"]
                    ):
                        raise ConflictError(
                            "blocked Task retry does not match its recorded reason and evidence Job"
                        )
                    if to_state == "superseded" and (
                        superseding_task_id != row["superseding_task_id"]
                    ):
                        raise ConflictError(
                            "superseded Task retry does not match its recorded replacement"
                        )
                    return self._task_payload(connection, row)
                if to_state not in allowed.get(from_state, set()):
                    raise TransitionError(
                        f"illegal Task transition {from_state} -> {to_state}"
                    )
                details: dict[str, Any] = {}
                updates: dict[str, Any] = {}

                if to_state == "ready":
                    self._assert_no_dependency_cycle(connection)
                    self._assert_dependencies_accepted(connection, task)
                elif to_state == "accepted":
                    self._assert_no_nonterminal_jobs_for_task(
                        connection,
                        row["task_id"],
                        revision=int(row["revision"]),
                    )
                    self._validate_acceptance_gate(
                        connection,
                        row,
                        task,
                        accepted_commit=accepted_commit,
                        gate_job_id=gate_job_id,
                    )
                    updates.update(
                        accepted_commit=accepted_commit,
                        accepted_gate_job_id=gate_job_id,
                    )
                    details.update(
                        accepted_commit=accepted_commit,
                        gate_job_id=gate_job_id,
                    )
                elif to_state == "blocked":
                    self._assert_no_nonterminal_jobs_for_task(
                        connection,
                        row["task_id"],
                        revision=int(row["revision"]),
                    )
                    if blocked_reason is None or not blocked_reason.strip():
                        raise TransitionError("blocked requires an exact nonempty --reason")
                    if not evidence_job_id:
                        raise TransitionError("blocked requires --evidence-job")
                    evidence = self._job_row(connection, evidence_job_id)
                    if (evidence["task_id"], evidence["task_revision"]) != (
                        row["task_id"],
                        row["revision"],
                    ):
                        raise TransitionError("evidence Job belongs to another Task revision")
                    if evidence["state"] not in {"blocked", "rejected"}:
                        raise TransitionError("evidence Job must be blocked or rejected")
                    if not evidence["exit_reason"]:
                        raise TransitionError("evidence Job must record an exit reason")
                    updates.update(
                        blocked_reason=blocked_reason.strip(),
                        blocked_evidence_job_id=evidence_job_id,
                    )
                    details.update(reason=blocked_reason.strip(), evidence_job_id=evidence_job_id)
                elif to_state == "superseded":
                    self._assert_no_nonterminal_jobs_for_task(
                        connection,
                        row["task_id"],
                        revision=int(row["revision"]),
                    )
                    if not superseding_task_id:
                        raise TransitionError("superseded requires --superseding-task")
                    replacement = self._latest_task_row(connection, superseding_task_id)
                    if (replacement["task_id"], replacement["revision"]) == (
                        row["task_id"],
                        row["revision"],
                    ):
                        raise TransitionError("a Task revision cannot supersede itself")
                    replacement_doc = json.loads(replacement["source_json"])
                    if replacement_doc.get("supersedes") != row["task_id"]:
                        raise TransitionError(
                            "replacement Task does not name the current Task in supersedes"
                        )
                    updates["superseding_task_id"] = superseding_task_id
                    details["superseding_task_id"] = superseding_task_id

                assignments = ["state = ?", "updated_at = ?"]
                values: list[Any] = [to_state, now]
                for column, value in updates.items():
                    assignments.append(f"{column} = ?")
                    values.append(value)
                values.extend([row["task_id"], row["revision"]])
                connection.execute(
                    f"UPDATE tasks SET {', '.join(assignments)} WHERE task_id = ? AND revision = ?",
                    values,
                )
                connection.execute(
                    """
                    INSERT INTO task_events(
                        task_id, revision, event, from_state, to_state, details_json, created_at
                    ) VALUES (?, ?, 'state_transition', ?, ?, ?, ?)
                    """,
                    (
                        row["task_id"],
                        row["revision"],
                        from_state,
                        to_state,
                        _canonical_json(details),
                        now,
                    ),
                )
                return self._task_payload(
                    connection,
                    self._latest_task_row(connection, row["task_id"], row["revision"]),
                )
        finally:
            connection.close()

    def enqueue_job(self, record: dict[str, Any]) -> dict[str, Any]:
        try:
            validate_job(record)
        except RecordValidationError as error:
            raise HarnessError(str(error)) from error
        if record["state"] != "queued":
            raise TransitionError("Jobs must be enqueued in queued state")
        if record["gate"]["status"] != "not_run" or "result_path" in record["gate"]:
            raise TransitionError("a queued Job gate must be not_run without a result")
        forbidden_lifecycle = {
            "started_at",
            "heartbeat_at",
            "finished_at",
            "exit_reason",
            "accepted_commit",
        }
        present = sorted(forbidden_lifecycle & record.keys())
        if present:
            raise TransitionError(f"queued Job carries lifecycle fields: {', '.join(present)}")
        expected_artifact_dir = f"harness/v2/state/jobs/{record['id']}"
        if record["artifacts"]["directory"] != expected_artifact_dir:
            raise ConflictError(
                f"Job artifacts.directory must be {expected_artifact_dir!r}"
            )
        worktree_path = Path(record["workspace"]["worktree"])
        if not worktree_path.is_absolute():
            raise ConflictError("Job workspace.worktree must be an absolute path")
        if ".." in worktree_path.parts:
            raise ConflictError("Job workspace.worktree must not contain '..'")
        expected_branch_prefix = f"codex/{record['task_id']}/"
        if not record["workspace"]["branch"].startswith(expected_branch_prefix):
            raise ConflictError(
                f"Job branch must start with {expected_branch_prefix!r}"
            )
        branch_suffix = record["workspace"]["branch"][len(expected_branch_prefix) :]
        if not branch_suffix or ".." in branch_suffix or "//" in branch_suffix:
            raise ConflictError("Job branch must have a safe nonempty attempt suffix")
        lease_expiry = datetime.fromisoformat(
            record["workspace"]["lease_expires_at"].replace("Z", "+00:00")
        )
        if lease_expiry.astimezone(timezone.utc) <= self._now():
            raise ConflictError("queued Job lease_expires_at must be in the future")

        source_json, source_sha256 = self._source_hash(record)
        connection = self._connect()
        try:
            with self._transaction(connection):
                now = _utc_text(self._now())
                existing = connection.execute(
                    "SELECT * FROM jobs WHERE job_id = ?", (record["id"],)
                ).fetchone()
                if existing is not None:
                    if existing["source_sha256"] != source_sha256:
                        raise ConflictError(f"Job {record['id']} is immutable")
                    return self._job_payload(connection, existing)

                task_row = self._latest_task_row(
                    connection, record["task_id"], record["task_revision"]
                )
                latest_revision = connection.execute(
                    "SELECT MAX(revision) AS revision FROM tasks WHERE task_id = ?",
                    (record["task_id"],),
                ).fetchone()["revision"]
                if int(latest_revision) != record["task_revision"]:
                    raise ConflictError("Jobs may only target the latest Task revision")
                if task_row["state"] not in {"ready", "active"}:
                    raise TransitionError("Job Task must be ready or active")
                task = json.loads(task_row["source_json"])
                self._assert_dependencies_accepted(connection, task)
                if record["workspace"]["base_commit"] != task_row["base_commit"]:
                    raise ConflictError("Job and Task base commits differ")
                self._validate_job_worktree(connection, record, required=False)
                maximum = connection.execute(
                    """
                    SELECT MAX(attempt) AS attempt FROM jobs
                    WHERE task_id = ? AND task_revision = ?
                    """,
                    (record["task_id"], record["task_revision"]),
                ).fetchone()["attempt"]
                expected_attempt = 1 if maximum is None else int(maximum) + 1
                if record["attempt"] != expected_attempt:
                    raise ConflictError(f"next Job attempt must be {expected_attempt}")
                if maximum is not None:
                    prior = connection.execute(
                        """
                        SELECT state FROM jobs
                        WHERE task_id = ? AND task_revision = ? AND attempt = ?
                        """,
                        (record["task_id"], record["task_revision"], int(maximum)),
                    ).fetchone()
                    if prior["state"] not in TERMINAL_JOB_STATES:
                        raise ConflictError("the prior Job attempt is not terminal")
                if record["attempt"] > task["budget"]["max_attempts"]:
                    raise ConflictError("Job attempt exceeds the Task max_attempts budget")
                requested_tokens = record["backend"]["sampling"].get("max_tokens")
                if requested_tokens is not None:
                    if isinstance(requested_tokens, bool) or not isinstance(requested_tokens, int):
                        raise ConflictError("backend.sampling.max_tokens must be an integer")
                    if requested_tokens < 1:
                        raise ConflictError("backend.sampling.max_tokens must be positive")
                    if requested_tokens > task["budget"]["max_output_tokens"]:
                        raise ConflictError("Job max_tokens exceeds the Task token budget")

                task_snapshot = dict(task)
                task_snapshot["status"] = "active"
                snapshots = self._ensure_artifact_snapshots(
                    record["id"], task_snapshot, record
                )
                artifact_dir = str(self._job_artifact_dir(record["id"]))
                connection.execute(
                    """
                    INSERT INTO jobs(
                        job_id, task_id, task_revision, attempt, state,
                        source_json, source_sha256, artifact_dir, gate_status,
                        created_at, updated_at
                    ) VALUES (?, ?, ?, ?, 'queued', ?, ?, ?, 'not_run', ?, ?)
                    """,
                    (
                        record["id"],
                        record["task_id"],
                        record["task_revision"],
                        record["attempt"],
                        source_json,
                        source_sha256,
                        artifact_dir,
                        now,
                        now,
                    ),
                )
                for name, (path, digest) in snapshots.items():
                    connection.execute(
                        """
                        INSERT INTO artifact_entries(job_id, name, path, sha256, created_at)
                        VALUES (?, ?, ?, ?, ?)
                        """,
                        (record["id"], name, str(path), digest, now),
                    )
                connection.execute(
                    """
                    INSERT INTO job_events(
                        job_id, event, from_state, to_state, owner, details_json, created_at
                    ) VALUES (?, 'enqueued', NULL, 'queued', NULL, '{}', ?)
                    """,
                    (record["id"], now),
                )
                if task_row["state"] == "ready":
                    connection.execute(
                        """
                        UPDATE tasks SET state = 'active', updated_at = ?
                        WHERE task_id = ? AND revision = ?
                        """,
                        (now, task_row["task_id"], task_row["revision"]),
                    )
                    connection.execute(
                        """
                        INSERT INTO task_events(
                            task_id, revision, event, from_state, to_state,
                            details_json, created_at
                        ) VALUES (?, ?, 'first_job_enqueued', 'ready', 'active', ?, ?)
                        """,
                        (
                            task_row["task_id"],
                            task_row["revision"],
                            _canonical_json({"job_id": record["id"]}),
                            now,
                        ),
                    )
                row = self._job_row(connection, record["id"])
                payload = self._job_payload(connection, row)
            return payload
        finally:
            connection.close()

    def _job_payload(self, connection: sqlite3.Connection, row: sqlite3.Row) -> dict[str, Any]:
        self._validated_job_artifact_dir(row)
        document = json.loads(row["source_json"])
        document["state"] = row["state"]
        if row["lease_owner"] is not None:
            document["workspace"]["lease_owner"] = row["lease_owner"]
        if row["lease_expires_at"] is not None:
            document["workspace"]["lease_expires_at"] = _epoch_to_text(
                row["lease_expires_at"]
            )
        for name in ("started_at", "heartbeat_at", "finished_at", "exit_reason"):
            if row[name] is not None:
                document[name] = row[name]
            else:
                document.pop(name, None)
        document["gate"] = {"status": row["gate_status"]}
        if row["gate_result_path"] is not None:
            try:
                relative_gate = Path(row["gate_result_path"]).relative_to(
                    Path(row["artifact_dir"])
                )
            except ValueError as error:
                raise ConflictError("stored gate path escaped its Job artifact directory") from error
            document["gate"]["result_path"] = relative_gate.as_posix()
        if row["accepted_commit"] is not None:
            document["accepted_commit"] = row["accepted_commit"]
        else:
            document.pop("accepted_commit", None)
        now_epoch = self._now().timestamp()
        leases = connection.execute(
            """
            SELECT scope, owner, generation, expires_at
            FROM file_leases WHERE job_id = ? ORDER BY scope
            """,
            (row["job_id"],),
        ).fetchall()
        worktree_validated = self._validate_job_worktree(
            connection, document, required=False
        )
        return {
            "job": document,
            "runtime": {
                "artifact_directory": row["artifact_dir"],
                "worktree_validation": (
                    "validated" if worktree_validated else "deferred_until_claim"
                ),
                "reviewer_identity": row["reviewer_identity"],
                "reviewed_at": row["reviewed_at"],
                "lease_active": bool(
                    row["state"] in ACTIVE_JOB_STATES
                    and row["lease_expires_at"] is not None
                    and row["lease_expires_at"] > now_epoch
                ),
                "lease_token": row["lease_generation"] or None,
                "lease_dispatch_generation": row["lease_dispatch_generation"],
                "gate_result_sha256": row["gate_result_sha256"],
                "accepted_tree": row["accepted_tree"],
                "created_at": row["created_at"],
                "updated_at": row["updated_at"],
                "scopes": [
                    {
                        "path": lease["scope"],
                        "owner": lease["owner"],
                        "lease_token": lease["generation"],
                        "expires_at": _epoch_to_text(lease["expires_at"]),
                        "active": lease["expires_at"] > now_epoch,
                    }
                    for lease in leases
                ],
            },
        }

    def get_job(self, job_id: str) -> dict[str, Any]:
        connection = self._connect()
        try:
            return self._job_payload(connection, self._job_row(connection, job_id))
        finally:
            connection.close()

    def list_jobs(
        self,
        *,
        state: str | None = None,
        task_id: str | None = None,
    ) -> list[dict[str, Any]]:
        connection = self._connect()
        try:
            clauses: list[str] = []
            parameters: list[Any] = []
            if state is not None:
                clauses.append("state = ?")
                parameters.append(state)
            if task_id is not None:
                clauses.append("task_id = ?")
                parameters.append(task_id)
            query = "SELECT * FROM jobs"
            if clauses:
                query += " WHERE " + " AND ".join(clauses)
            query += " ORDER BY created_at, job_id"
            return [
                self._job_payload(connection, row)
                for row in connection.execute(query, parameters).fetchall()
            ]
        finally:
            connection.close()

    @staticmethod
    def _lease_seconds(value: int) -> int:
        if isinstance(value, bool) or not isinstance(value, int) or value < 1:
            raise LeaseError("lease duration must be a positive integer")
        if value > 7 * 24 * 60 * 60:
            raise LeaseError("lease duration may not exceed seven days")
        return value

    def _scope_conflict(
        self,
        connection: sqlite3.Connection,
        scopes: Sequence[str],
        job_id: str,
        now_epoch: float,
        stale_execution_fences: dict[str, int],
    ) -> str | None:
        held_scopes = connection.execute(
            """
            SELECT scope, job_id, owner, expires_at FROM file_leases
            WHERE job_id != ?
            """,
            (job_id,),
        ).fetchall()
        for requested in scopes:
            for held in held_scopes:
                if not scopes_overlap(requested, held["scope"]):
                    continue
                if held["expires_at"] > now_epoch:
                    return (
                        f"scope {requested!r} overlaps {held['scope']!r} held by "
                        f"Job {held['job_id']} owner {held['owner']}"
                    )
                holder_job_id = held["job_id"]
                if holder_job_id in stale_execution_fences:
                    continue
                try:
                    stale_execution_fences[holder_job_id] = (
                        self._acquire_job_execution_fence(holder_job_id)
                    )
                except LeaseError:
                    return (
                        f"scope {requested!r} overlaps expired lease {held['scope']!r} "
                        f"whose Job {holder_job_id} still has an in-flight execution"
                    )
        return None

    def claim_job(
        self,
        *,
        owner: str,
        lease_seconds: int,
        job_id: str | None = None,
    ) -> dict[str, Any]:
        if not owner or not owner.strip():
            raise LeaseError("lease owner must not be empty")
        owner = owner.strip()
        _reject_runtime_secrets(owner, "lease_owner")
        duration = self._lease_seconds(lease_seconds)
        connection = self._connect()
        execution_descriptor: int | None = None
        stale_execution_fences: dict[str, int] = {}
        try:
            with self._transaction(connection):
                now_moment = self._now()
                now = _utc_text(now_moment)
                now_epoch = now_moment.timestamp()
                expiry = (now_moment + timedelta(seconds=duration)).timestamp()
                dispatch = self._assert_dispatch_running(connection)
                dispatch_generation = int(dispatch["generation"])
                if job_id is not None:
                    candidates = [self._job_row(connection, job_id)]
                else:
                    candidates = connection.execute(
                        """
                        SELECT * FROM jobs
                        WHERE state = 'queued'
                           OR (state IN ('preparing', 'running', 'reviewing')
                               AND lease_expires_at <= ?)
                        ORDER BY
                            CASE WHEN state = 'queued' THEN 1 ELSE 0 END,
                            created_at,
                            job_id
                        """,
                        (now_epoch,),
                    ).fetchall()
                if not candidates:
                    raise NotFoundError("no queued or expired recoverable Job is available")

                selected: sqlite3.Row | None = None
                selected_task: sqlite3.Row | None = None
                selected_scopes: list[str] = []
                last_conflict: str | None = None
                for candidate in candidates:
                    if candidate["state"] in TERMINAL_JOB_STATES:
                        last_conflict = f"Job {candidate['job_id']} is terminal"
                        continue
                    if (
                        candidate["state"] in ACTIVE_JOB_STATES
                        and candidate["lease_dispatch_generation"]
                        != dispatch_generation
                    ):
                        last_conflict = (
                            f"Job {candidate['job_id']} belongs to an earlier dispatch "
                            "generation and must be interrupted before relaunch"
                        )
                        continue
                    latest_revision = connection.execute(
                        "SELECT MAX(revision) AS revision FROM tasks WHERE task_id = ?",
                        (candidate["task_id"],),
                    ).fetchone()["revision"]
                    if int(latest_revision) != candidate["task_revision"]:
                        last_conflict = (
                            f"Job {candidate['job_id']} targets stale Task revision "
                            f"{candidate['task_revision']}"
                        )
                        continue
                    candidate_document = json.loads(candidate["source_json"])
                    try:
                        self._validate_job_worktree(
                            connection, candidate_document, required=True
                        )
                    except ConflictError as error:
                        last_conflict = str(error)
                        continue
                    if candidate["state"] in ACTIVE_JOB_STATES:
                        if candidate["lease_expires_at"] is not None and candidate[
                            "lease_expires_at"
                        ] > now_epoch:
                            if candidate["lease_owner"] == owner:
                                with self._job_execution_fence(candidate["job_id"]):
                                    return self._job_payload(connection, candidate)
                            last_conflict = (
                                f"Job {candidate['job_id']} is leased by "
                                f"{candidate['lease_owner']}"
                            )
                            continue
                    task_row = self._latest_task_row(
                        connection, candidate["task_id"], candidate["task_revision"]
                    )
                    if task_row["state"] != "active":
                        last_conflict = (
                            f"Job {candidate['job_id']} Task is {task_row['state']}"
                        )
                        continue
                    task = json.loads(task_row["source_json"])
                    scopes = [normalize_scope(path)[0] for path in task["scope"]["allowed_paths"]]
                    candidate_stale_fences: dict[str, int] = {}
                    conflict = self._scope_conflict(
                        connection,
                        scopes,
                        candidate["job_id"],
                        now_epoch,
                        candidate_stale_fences,
                    )
                    if conflict:
                        for descriptor in candidate_stale_fences.values():
                            self._release_job_execution_fence(descriptor)
                        last_conflict = conflict
                        continue
                    stale_execution_fences.update(candidate_stale_fences)
                    try:
                        execution_descriptor = self._acquire_job_execution_fence(
                            candidate["job_id"]
                        )
                    except LeaseError as error:
                        last_conflict = str(error)
                        continue
                    selected = candidate
                    selected_task = task_row
                    selected_scopes = scopes
                    break
                if selected is None or selected_task is None:
                    raise LeaseError(last_conflict or "no claimable Job has a free file scope")

                prior_state = selected["state"]
                recovered = prior_state in ACTIVE_JOB_STATES
                new_state = prior_state if recovered else "preparing"
                generation = int(selected["lease_generation"] or 0) + 1
                started_at = selected["started_at"] or now
                connection.execute(
                    """
                    UPDATE jobs
                    SET state = ?, lease_owner = ?, lease_expires_at = ?,
                        lease_generation = ?, lease_dispatch_generation = ?,
                        started_at = ?, heartbeat_at = ?, updated_at = ?
                    WHERE job_id = ?
                    """,
                    (
                        new_state,
                        owner,
                        expiry,
                        generation,
                        dispatch_generation,
                        started_at,
                        now,
                        now,
                        selected["job_id"],
                    ),
                )
                lease_event = "recovered" if recovered else "acquired"
                for scope in selected_scopes:
                    _, prefix = normalize_scope(scope)
                    acquired_at = now
                    old = connection.execute(
                        "SELECT acquired_at FROM file_leases WHERE scope = ?", (scope,)
                    ).fetchone()
                    if old is not None and recovered:
                        acquired_at = old["acquired_at"]
                    connection.execute(
                        """
                        INSERT INTO file_leases(
                            scope, literal_prefix, job_id, owner, generation,
                            acquired_at, heartbeat_at, expires_at
                        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                        ON CONFLICT(scope) DO UPDATE SET
                            literal_prefix = excluded.literal_prefix,
                            job_id = excluded.job_id,
                            owner = excluded.owner,
                            generation = excluded.generation,
                            acquired_at = excluded.acquired_at,
                            heartbeat_at = excluded.heartbeat_at,
                            expires_at = excluded.expires_at
                        """,
                        (
                            scope,
                            prefix,
                            selected["job_id"],
                            owner,
                            generation,
                            acquired_at,
                            now,
                            expiry,
                        ),
                    )
                    connection.execute(
                        """
                        INSERT INTO lease_events(
                            scope, job_id, owner, generation, event, expires_at, created_at
                        ) VALUES (?, ?, ?, ?, ?, ?, ?)
                        """,
                        (
                            scope,
                            selected["job_id"],
                            owner,
                            generation,
                            lease_event,
                            expiry,
                            now,
                        ),
                    )
                connection.execute(
                    """
                    INSERT INTO job_events(
                        job_id, event, from_state, to_state, owner, details_json, created_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        selected["job_id"],
                        "lease_recovered" if recovered else "claimed",
                        prior_state,
                        new_state,
                        owner,
                        _canonical_json(
                            {"lease_expires_at": _epoch_to_text(expiry), "lease_token": generation}
                        ),
                        now,
                    ),
                )
                payload = self._job_payload(
                    connection, self._job_row(connection, selected["job_id"])
                )
            return payload
        finally:
            if execution_descriptor is not None:
                self._release_job_execution_fence(execution_descriptor)
            for descriptor in stale_execution_fences.values():
                self._release_job_execution_fence(descriptor)
            connection.close()

    def _assert_current_lease(
        self,
        row: sqlite3.Row,
        *,
        owner: str,
        lease_token: int,
        now_epoch: float,
    ) -> None:
        if row["state"] not in ACTIVE_JOB_STATES:
            raise LeaseError(f"Job {row['job_id']} is not active")
        if row["lease_owner"] != owner:
            raise LeaseError(f"Job {row['job_id']} is leased by another owner")
        if int(row["lease_generation"] or 0) != lease_token:
            raise LeaseError("stale lease token")
        if row["lease_expires_at"] is None or row["lease_expires_at"] <= now_epoch:
            raise LeaseError("Job lease expired; claim it for recovery before continuing")

    def _assert_reviewable_lease(
        self,
        connection: sqlite3.Connection,
        row: sqlite3.Row,
        *,
        now_epoch: float,
    ) -> None:
        owner = row["lease_owner"]
        generation = int(row["lease_generation"] or 0)
        if owner is None or generation < 1:
            raise LeaseError("reviewing Job has no fenced worker lease")
        self._assert_current_lease(
            row,
            owner=owner,
            lease_token=generation,
            now_epoch=now_epoch,
        )
        task_row = self._latest_task_row(
            connection, row["task_id"], row["task_revision"]
        )
        expected_scopes = {
            normalize_scope(path)[0]
            for path in json.loads(task_row["source_json"])["scope"]["allowed_paths"]
        }
        leases = connection.execute(
            "SELECT * FROM file_leases WHERE job_id = ?", (row["job_id"],)
        ).fetchall()
        if {lease["scope"] for lease in leases} != expected_scopes:
            raise LeaseError("reviewing Job no longer owns its complete file scope")
        for lease in leases:
            if (
                lease["owner"] != owner
                or int(lease["generation"]) != generation
                or lease["expires_at"] <= now_epoch
            ):
                raise LeaseError("reviewing Job has a stale or incomplete file-scope lease")

    @staticmethod
    def _row_fingerprint(row: sqlite3.Row | None) -> tuple[tuple[str, Any], ...] | None:
        if row is None:
            return None
        return tuple((key, row[key]) for key in row.keys())

    def _review_authority_snapshot(
        self, connection: sqlite3.Connection, job_id: str
    ) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
        """Capture every SQLite authority fact on which a review depends."""

        row = self._job_row(connection, job_id)
        task_row = self._latest_task_row(
            connection, row["task_id"], row["task_revision"]
        )
        latest_revision = connection.execute(
            "SELECT MAX(revision) AS revision FROM tasks WHERE task_id = ?",
            (row["task_id"],),
        ).fetchone()
        dispatch = self._dispatch_row(connection)
        runtime_config = connection.execute(
            "SELECT * FROM runtime_config WHERE singleton = 1"
        ).fetchone()
        leases = connection.execute(
            "SELECT * FROM file_leases WHERE job_id = ? ORDER BY scope",
            (job_id,),
        ).fetchall()
        worker_owners = connection.execute(
            """
            SELECT DISTINCT owner FROM lease_events
            WHERE job_id = ? AND event IN ('acquired', 'recovered')
            ORDER BY owner
            """,
            (job_id,),
        ).fetchall()
        artifacts = connection.execute(
            "SELECT * FROM artifact_entries WHERE job_id = ? ORDER BY name",
            (job_id,),
        ).fetchall()
        snapshot = {
            "job": self._row_fingerprint(row),
            "task": self._row_fingerprint(task_row),
            "latest_revision": int(latest_revision["revision"]),
            "dispatch": self._row_fingerprint(dispatch),
            "runtime_config": self._row_fingerprint(runtime_config),
            "leases": tuple(self._row_fingerprint(item) for item in leases),
            "worker_owners": tuple(item["owner"] for item in worker_owners),
            "artifacts": tuple(self._row_fingerprint(item) for item in artifacts),
        }
        return dict(row), dict(task_row), snapshot

    def heartbeat_job(
        self,
        job_id: str,
        *,
        owner: str,
        lease_token: int,
        lease_seconds: int,
        to_state: str | None = None,
    ) -> dict[str, Any]:
        duration = self._lease_seconds(lease_seconds)
        if not owner or not owner.strip():
            raise LeaseError("lease owner must not be empty")
        _reject_runtime_secrets(owner.strip(), "lease_owner")
        execution_descriptor = (
            self._acquire_job_execution_fence(job_id)
            if to_state == "reviewing"
            else None
        )
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            with self._transaction(connection):
                now_moment = self._now()
                now = _utc_text(now_moment)
                now_epoch = now_moment.timestamp()
                expiry = (now_moment + timedelta(seconds=duration)).timestamp()
                row = self._job_row(connection, job_id)
                job_document = json.loads(row["source_json"])
                self._validate_job_worktree(connection, job_document, required=True)
                self._assert_active_lease_dispatch_epoch(connection, row)
                latest_revision = connection.execute(
                    "SELECT MAX(revision) AS revision FROM tasks WHERE task_id = ?",
                    (row["task_id"],),
                ).fetchone()["revision"]
                if int(latest_revision) != row["task_revision"]:
                    raise TransitionError("Job targets a stale Task revision")
                self._assert_current_lease(
                    row, owner=owner.strip(), lease_token=lease_token, now_epoch=now_epoch
                )
                from_state = row["state"]
                if from_state == "reviewing" and execution_descriptor is None:
                    execution_descriptor = self._acquire_job_execution_fence(job_id)
                target = from_state if to_state is None else to_state
                legal = {"preparing": {"preparing", "running"}, "running": {"running", "reviewing"}, "reviewing": {"reviewing"}}
                if target not in legal[from_state]:
                    raise TransitionError(
                        f"illegal heartbeat Job transition {from_state} -> {target}"
                    )
                scopes = connection.execute(
                    "SELECT * FROM file_leases WHERE job_id = ?", (job_id,)
                ).fetchall()
                task_row = self._latest_task_row(
                    connection, row["task_id"], row["task_revision"]
                )
                expected_scopes = {
                    normalize_scope(path)[0]
                    for path in json.loads(task_row["source_json"])["scope"]["allowed_paths"]
                }
                held_scopes = {scope["scope"] for scope in scopes}
                if held_scopes != expected_scopes:
                    raise LeaseError("Job no longer owns its complete file scope")
                for scope in scopes:
                    if (
                        scope["owner"] != owner.strip()
                        or scope["generation"] != lease_token
                        or scope["expires_at"] <= now_epoch
                    ):
                        raise LeaseError("one or more file-scope leases were lost")
                    connection.execute(
                        """
                        UPDATE file_leases SET heartbeat_at = ?, expires_at = ?
                        WHERE scope = ?
                        """,
                        (now, expiry, scope["scope"]),
                    )
                    connection.execute(
                        """
                        INSERT INTO lease_events(
                            scope, job_id, owner, generation, event, expires_at, created_at
                        ) VALUES (?, ?, ?, ?, 'renewed', ?, ?)
                        """,
                        (scope["scope"], job_id, owner.strip(), lease_token, expiry, now),
                    )
                connection.execute(
                    """
                    UPDATE jobs SET state = ?, heartbeat_at = ?, lease_expires_at = ?, updated_at = ?
                    WHERE job_id = ?
                    """,
                    (target, now, expiry, now, job_id),
                )
                connection.execute(
                    """
                    INSERT INTO job_events(
                        job_id, event, from_state, to_state, owner, details_json, created_at
                    ) VALUES (?, 'heartbeat', ?, ?, ?, ?, ?)
                    """,
                    (
                        job_id,
                        from_state,
                        target,
                        owner.strip(),
                        _canonical_json(
                            {"lease_expires_at": _epoch_to_text(expiry), "lease_token": lease_token}
                        ),
                        now,
                    ),
                )
                payload = self._job_payload(connection, self._job_row(connection, job_id))
            return payload
        finally:
            if connection is not None:
                connection.close()
            if execution_descriptor is not None:
                self._release_job_execution_fence(execution_descriptor)

    def _gate_artifact(
        self, artifact_dir: Path, result_path: str
    ) -> tuple[Path, bytes, str]:
        if not result_path or Path(result_path).is_absolute() or ".." in Path(result_path).parts:
            raise ConflictError("gate result must be a relative path inside the Job artifact directory")
        if artifact_dir.is_symlink():
            raise ConflictError("Job artifact directory is a symbolic link")
        root = artifact_dir.resolve(strict=True)
        unresolved = root / result_path
        try:
            _assert_no_symlink_ancestors(unresolved)
        except HarnessError as error:
            raise ConflictError(f"gate result path is unsafe: {error}") from error
        if unresolved.is_symlink():
            raise ConflictError("gate result must not be a symbolic link")
        candidate = unresolved.resolve(strict=True)
        if candidate.parent != root and root not in candidate.parents:
            raise ConflictError("gate result escaped the Job artifact directory")
        if not candidate.is_file() or candidate.is_symlink():
            raise ConflictError("gate result must be a regular non-symlink file")
        content, digest = _read_regular_file_safely(
            candidate, maximum_bytes=MAX_GATE_BYTES
        )
        return candidate, content, digest

    @staticmethod
    def _file_identity(path: Path) -> tuple[int, ...]:
        metadata = os.stat(path, follow_symlinks=False)
        if not stat.S_ISREG(metadata.st_mode):
            raise ConflictError("review evidence is no longer a regular file")
        return (
            metadata.st_dev,
            metadata.st_ino,
            metadata.st_mode,
            metadata.st_uid,
            metadata.st_nlink,
            metadata.st_size,
            metadata.st_mtime_ns,
            metadata.st_ctime_ns,
        )

    def _register_prevalidated_gate(
        self,
        connection: sqlite3.Connection,
        row: sqlite3.Row | dict[str, Any],
        *,
        gate_path: Path,
        gate_digest: str,
        now: str,
    ) -> None:
        existing = connection.execute(
            """
            SELECT * FROM artifact_entries
            WHERE job_id = ? AND name = 'gate_result'
            """,
            (row["job_id"],),
        ).fetchone()
        if existing is not None and (
            existing["path"] != str(gate_path)
            or existing["sha256"] != gate_digest
        ):
            raise ConflictError("gate artifact registration is immutable")
        if existing is None:
            connection.execute(
                """
                INSERT INTO artifact_entries(job_id, name, path, sha256, created_at)
                VALUES (?, 'gate_result', ?, ?, ?)
                """,
                (row["job_id"], str(gate_path), gate_digest, now),
            )

    def _register_validated_gate(
        self,
        connection: sqlite3.Connection,
        row: sqlite3.Row,
        *,
        task: dict[str, Any],
        gate_status: str,
        gate_result: str,
        reviewed_commit: str,
        reviewed_tree: str,
        now: str,
    ) -> tuple[Path, str]:
        artifact_dir = self._validated_job_artifact_dir(row)
        gate_path, content, gate_digest = self._gate_artifact(artifact_dir, gate_result)
        try:
            document = json.loads(content.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise TransitionError(f"gate artifact is not valid UTF-8 JSON: {error}") from error
        _validate_gate_document(
            document,
            task=task,
            expected_status=gate_status,
            accepted_commit=reviewed_commit,
            accepted_tree=reviewed_tree,
            artifact_dir=artifact_dir,
        )
        self._register_prevalidated_gate(
            connection,
            row,
            gate_path=gate_path,
            gate_digest=gate_digest,
            now=now,
        )
        return gate_path, gate_digest

    def _record_job_completion(
        self,
        connection: sqlite3.Connection,
        row: sqlite3.Row,
        *,
        state: str,
        exit_reason: str,
        gate_status: str,
        gate_path: Path | None,
        gate_digest: str | None,
        reviewed_commit: str | None,
        reviewed_tree: str | None,
        actor: str,
        reviewer_identity: str | None,
        now: str,
        now_epoch: float,
    ) -> dict[str, Any]:
        artifact_dir = self._validated_job_artifact_dir(row)
        relative_gate = (
            None
            if gate_path is None
            else gate_path.relative_to(artifact_dir).as_posix()
        )
        result_document = {
            "accepted_commit": reviewed_commit,
            "accepted_tree": reviewed_tree,
            "exit_reason": exit_reason,
            "gate": {
                "result_path": relative_gate,
                "sha256": gate_digest,
                "status": gate_status,
            },
            "job_id": row["job_id"],
            "reviewer_identity": reviewer_identity,
            "state": state,
        }
        result_path = artifact_dir / "result.json"
        result_digest = self._write_exclusive(
            result_path, _pretty_json(result_document)
        )
        connection.execute(
            """
            INSERT INTO artifact_entries(job_id, name, path, sha256, created_at)
            VALUES (?, 'result_snapshot', ?, ?, ?)
            """,
            (row["job_id"], str(result_path), result_digest, now),
        )
        connection.execute(
            """
            UPDATE jobs
            SET state = ?, finished_at = ?, heartbeat_at = ?, lease_expires_at = ?,
                exit_reason = ?, gate_status = ?, gate_result_path = ?,
                gate_result_sha256 = ?, accepted_commit = ?, accepted_tree = ?,
                reviewer_identity = ?,
                reviewed_at = ?, updated_at = ?
            WHERE job_id = ?
            """,
            (
                state,
                now,
                now,
                now_epoch,
                exit_reason,
                gate_status,
                None if gate_path is None else str(gate_path),
                gate_digest,
                reviewed_commit,
                reviewed_tree,
                reviewer_identity,
                now if reviewer_identity is not None else None,
                now,
                row["job_id"],
            ),
        )
        leases = connection.execute(
            "SELECT * FROM file_leases WHERE job_id = ?", (row["job_id"],)
        ).fetchall()
        for lease in leases:
            connection.execute(
                "UPDATE file_leases SET heartbeat_at = ?, expires_at = ? WHERE scope = ?",
                (now, now_epoch, lease["scope"]),
            )
            connection.execute(
                """
                INSERT INTO lease_events(
                    scope, job_id, owner, generation, event, expires_at, created_at
                ) VALUES (?, ?, ?, ?, 'released', ?, ?)
                """,
                (
                    lease["scope"],
                    row["job_id"],
                    lease["owner"],
                    lease["generation"],
                    now_epoch,
                    now,
                ),
            )
        connection.execute(
            """
            INSERT INTO job_events(
                job_id, event, from_state, to_state, owner, details_json, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
            (
                row["job_id"],
                "reviewed" if reviewer_identity is not None else "finished",
                row["state"],
                state,
                actor,
                _canonical_json(
                    {
                        "exit_reason": exit_reason,
                        "gate_status": gate_status,
                        "reviewer_identity": reviewer_identity,
                    }
                ),
                now,
            ),
        )
        return self._job_payload(connection, self._job_row(connection, row["job_id"]))

    def finish_job(
        self,
        job_id: str,
        *,
        owner: str,
        lease_token: int,
        state: str,
        exit_reason: str,
        gate_status: str = "not_run",
        gate_result: str | None = None,
        accepted_commit: str | None = None,
    ) -> dict[str, Any]:
        if state not in {"blocked", "interrupted"}:
            raise TransitionError(
                "worker finish only supports blocked/interrupted; use job review for pass/reject"
            )
        if not exit_reason or not exit_reason.strip():
            raise TransitionError("finish requires a nonempty exit reason")
        _reject_runtime_secrets(exit_reason.strip(), "exit_reason")
        _reject_runtime_secrets(owner.strip(), "lease_owner")
        if gate_status != "not_run" or gate_result is not None or accepted_commit is not None:
            raise TransitionError("worker finish cannot record gate or accepted-commit evidence")
        execution_descriptor = self._acquire_job_execution_fence(job_id)
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            with self._transaction(connection):
                now_moment = self._now()
                now = _utc_text(now_moment)
                now_epoch = now_moment.timestamp()
                row = self._job_row(connection, job_id)
                if row["state"] in TERMINAL_JOB_STATES:
                    if (
                        row["state"] == state
                        and row["exit_reason"] == exit_reason.strip()
                        and row["gate_status"] == "not_run"
                        and row["reviewer_identity"] is None
                        and row["lease_owner"] == owner.strip()
                        and int(row["lease_generation"] or 0) == lease_token
                    ):
                        return self._job_payload(connection, row)
                    raise TransitionError(f"Job {job_id} is already terminal")
                self._assert_current_lease(
                    row,
                    owner=owner.strip(),
                    lease_token=lease_token,
                    now_epoch=now_epoch,
                )
                legal = {
                    "preparing": {"interrupted"},
                    "running": {"blocked", "interrupted"},
                    "reviewing": {"blocked", "interrupted"},
                }
                if state not in legal[row["state"]]:
                    raise TransitionError(f"illegal Job transition {row['state']} -> {state}")

                payload = self._record_job_completion(
                    connection,
                    row,
                    state=state,
                    exit_reason=exit_reason.strip(),
                    gate_status="not_run",
                    gate_path=None,
                    gate_digest=None,
                    reviewed_commit=None,
                    reviewed_tree=None,
                    actor=owner.strip(),
                    reviewer_identity=None,
                    now=now,
                    now_epoch=now_epoch,
                )
            return payload
        finally:
            if connection is not None:
                connection.close()
            self._release_job_execution_fence(execution_descriptor)

    def interrupt_job_after_stop(
        self,
        job_id: str,
        *,
        actor: str,
        exit_reason: str,
    ) -> dict[str, Any]:
        """Interrupt a nonterminal Job only after dispatch stopped and execution reaped."""

        if not actor or not actor.strip():
            raise TransitionError("stop-interrupt actor must not be empty")
        if not exit_reason or not exit_reason.strip():
            raise TransitionError("stop-interrupt requires a nonempty exit reason")
        actor = actor.strip()
        exit_reason = exit_reason.strip()
        _reject_runtime_secrets(actor, "stop_interrupt_actor")
        _reject_runtime_secrets(exit_reason, "exit_reason")
        execution_descriptor = self._acquire_job_execution_fence(job_id)
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            with self._transaction(connection):
                dispatch = self._dispatch_row(connection)
                if dispatch["desired_state"] != "stopped":
                    raise TransitionError(
                        "stop-interrupt requires the durable dispatch state to be stopped"
                    )
                now_moment = self._now()
                now = _utc_text(now_moment)
                now_epoch = now_moment.timestamp()
                row = self._job_row(connection, job_id)
                if row["state"] in TERMINAL_JOB_STATES:
                    if (
                        row["state"] == "interrupted"
                        and row["exit_reason"] == exit_reason
                        and row["gate_status"] == "not_run"
                        and row["reviewer_identity"] is None
                    ):
                        return self._job_payload(connection, row)
                    raise TransitionError(f"Job {job_id} is already terminal")
                if row["state"] not in ACTIVE_JOB_STATES:
                    raise TransitionError(
                        "stop-interrupt preserves queued Jobs for a later deployment"
                    )
                return self._record_job_completion(
                    connection,
                    row,
                    state="interrupted",
                    exit_reason=exit_reason,
                    gate_status="not_run",
                    gate_path=None,
                    gate_digest=None,
                    reviewed_commit=None,
                    reviewed_tree=None,
                    actor=actor,
                    reviewer_identity=None,
                    now=now,
                    now_epoch=now_epoch,
                )
        finally:
            if connection is not None:
                connection.close()
            self._release_job_execution_fence(execution_descriptor)

    def review_job(
        self,
        job_id: str,
        *,
        reviewer: str,
        state: str,
        exit_reason: str,
        gate_status: str = "not_run",
        gate_result: str | None = None,
        accepted_commit: str | None = None,
    ) -> dict[str, Any]:
        if state not in {"passed", "rejected"}:
            raise TransitionError("review state must be passed or rejected")
        if not reviewer or not reviewer.strip():
            raise TransitionError("reviewer identity must not be empty")
        reviewer = reviewer.strip()
        _reject_runtime_secrets(reviewer, "reviewer_identity")
        if not exit_reason or not exit_reason.strip():
            raise TransitionError("review requires a nonempty exit reason")
        exit_reason = exit_reason.strip()
        _reject_runtime_secrets(exit_reason, "exit_reason")
        if gate_status not in GATE_STATES:
            raise TransitionError("invalid gate status")
        if state == "passed" and gate_status != "passed":
            raise TransitionError("passed review requires a passed gate")
        if gate_status == "not_run":
            if gate_result is not None or accepted_commit is not None:
                raise TransitionError("not_run review cannot carry gate or commit evidence")
        else:
            if gate_result is None:
                raise TransitionError("completed gate review requires --gate-result")
            if accepted_commit is None or COMMIT_RE.fullmatch(accepted_commit) is None:
                raise TransitionError("completed gate review requires --accepted-commit")
        execution_descriptor = self._acquire_job_execution_fence(job_id)
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            try:
                connection.execute("BEGIN")
            except sqlite3.Error as error:
                raise HarnessError(
                    f"could not acquire SQLite review snapshot: {error}"
                ) from error
            try:
                row, task_row, authority_snapshot = self._review_authority_snapshot(
                    connection, job_id
                )
                terminal_retry = row["state"] in TERMINAL_JOB_STATES
                if terminal_retry:
                    if not (
                        row["state"] == state
                        and row["exit_reason"] == exit_reason
                        and row["gate_status"] == gate_status
                        and row["accepted_commit"] == accepted_commit
                        and row["reviewer_identity"] == reviewer
                    ):
                        raise TransitionError(f"Job {job_id} is already terminal")
                else:
                    if row["state"] != "reviewing":
                        raise TransitionError(
                            "Job must be reviewing before Codex review"
                        )
                    if reviewer in set(authority_snapshot["worker_owners"]):
                        raise TransitionError(
                            "a current or prior worker lease owner cannot review its own Job"
                        )
                    self._assert_active_lease_dispatch_epoch(connection, row)
                    self._assert_reviewable_lease(
                        connection, row, now_epoch=self._now().timestamp()
                    )
                    if (
                        state == "passed"
                        and authority_snapshot["latest_revision"]
                        != row["task_revision"]
                    ):
                        raise TransitionError(
                            "stale Task revision cannot produce a passed Job"
                        )
                    self._validate_job_worktree(
                        connection, json.loads(row["source_json"]), required=True
                    )
                task = json.loads(task_row["source_json"])
                artifact_dir = self._validated_job_artifact_dir(row)
                connection.commit()
            except Exception:
                connection.rollback()
                raise

            # Git and gate hashing may take seconds. The per-Job execution fence
            # remains held, but no SQLite write transaction spans this I/O.
            gate_path: Path | None = None
            gate_digest: str | None = None
            gate_identity: tuple[int, ...] | None = None
            accepted_tree: str | None = None
            if gate_result is not None and accepted_commit is not None:
                accepted_tree = self._validate_reviewed_commit(
                    connection, row, task, accepted_commit
                )
                gate_path, content, gate_digest = self._gate_artifact(
                    artifact_dir, gate_result
                )
                try:
                    gate_document = json.loads(content.decode("utf-8"))
                except (UnicodeDecodeError, json.JSONDecodeError) as error:
                    raise TransitionError(
                        f"gate artifact is not valid UTF-8 JSON: {error}"
                    ) from error
                _validate_gate_document(
                    gate_document,
                    task=task,
                    expected_status=gate_status,
                    accepted_commit=accepted_commit,
                    accepted_tree=accepted_tree,
                    artifact_dir=artifact_dir,
                )
                gate_identity = self._file_identity(gate_path)

            if terminal_retry:
                if gate_path is not None and (
                    row["accepted_tree"] != accepted_tree
                    or row["gate_result_path"] != str(gate_path)
                    or row["gate_result_sha256"] != gate_digest
                ):
                    raise ConflictError("review retry gate or commit evidence changed")
                connection.execute("BEGIN")
                try:
                    final_row, _, final_snapshot = self._review_authority_snapshot(
                        connection, job_id
                    )
                    if final_snapshot != authority_snapshot:
                        raise ConflictError(
                            "review authority changed during evidence validation"
                        )
                    if gate_path is not None and self._file_identity(
                        gate_path
                    ) != gate_identity:
                        raise ConflictError(
                            "review gate evidence changed during validation"
                        )
                    payload = self._job_payload(connection, final_row)
                    connection.commit()
                    return payload
                except Exception:
                    connection.rollback()
                    raise

            with self._transaction(connection):
                now_moment = self._now()
                now = _utc_text(now_moment)
                now_epoch = now_moment.timestamp()
                final_row, _, final_snapshot = self._review_authority_snapshot(
                    connection, job_id
                )
                if final_snapshot != authority_snapshot:
                    raise ConflictError(
                        "review authority changed during evidence validation"
                    )
                self._assert_active_lease_dispatch_epoch(connection, final_row)
                self._assert_reviewable_lease(
                    connection, final_row, now_epoch=now_epoch
                )
                if gate_path is not None:
                    if self._file_identity(gate_path) != gate_identity:
                        raise ConflictError(
                            "review gate evidence changed during validation"
                        )
                    assert gate_digest is not None
                    self._register_prevalidated_gate(
                        connection,
                        final_row,
                        gate_path=gate_path,
                        gate_digest=gate_digest,
                        now=now,
                    )
                payload = self._record_job_completion(
                    connection,
                    final_row,
                    state=state,
                    exit_reason=exit_reason,
                    gate_status=gate_status,
                    gate_path=gate_path,
                    gate_digest=gate_digest,
                    reviewed_commit=accepted_commit,
                    reviewed_tree=accepted_tree,
                    actor=reviewer,
                    reviewer_identity=reviewer,
                    now=now,
                    now_epoch=now_epoch,
                )
            return payload
        finally:
            if connection is not None:
                connection.close()
            self._release_job_execution_fence(execution_descriptor)


def default_state_dir() -> Path:
    return Path(__file__).resolve().parent.parent / "state"


__all__ = [
    "ACTIVE_JOB_STATES",
    "ConflictError",
    "HarnessError",
    "HarnessStore",
    "LeaseError",
    "NotFoundError",
    "NotInitializedError",
    "SCHEMA_VERSION",
    "TERMINAL_JOB_STATES",
    "TransitionError",
    "default_state_dir",
]
