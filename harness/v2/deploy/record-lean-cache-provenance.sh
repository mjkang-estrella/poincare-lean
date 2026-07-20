#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  printf 'Usage: %s --task absolute-immutable-task.json --command-index integer [--source-root exact-base-checkout] [environment-file]\n' "${0##*/}"
}

task_path=
command_index=
source_override=
config_file=
while (( $# > 0 )); do
  case "$1" in
    --task)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      task_path=$2
      shift 2
      ;;
    --command-index)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      command_index=$2
      shift 2
      ;;
    --source-root)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      source_override=$2
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    --*)
      usage >&2
      exit 64
      ;;
    *)
      [[ -z "$config_file" && $# -eq 1 ]] || { usage >&2; exit 64; }
      config_file=$1
      shift
      ;;
  esac
done

[[ -n "$task_path" && "$task_path" = /* ]] || {
  printf 'ERROR: --task must name an absolute immutable Task JSON file\n' >&2
  exit 64
}
[[ "$command_index" =~ ^(0|[1-9][0-9]*)$ ]] || {
  printf 'ERROR: --command-index must be a nonnegative integer\n' >&2
  exit 64
}
[[ -z "$source_override" || "$source_override" = /* ]] || {
  printf 'ERROR: --source-root must be absolute\n' >&2
  exit 64
}

load_config "${config_file:-$SCRIPT_DIR/.env}"
[[ -n "${HARNESS_PI_PYTHON:-}" && -x "$HARNESS_PI_PYTHON" ]] ||
  die "the pinned Python executable is unavailable: ${HARNESS_PI_PYTHON:-unset}"
[[ -x "$HARNESS_PI_GIT" && ! -L "$HARNESS_PI_GIT" ]] ||
  die "the pinned Git executable is unavailable: $HARNESS_PI_GIT"
readonly PINNED_LAKE="$POINCARE_PI_TOOLCHAIN_ROOT/bin/lake"
[[ -x "$PINNED_LAKE" && ! -L "$PINNED_LAKE" ]] ||
  die "the pinned Lake executable is unavailable: $PINNED_LAKE"
readonly PINNED_LEAN="$POINCARE_PI_TOOLCHAIN_ROOT/bin/lean"
[[ -x "$PINNED_LEAN" && ! -L "$PINNED_LEAN" ]] ||
  die "the pinned Lean executable is unavailable: $PINNED_LEAN"
assert_deploy_code_committed

PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
  PYTHONDONTWRITEBYTECODE=1 \
  exec "$HARNESS_PI_PYTHON" -S -P -B - \
    "$task_path" "$command_index" "$source_override" \
    "$POINCARE_CONFIG_FILE" "$POINCARE_REPO_ROOT" \
    "$POINCARE_WORKTREE_ROOT" "$POINCARE_PI_LAKE_CACHE_ROOT" \
    "$POINCARE_STATE_DIR" "$POINCARE_DEPLOY_CODE_ROOT" \
    "$SCRIPT_DIR/publish-lean-cache.sh" "$HARNESS_PI_GIT" "$PINNED_LAKE" \
    "$PINNED_LEAN" "$POINCARE_PI_TOOLCHAIN_ROOT" <<'PY'
from __future__ import annotations

import datetime as dt
import fcntl
import fnmatch
import hashlib
import importlib.util
import json
import os
import re
import secrets
import selectors
import signal
import stat
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import Any

from harness.v2.pi.security import SecurityError, _sealed_tree_attestation

(
    task_raw_path,
    command_index_raw,
    source_override,
    config_raw,
    configured_repo_raw,
    worktree_root_raw,
    cache_root_raw,
    state_root_raw,
    control_root_raw,
    publisher_raw,
    git_executable_raw,
    lake_executable_raw,
    lean_executable_raw,
    toolchain_root_raw,
) = sys.argv[1:]

LOG_CAP = 256 * 1024 * 1024
PROJECTION_LOG_CAP = 1024 * 1024
TASK_CAP = 1024 * 1024
HEX40 = re.compile(r"[0-9a-f]{40}")
HEX64 = re.compile(r"[0-9a-f]{64}")
PUBLISHER_TASK_ID = re.compile(r"[a-z0-9][a-z0-9-]{0,127}")
BUILD_TARGET = re.compile(r"[A-Za-z0-9_.-]+")
ROOT_BUILD_ARGV = ["env", "LEAN_NUM_THREADS=1", "lake", "build"]
ROOT_LEAN_ARGV = [
    "env",
    "LEAN_NUM_THREADS=1",
    "lake",
    "env",
    "lean",
    "Poincare.lean",
]
STEP_KEYS = {
    "argv",
    "status",
    "exit_code",
    "started_at",
    "completed_at",
    "stdout",
    "stderr",
}


class RecorderFailure(RuntimeError):
    pass


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def canonical_json(value: object) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")


def run_checked(argv: list[str], *, cwd: Path, label: str) -> str:
    completed = subprocess.run(
        argv,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=os.environ.copy(),
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise RecorderFailure(f"{label} failed: {detail[:2048]}")
    return completed.stdout.strip()


def canonical_directory(raw: str, label: str) -> Path:
    if not raw or not os.path.isabs(raw) or os.path.normpath(raw) != raw:
        raise RecorderFailure(f"{label} must be an absolute normalized path")
    path = Path(raw)
    if path.is_symlink() or not path.is_dir():
        raise RecorderFailure(f"{label} must be a real directory")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise RecorderFailure(f"cannot resolve {label}: {exc}") from exc
    if resolved != path:
        raise RecorderFailure(f"{label} must not traverse a symbolic link")
    info = os.lstat(path)
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid():
        raise RecorderFailure(f"{label} must be a current-user-owned directory")
    return path


def canonical_executable(raw: str, label: str) -> Path:
    if not raw or not os.path.isabs(raw) or os.path.normpath(raw) != raw:
        raise RecorderFailure(f"{label} must be an absolute normalized path")
    path = Path(raw)
    if path.is_symlink():
        raise RecorderFailure(f"{label} must not be a symbolic link")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise RecorderFailure(f"cannot resolve {label}: {exc}") from exc
    info = os.lstat(path)
    if resolved != path or not stat.S_ISREG(info.st_mode) or not os.access(path, os.X_OK):
        raise RecorderFailure(f"{label} must be a canonical executable regular file")
    return path


GIT_EXECUTABLE = canonical_executable(git_executable_raw, "pinned Git")
LAKE_EXECUTABLE = canonical_executable(lake_executable_raw, "pinned Lake")
LEAN_EXECUTABLE = canonical_executable(lean_executable_raw, "pinned Lean")
TOOLCHAIN_ROOT = canonical_directory(toolchain_root_raw, "pinned Lean toolchain root")
for executable, label in (
    (LAKE_EXECUTABLE, "Lake"),
    (LEAN_EXECUTABLE, "Lean"),
):
    try:
        executable.relative_to(TOOLCHAIN_ROOT)
    except ValueError as exc:
        raise RecorderFailure(f"pinned {label} executable escapes the Lean toolchain root") from exc


def executable_record(path: Path, label: str) -> dict[str, object]:
    before = os.lstat(path)
    if not stat.S_ISREG(before.st_mode) or not os.access(path, os.X_OK):
        raise RecorderFailure(f"{label} is no longer an executable regular file")
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        opened = os.fstat(descriptor)
        identity = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_nlink,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        if identity != (
            opened.st_dev,
            opened.st_ino,
            opened.st_mode,
            opened.st_nlink,
            opened.st_size,
            opened.st_mtime_ns,
            opened.st_ctime_ns,
        ):
            raise RecorderFailure(f"{label} changed while it was opened")
        digest = hashlib.sha256()
        total = 0
        while chunk := os.read(descriptor, 1024 * 1024):
            total += len(chunk)
            if total > 256 * 1024 * 1024:
                raise RecorderFailure(f"{label} exceeds its executable byte cap")
            digest.update(chunk)
        after = os.fstat(descriptor)
        if identity != (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ) or total != before.st_size:
            raise RecorderFailure(f"{label} changed while it was hashed")
        return {
            "path": str(path),
            "sha256": digest.hexdigest(),
            "size_bytes": total,
            "mode": stat.S_IMODE(before.st_mode),
        }
    finally:
        os.close(descriptor)


EXECUTABLES = {
    "git": executable_record(GIT_EXECUTABLE, "pinned Git"),
    "lake": executable_record(LAKE_EXECUTABLE, "pinned Lake"),
    "lean": executable_record(LEAN_EXECUTABLE, "pinned Lean"),
}


def lean_toolchain_record() -> dict[str, object]:
    compiler_lib = TOOLCHAIN_ROOT / "lib" / "lean"
    if compiler_lib.is_symlink() or not compiler_lib.is_dir():
        raise RecorderFailure("Lean compiler library must be a real directory")
    try:
        resolved = compiler_lib.resolve(strict=True)
        resolved.relative_to(TOOLCHAIN_ROOT)
    except (OSError, ValueError) as exc:
        raise RecorderFailure("Lean compiler library escapes the toolchain root") from exc
    if resolved != compiler_lib:
        raise RecorderFailure("Lean compiler library path must be canonical")
    try:
        digest, entry_count, _ = _sealed_tree_attestation(
            compiler_lib,
            "Lean compiler library",
            require_sealed=False,
            allow_internal_symlinks=True,
        )
    except SecurityError as exc:
        raise RecorderFailure(f"cannot attest Lean compiler library: {exc}") from exc
    return {
        "root": str(TOOLCHAIN_ROOT),
        "compiler_lib": {
            "path": str(compiler_lib),
            "tree_sha256": digest,
            "entry_count": entry_count,
        },
    }


LEAN_TOOLCHAIN = lean_toolchain_record()


def assert_toolchain_stable() -> None:
    current = {
        "git": executable_record(GIT_EXECUTABLE, "pinned Git"),
        "lake": executable_record(LAKE_EXECUTABLE, "pinned Lake"),
        "lean": executable_record(LEAN_EXECUTABLE, "pinned Lean"),
    }
    if current != EXECUTABLES:
        raise RecorderFailure(
            "pinned Git/Lake/Lean identity changed during provenance recording"
        )
    if lean_toolchain_record() != LEAN_TOOLCHAIN:
        raise RecorderFailure(
            "Lean toolchain closure changed during provenance recording"
        )


def stable_regular_file(
    raw: str | Path,
    *,
    label: str,
    cap: int,
    immutable: bool,
) -> tuple[Path, bytes, tuple[int, ...]]:
    text = os.fspath(raw)
    if not os.path.isabs(text) or os.path.normpath(text) != text:
        raise RecorderFailure(f"{label} must be an absolute normalized path")
    path = Path(text)
    lexical = Path(os.path.abspath(path))
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise RecorderFailure(f"cannot resolve {label}: {exc}") from exc
    if lexical != resolved or path.is_symlink():
        raise RecorderFailure(f"{label} must not traverse a symbolic link")
    before = os.lstat(path)
    if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
        raise RecorderFailure(f"{label} must be a singly linked regular file")
    if before.st_uid != os.geteuid():
        raise RecorderFailure(f"{label} must be owned by the current user")
    if immutable and before.st_mode & 0o222:
        raise RecorderFailure(f"{label} must be immutable (no write bits)")
    if before.st_size > cap:
        raise RecorderFailure(f"{label} exceeds its {cap}-byte limit")
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise RecorderFailure(f"cannot safely open {label}: {exc}") from exc
    try:
        opened = os.fstat(descriptor)
        identity = (
            before.st_dev,
            before.st_ino,
            before.st_uid,
            before.st_mode,
            before.st_nlink,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        opened_identity = (
            opened.st_dev,
            opened.st_ino,
            opened.st_uid,
            opened.st_mode,
            opened.st_nlink,
            opened.st_size,
            opened.st_mtime_ns,
            opened.st_ctime_ns,
        )
        if opened_identity != identity:
            raise RecorderFailure(f"{label} changed while it was opened")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, 65536)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise RecorderFailure(f"{label} exceeds its {cap}-byte limit")
            chunks.append(chunk)
        after = os.fstat(descriptor)
        after_identity = (
            after.st_dev,
            after.st_ino,
            after.st_uid,
            after.st_mode,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if after_identity != identity or total != before.st_size:
            raise RecorderFailure(f"{label} changed while it was read")
    finally:
        os.close(descriptor)
    return path, b"".join(chunks), identity


def stable_file_digest(path: Path, *, label: str, cap: int) -> str:
    if not path.is_absolute() or path.resolve(strict=True) != path or path.is_symlink():
        raise RecorderFailure(f"{label} must be an absolute non-symlink file")
    before = os.lstat(path)
    if (
        not stat.S_ISREG(before.st_mode)
        or before.st_nlink != 1
        or before.st_uid != os.geteuid()
        or before.st_mode & 0o222
        or before.st_size > cap
    ):
        raise RecorderFailure(f"{label} is not a safe immutable evidence file")
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        opened = os.fstat(descriptor)
        expected = (
            before.st_dev,
            before.st_ino,
            before.st_uid,
            before.st_mode,
            before.st_nlink,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        actual = (
            opened.st_dev,
            opened.st_ino,
            opened.st_uid,
            opened.st_mode,
            opened.st_nlink,
            opened.st_size,
            opened.st_mtime_ns,
            opened.st_ctime_ns,
        )
        if actual != expected:
            raise RecorderFailure(f"{label} changed while it was opened")
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise RecorderFailure(f"{label} exceeds its byte cap")
            digest.update(chunk)
        after = os.fstat(descriptor)
        final = (
            after.st_dev,
            after.st_ino,
            after.st_uid,
            after.st_mode,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if final != expected or total != before.st_size:
            raise RecorderFailure(f"{label} changed while it was hashed")
        return digest.hexdigest()
    finally:
        os.close(descriptor)


def git_common_dir(worktree: Path) -> Path:
    raw = run_checked(
        [str(GIT_EXECUTABLE), "-C", str(worktree), "rev-parse", "--git-common-dir"],
        cwd=worktree,
        label="Git common-directory lookup",
    )
    candidate = Path(raw)
    if not candidate.is_absolute():
        candidate = worktree / candidate
    return candidate.resolve(strict=True)


def git_value(source: Path, expression: str, label: str) -> str:
    return run_checked(
        [str(GIT_EXECUTABLE), "-C", str(source), "rev-parse", expression],
        cwd=source,
        label=label,
    )


def assert_source_stable(source: Path, commit: str, tree: str) -> None:
    if git_value(source, "HEAD", "source HEAD lookup") != commit:
        raise RecorderFailure("source HEAD changed during provenance recording")
    if git_value(source, "HEAD^{tree}", "source tree lookup") != tree:
        raise RecorderFailure("source tree changed during provenance recording")
    status = run_checked(
        [
            str(GIT_EXECUTABLE),
            "-C",
            str(source),
            "status",
            "--porcelain",
            "--untracked-files=all",
        ],
        cwd=source,
        label="source status audit",
    )
    if status:
        raise RecorderFailure("provenance recording requires a clean exact-base source")


def assert_control_surface(control: Path) -> None:
    required = [
        "harness/__init__.py",
        "harness/v2/__init__.py",
        "harness/v2/runtime/__init__.py",
        "harness/v2/runtime/validation.py",
        "harness/v2/pi/__init__.py",
        "harness/v2/pi/security.py",
        "harness/v2/deploy/common.sh",
        "harness/v2/deploy/publish-lean-cache.sh",
        "harness/v2/deploy/verify-lean-cache.sh",
        "harness/v2/deploy/cache-sandbox-smoke.sh",
        "harness/v2/deploy/record-lean-cache-provenance.sh",
    ]
    top = run_checked(
        [str(GIT_EXECUTABLE), "-C", str(control), "rev-parse", "--show-toplevel"],
        cwd=control,
        label="deployment checkout lookup",
    )
    if top != str(control):
        raise RecorderFailure("deployment control root is not its Git top level")
    for relative in required:
        run_checked(
            [str(GIT_EXECUTABLE), "-C", str(control), "ls-files", "--error-unmatch", relative],
            cwd=control,
            label=f"control input tracking check ({relative})",
        )
        candidate = control / relative
        if candidate.is_symlink() or not candidate.is_file():
            raise RecorderFailure(f"deployment control input is not a regular file: {relative}")
        actual = run_checked(
            [str(GIT_EXECUTABLE), "-C", str(control), "hash-object", "--no-filters", str(candidate)],
            cwd=control,
            label=f"control input hash ({relative})",
        )
        expected = run_checked(
            [str(GIT_EXECUTABLE), "-C", str(control), "rev-parse", f"HEAD:{relative}"],
            cwd=control,
            label=f"committed control input hash ({relative})",
        )
        if actual != expected:
            raise RecorderFailure(f"deployment control input differs from HEAD: {relative}")
    status = run_checked(
        [
            str(GIT_EXECUTABLE),
            "-C",
            str(control),
            "status",
            "--porcelain",
            "--untracked-files=all",
            "--",
            *required,
        ],
        cwd=control,
        label="deployment control status audit",
    )
    if status:
        raise RecorderFailure("deployment provenance control inputs differ from committed HEAD")


def ensure_runtime_directory(parent: Path, relative_parts: tuple[str, ...]) -> Path:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(parent, flags)
    current = parent
    try:
        for index, part in enumerate(relative_parts):
            try:
                os.mkdir(part, 0o700, dir_fd=descriptor)
                os.fsync(descriptor)
            except FileExistsError:
                pass
            next_descriptor = os.open(part, flags, dir_fd=descriptor)
            info = os.fstat(next_descriptor)
            if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid():
                os.close(next_descriptor)
                raise RecorderFailure(f"runtime path is not an owned real directory: {current / part}")
            if index >= 2 and info.st_mode & 0o022:
                os.close(next_descriptor)
                raise RecorderFailure(f"runtime directory is group/world writable: {current / part}")
            os.close(descriptor)
            descriptor = next_descriptor
            current = current / part
    finally:
        os.close(descriptor)
    return current


def create_bundle(configured_repo: Path, state_root: Path, commit: str) -> Path:
    expected = configured_repo / "harness" / "v2" / "state"
    if state_root != expected:
        raise RecorderFailure("configured state root is not the canonical Harness v2 state path")
    head_root = ensure_runtime_directory(
        configured_repo,
        ("harness", "v2", "state", "cache-provenance", commit),
    )
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(head_root, flags)
    try:
        for _ in range(32):
            unique = (
                dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
                + f"-{os.getpid()}-{secrets.token_hex(8)}"
            )
            try:
                os.mkdir(unique, 0o700, dir_fd=descriptor)
            except FileExistsError:
                continue
            os.fsync(descriptor)
            return head_root / unique
    finally:
        os.close(descriptor)
    raise RecorderFailure("could not allocate a unique append-only provenance bundle")


def bundle_fd(bundle: Path) -> int:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    return os.open(bundle, flags)


def write_exclusive(bundle: Path, name: str, raw: bytes, mode: int = 0o400) -> Path:
    if not name or PurePosixPath(name).name != name or name in {".", ".."}:
        raise RecorderFailure("invalid provenance artifact name")
    directory = bundle_fd(bundle)
    descriptor = -1
    try:
        flags = (
            os.O_CREAT
            | os.O_EXCL
            | os.O_WRONLY
            | getattr(os, "O_CLOEXEC", 0)
            | getattr(os, "O_NOFOLLOW", 0)
        )
        descriptor = os.open(name, flags, 0o600, dir_fd=directory)
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            view = view[written:]
        os.fsync(descriptor)
        os.fchmod(descriptor, mode)
        os.fsync(descriptor)
        os.fsync(directory)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        os.close(directory)
    return bundle / name


def open_exclusive_log(bundle: Path, name: str) -> tuple[int, int]:
    directory = bundle_fd(bundle)
    flags = (
        os.O_CREAT
        | os.O_EXCL
        | os.O_WRONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    try:
        descriptor = os.open(name, flags, 0o600, dir_fd=directory)
    except BaseException:
        os.close(directory)
        raise
    return directory, descriptor


def finish_log(directory: int, descriptor: int) -> None:
    os.fsync(descriptor)
    os.fchmod(descriptor, 0o400)
    os.fsync(descriptor)
    os.close(descriptor)
    os.fsync(directory)
    os.close(directory)


def terminate_process(proc: subprocess.Popen[bytes]) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        proc.wait(timeout=5)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def pinned_lake_argv(logical: list[str]) -> list[str]:
    if logical[:3] != ["env", "LEAN_NUM_THREADS=1", "lake"]:
        raise RecorderFailure("recorded build commands must use the canonical pinned-Lake form")
    tail = logical[3:]
    if tail[:2] == ["env", "lean"]:
        tail = ["env", str(LEAN_EXECUTABLE), *tail[2:]]
    return [str(LAKE_EXECUTABLE), *tail]


def run_captured(
    bundle: Path,
    *,
    name: str,
    argv: list[str],
    cwd: Path,
    cap: int,
    execution_argv: list[str] | None = None,
) -> tuple[dict[str, Any], bool]:
    stdout_name = f"{name}.stdout"
    stderr_name = f"{name}.stderr"
    stdout_dir, stdout_fd = open_exclusive_log(bundle, stdout_name)
    try:
        stderr_dir, stderr_fd = open_exclusive_log(bundle, stderr_name)
    except BaseException:
        finish_log(stdout_dir, stdout_fd)
        raise
    started = utc_now()
    proc: subprocess.Popen[bytes] | None = None
    overflow = False
    returncode = 127
    try:
        actual_argv = execution_argv if execution_argv is not None else pinned_lake_argv(argv)
        child_environment = os.environ.copy()
        if execution_argv is None:
            child_environment["LEAN_NUM_THREADS"] = "1"
            child_environment["PATH"] = f"{LAKE_EXECUTABLE.parent}:/usr/bin:/bin"
        proc = subprocess.Popen(
            actual_argv,
            cwd=cwd,
            env=child_environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
            close_fds=True,
        )
        if proc.stdout is None or proc.stderr is None:
            raise RecorderFailure("could not capture command output")
        selector = selectors.DefaultSelector()
        selector.register(proc.stdout, selectors.EVENT_READ, (stdout_fd, "stdout"))
        selector.register(proc.stderr, selectors.EVENT_READ, (stderr_fd, "stderr"))
        totals = {"stdout": 0, "stderr": 0}
        while selector.get_map():
            for key, _ in selector.select(timeout=1):
                data = os.read(key.fileobj.fileno(), 65536)
                if not data:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                target_fd, stream_name = key.data
                remaining = max(0, cap - totals[stream_name])
                if remaining:
                    chunk = data[:remaining]
                    view = memoryview(chunk)
                    while view:
                        written = os.write(target_fd, view)
                        view = view[written:]
                    totals[stream_name] += len(chunk)
                if len(data) > remaining:
                    overflow = True
                    terminate_process(proc)
        returncode = proc.wait()
    except BaseException:
        if proc is not None:
            terminate_process(proc)
        raise
    finally:
        completed = utc_now()
        finish_log(stdout_dir, stdout_fd)
        finish_log(stderr_dir, stderr_fd)
    if overflow and returncode == 0:
        returncode = 74
    step = {
        "argv": argv,
        "status": "passed" if returncode == 0 and not overflow else "failed",
        "exit_code": returncode,
        "started_at": started,
        "completed_at": completed,
        "stdout": file_reference(bundle / stdout_name),
        "stderr": file_reference(bundle / stderr_name),
    }
    return step, overflow


def file_reference(path: Path) -> dict[str, str]:
    return {
        "path": path.name,
        "sha256": stable_file_digest(path, label=path.name, cap=LOG_CAP),
    }


def check_task_unchanged(
    task_path: Path, expected: bytes, expected_identity: tuple[int, ...]
) -> None:
    _, current, identity = stable_regular_file(
        task_path, label="Task source", cap=TASK_CAP, immutable=True
    )
    if identity != expected_identity or current != expected:
        raise RecorderFailure("immutable Task source changed during provenance recording")


def scope_matches(relative: str, pattern: str) -> bool:
    path_parts = PurePosixPath(relative).parts
    pattern_parts = PurePosixPath(pattern).parts

    def matches(path: tuple[str, ...], wanted: tuple[str, ...]) -> bool:
        if not wanted:
            return not path
        head, *tail = wanted
        remainder = tuple(tail)
        if head == "**":
            return matches(path, remainder) or bool(path and matches(path[1:], wanted))
        return bool(
            path
            and fnmatch.fnmatchcase(path[0], head)
            and matches(path[1:], remainder)
        )

    return matches(path_parts, pattern_parts)


def safe_gate_path(source: Path, relative: str, task: dict[str, Any]) -> None:
    pure = PurePosixPath(relative)
    if (
        pure.is_absolute()
        or pure.suffix != ".lean"
        or any(part in {"", ".", ".."} for part in pure.parts)
        or "\\" in relative
        or "\n" in relative
        or "\r" in relative
    ):
        raise RecorderFailure("selected Task Lean/module gate path is unsafe")
    allowed = task["scope"]["allowed_paths"]
    context = task["context"]["files"]
    forbidden = task["scope"]["forbidden_paths"]
    if not any(scope_matches(relative, pattern) for pattern in allowed) and relative not in context:
        raise RecorderFailure("selected Task gate is outside its allowed/context source scope")
    if any(scope_matches(relative, pattern) for pattern in forbidden):
        raise RecorderFailure("selected Task gate is inside its forbidden source scope")
    candidate = source.joinpath(*pure.parts)
    if candidate.is_symlink() or not candidate.is_file():
        raise RecorderFailure("selected Task gate source is not a real file")
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise RecorderFailure(f"cannot resolve selected Task gate source: {exc}") from exc
    if resolved != candidate.absolute():
        raise RecorderFailure("selected Task gate source traverses a symbolic link")
    try:
        resolved.relative_to(source)
    except ValueError as exc:
        raise RecorderFailure("selected Task gate source escapes the exact-base checkout") from exc


def selected_gate(task: dict[str, Any], index: int, source: Path) -> list[str]:
    commands = task["acceptance"]["commands"]
    if not 0 <= index < len(commands):
        raise RecorderFailure("--command-index is outside Task acceptance.commands")
    argv = commands[index]
    lean_prefix = ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean"]
    build_prefix = ["env", "LEAN_NUM_THREADS=1", "lake", "build"]
    if argv[:5] == lean_prefix and len(argv) == 6:
        safe_gate_path(source, argv[5], task)
    elif argv[:4] == build_prefix and len(argv) == 5:
        target = argv[4]
        if BUILD_TARGET.fullmatch(target) is None:
            raise RecorderFailure("selected Task Lake module target is unsafe")
        safe_gate_path(source, target.replace(".", "/") + ".lean", task)
    else:
        raise RecorderFailure(
            "selected Task command must be one exact single-threaded Lean source or Lake module build gate"
        )
    return list(argv)


def source_cache_projection(source: Path) -> str:
    root = (source / ".lake").resolve(strict=True)
    if root != (source / ".lake").absolute() or root.is_symlink() or not root.is_dir():
        raise RecorderFailure("post-build source .lake must be a real directory")
    for required in ("packages", "build", "config"):
        candidate = root / required
        if candidate.is_symlink() or not candidate.is_dir():
            raise RecorderFailure(f"post-build source cache lacks .lake/{required}/")
    reserved = {
        PurePosixPath(".harness-cache.json"),
        PurePosixPath(".harness-package-overrides.json"),
        PurePosixPath(".harness-cache-provenance.json"),
        PurePosixPath(".harness-package-identities.json"),
    }
    records: list[dict[str, object]] = []
    pending: list[tuple[Path, PurePosixPath]] = [(root, PurePosixPath("."))]
    while pending:
        directory, relative_directory = pending.pop()
        entries = sorted(os.scandir(directory), key=lambda item: item.name)
        children: list[tuple[Path, PurePosixPath]] = []
        for entry in entries:
            relative = (
                PurePosixPath(entry.name)
                if relative_directory == PurePosixPath(".")
                else relative_directory / entry.name
            )
            if entry.name == ".git" or relative in reserved:
                continue
            if "\n" in entry.name or "\r" in entry.name:
                raise RecorderFailure("source cache contains an unsafe filename")
            info = entry.stat(follow_symlinks=False)
            if stat.S_ISDIR(info.st_mode):
                records.append({"kind": "directory", "path": relative.as_posix()})
                children.append((Path(entry.path), relative))
                continue
            if stat.S_ISLNK(info.st_mode):
                target = os.readlink(entry.path)
                if not target or os.path.isabs(target) or "\x00" in target:
                    raise RecorderFailure(f"source cache contains an unsafe symlink: {relative}")
                lexical = Path(os.path.abspath(Path(entry.path).parent / target))
                try:
                    lexical.relative_to(root)
                    file_path = Path(entry.path).resolve(strict=True)
                    file_path.relative_to(root)
                except (OSError, ValueError) as exc:
                    raise RecorderFailure(f"source cache symlink escapes: {relative}") from exc
                target_info = file_path.stat()
                if not stat.S_ISREG(target_info.st_mode):
                    raise RecorderFailure(f"source cache symlink is not a file: {relative}")
                size = target_info.st_size
            elif stat.S_ISREG(info.st_mode):
                file_path = Path(entry.path)
                size = info.st_size
            else:
                raise RecorderFailure(f"source cache contains a special file: {relative}")
            digest = hashlib.sha256()
            with file_path.open("rb") as stream:
                while chunk := stream.read(1024 * 1024):
                    digest.update(chunk)
            records.append(
                {
                    "kind": "file",
                    "path": relative.as_posix(),
                    "sha256": digest.hexdigest(),
                    "size": size,
                }
            )
        pending.extend(reversed(children))
    raw = json.dumps(
        records, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return hashlib.sha256(raw).hexdigest()


def open_lock(lock_path: Path) -> tuple[int, tuple[int, int]]:
    if lock_path.parent.is_symlink() or lock_path.parent.resolve(strict=True) != lock_path.parent:
        raise RecorderFailure("build/Job lock parent is not a canonical real directory")
    flags = (
        os.O_CREAT
        | os.O_RDWR
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    descriptor = os.open(lock_path, flags, 0o600)
    info = os.fstat(descriptor)
    if (
        not stat.S_ISREG(info.st_mode)
        or info.st_uid != os.geteuid()
        or info.st_nlink != 1
        or info.st_mode & 0o077
    ):
        os.close(descriptor)
        raise RecorderFailure("build/Job lock must be a private current-user-owned regular file")
    path_info = os.lstat(lock_path)
    if (path_info.st_dev, path_info.st_ino) != (info.st_dev, info.st_ino):
        os.close(descriptor)
        raise RecorderFailure("build/Job lock changed while it was opened")
    return descriptor, (info.st_dev, info.st_ino)


def assert_lock_identity(lock_path: Path, identity: tuple[int, int], descriptor: int) -> None:
    current = os.lstat(lock_path)
    opened = os.fstat(descriptor)
    if (
        stat.S_ISLNK(current.st_mode)
        or (current.st_dev, current.st_ino) != identity
        or (opened.st_dev, opened.st_ino) != identity
    ):
        raise RecorderFailure("build/Job lock path changed during provenance recording")


def acquire_lock(descriptor: int, message: str) -> None:
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        raise RecorderFailure(message) from exc


def seal_bundle(bundle: Path) -> None:
    try:
        directory = bundle_fd(bundle)
    except OSError:
        return
    try:
        for entry in os.scandir(bundle):
            info = entry.stat(follow_symlinks=False)
            if stat.S_ISREG(info.st_mode):
                os.chmod(entry.path, 0o400, follow_symlinks=False)
            elif not stat.S_ISDIR(info.st_mode):
                raise RecorderFailure("provenance bundle contains a non-regular artifact")
        os.fsync(directory)
        os.chmod(bundle, 0o500)
        os.fsync(directory)
    finally:
        os.close(directory)
    parent = os.open(
        bundle.parent,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        os.fsync(parent)
    finally:
        os.close(parent)


bundle: Path | None = None
steps: list[dict[str, Any]] = []
projection_step: dict[str, Any] | None = None
task: dict[str, Any] | None = None
base_commit = ""
base_tree = ""
lock_fd = -1
failure_message = ""

try:
    command_index = int(command_index_raw)
    config, _, _ = stable_regular_file(
        config_raw, label="environment file", cap=1024 * 1024, immutable=False
    )
    config_mode = stat.S_IMODE(os.lstat(config).st_mode)
    if config_mode not in {0o400, 0o600}:
        raise RecorderFailure("environment file mode must be 0400 or 0600")

    configured_repo = canonical_directory(configured_repo_raw, "configured repository")
    control_root = canonical_directory(control_root_raw, "deployment control root")
    worktree_root = canonical_directory(worktree_root_raw, "worktree root")
    cache_root = canonical_directory(cache_root_raw, "immutable Lake cache root")
    state_root = Path(state_root_raw)
    publisher, _, _ = stable_regular_file(
        publisher_raw,
        label="cache publisher",
        cap=2 * 1024 * 1024,
        immutable=False,
    )
    if not os.access(publisher, os.X_OK):
        raise RecorderFailure("cache publisher is not executable")
    assert_control_surface(control_root)
    validation_path = control_root / "harness/v2/runtime/validation.py"
    validation_spec = importlib.util.spec_from_file_location(
        "_poincare_harness_v2_task_validation", validation_path
    )
    if validation_spec is None or validation_spec.loader is None:
        raise RecorderFailure("could not load the attested Harness v2 Task validator")
    validation_module = importlib.util.module_from_spec(validation_spec)
    validation_spec.loader.exec_module(validation_module)

    source = canonical_directory(
        source_override or configured_repo_raw,
        "cache provenance source",
    )
    top = run_checked(
        [str(GIT_EXECUTABLE), "-C", str(source), "rev-parse", "--show-toplevel"],
        cwd=source,
        label="source Git top-level lookup",
    )
    if top != str(source):
        raise RecorderFailure("cache provenance source is not its Git top level")
    if git_common_dir(source) != git_common_dir(configured_repo):
        raise RecorderFailure("cache provenance source is not a worktree of the configured repository")
    if source == configured_repo:
        branch = run_checked(
            [str(GIT_EXECUTABLE), "-C", str(source), "symbolic-ref", "--quiet", "--short", "HEAD"],
            cwd=source,
            label="integration branch lookup",
        )
        expected_branch = os.environ["POINCARE_INTEGRATION_BRANCH"]
        if branch != expected_branch:
            raise RecorderFailure(
                f"cache provenance on the integration checkout requires branch {expected_branch!r}"
            )
    for protected, label in (
        (cache_root, "immutable Lake cache root"),
        (worktree_root, "worktree root"),
    ):
        if source == protected or source in protected.parents or protected in source.parents:
            raise RecorderFailure(f"cache provenance source overlaps the {label}")
    if not os.access(cache_root, os.W_OK | os.X_OK):
        raise RecorderFailure("immutable Lake cache root is not writable")

    base_commit = git_value(source, "HEAD", "source HEAD lookup")
    base_tree = git_value(source, "HEAD^{tree}", "source tree lookup")
    if HEX40.fullmatch(base_commit) is None or HEX40.fullmatch(base_tree) is None:
        raise RecorderFailure("source HEAD/tree is not a full Git object ID")
    assert_source_stable(source, base_commit, base_tree)

    task_path, task_bytes, task_identity = stable_regular_file(
        task_raw_path,
        label="Task source",
        cap=TASK_CAP,
        immutable=True,
    )
    def reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise RecorderFailure(f"Task source contains duplicate key {key!r}")
            result[key] = value
        return result

    def reject_nonfinite(value: str) -> object:
        raise RecorderFailure(f"Task source contains non-JSON numeric constant {value}")

    try:
        decoded_task = json.loads(
            task_bytes,
            object_pairs_hook=reject_duplicate_keys,
            parse_constant=reject_nonfinite,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecorderFailure("Task source is not valid UTF-8 JSON") from exc
    try:
        task = validation_module.validate_task(decoded_task)
    except ValueError as exc:
        raise RecorderFailure(f"Task source violates Harness v2: {exc}") from exc
    if PUBLISHER_TASK_ID.fullmatch(task["id"]) is None:
        raise RecorderFailure("Task ID is incompatible with cache provenance schema")
    if task["base_commit"] != base_commit:
        raise RecorderFailure("Task base_commit does not equal the exact source HEAD")
    gate_argv = selected_gate(task, command_index, source)
    source_cache = source / ".lake"
    if source_cache.is_symlink():
        raise RecorderFailure("source .lake must not be a symbolic link")

    bundle = create_bundle(configured_repo, state_root, base_commit)
    task_copy = write_exclusive(bundle, "task.json", task_bytes)
    task_reference = file_reference(task_copy)

    lock_path = state_root / "build-job.lock"
    lock_fd, lock_identity = open_lock(lock_path)
    acquire_lock(
        lock_fd,
        "a root build, cache operation, or Harness Job holds the shared build/Job lock",
    )
    assert_lock_identity(lock_path, lock_identity, lock_fd)
    assert_source_stable(source, base_commit, base_tree)
    check_task_unchanged(task_path, task_bytes, task_identity)

    for name, argv in (
        ("root-build", ROOT_BUILD_ARGV),
        ("root-lean", ROOT_LEAN_ARGV),
        ("module-gate", gate_argv),
    ):
        step, overflow = run_captured(
            bundle,
            name=name,
            argv=argv,
            cwd=source,
            cap=LOG_CAP,
        )
        steps.append(step)
        assert_toolchain_stable()
        assert_source_stable(source, base_commit, base_tree)
        check_task_unchanged(task_path, task_bytes, task_identity)
        assert_lock_identity(lock_path, lock_identity, lock_fd)
        if overflow:
            raise RecorderFailure(f"{name} exceeded the immutable evidence byte cap")
        if step["exit_code"] != 0:
            raise RecorderFailure(
                f"{name} failed with exit code {step['exit_code']}; evidence was preserved"
            )

    # Projection mode owns this same nonblocking lock. Release only for that
    # child, then immediately reacquire and compare the publisher's digest with
    # a fresh projection while the lock is held again. A competing build wins
    # the handoff only by making this attempt fail closed.
    fcntl.flock(lock_fd, fcntl.LOCK_UN)
    projection_argv = [
        str(publisher),
        "--source-root",
        str(source),
        "--print-source-projection",
        str(config),
    ]
    projection_step, projection_overflow = run_captured(
        bundle,
        name="source-projection",
        argv=projection_argv,
        cwd=control_root,
        cap=PROJECTION_LOG_CAP,
        execution_argv=projection_argv,
    )
    write_exclusive(
        bundle,
        "source-projection.json",
        canonical_json(projection_step),
    )
    if projection_overflow or projection_step["exit_code"] != 0:
        raise RecorderFailure(
            "publisher source-projection command failed; its evidence was preserved"
        )
    acquire_lock(
        lock_fd,
        "another build or Harness Job entered during the publisher lock handoff",
    )
    assert_lock_identity(lock_path, lock_identity, lock_fd)
    assert_source_stable(source, base_commit, base_tree)
    check_task_unchanged(task_path, task_bytes, task_identity)
    projection_stdout = bundle / "source-projection.stdout"
    _, projection_raw, _ = stable_regular_file(
        projection_stdout,
        label="publisher source projection output",
        cap=PROJECTION_LOG_CAP,
        immutable=True,
    )
    try:
        projection_text = projection_raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise RecorderFailure("publisher source projection is not ASCII") from exc
    if not projection_text.endswith("\n") or projection_text.count("\n") != 1:
        raise RecorderFailure("publisher source projection output is not one canonical line")
    source_projection = projection_text[:-1]
    if HEX64.fullmatch(source_projection) is None:
        raise RecorderFailure("publisher source projection digest is invalid")
    if source_cache_projection(source) != source_projection:
        raise RecorderFailure("source cache changed across the publisher lock handoff")
    assert_toolchain_stable()
    assert_source_stable(source, base_commit, base_tree)
    check_task_unchanged(task_path, task_bytes, task_identity)

    provenance = {
        "schema_version": "poincare.cache-provenance.v1",
        "base_commit": base_commit,
        "base_tree": base_tree,
        "source_root": str(source),
        "source_cache_projection_sha256": source_projection,
        "exclusion_lock": str(lock_path),
        "executables": EXECUTABLES,
        "lean_toolchain": LEAN_TOOLCHAIN,
        "root_build": {"commands": [steps[0], steps[1]]},
        "selected_task": {
            "id": task["id"],
            "revision": task["revision"],
            "base_commit": task["base_commit"],
            "source": task_reference,
        },
        "module_gate": {**steps[2], "command_index": command_index},
    }
    if set(steps[0]) != STEP_KEYS or set(steps[1]) != STEP_KEYS or set(steps[2]) != STEP_KEYS:
        raise RecorderFailure("internal provenance step shape is invalid")
    provenance_path = write_exclusive(
        bundle, "provenance.json", canonical_json(provenance)
    )
    seal_bundle(bundle)
    print(f"Recorded immutable cache provenance: {provenance_path}")
except BaseException as exc:
    failure_message = str(exc) or exc.__class__.__name__
    if lock_fd >= 0:
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
        except OSError:
            pass
    if bundle is not None:
        failure = {
            "schema_version": "poincare.cache-provenance-attempt.v1",
            "status": "failed",
            "recorded_at": utc_now(),
            "base_commit": base_commit or None,
            "base_tree": base_tree or None,
            "task_id": task.get("id") if task else None,
            "task_revision": task.get("revision") if task else None,
            "command_index": int(command_index_raw) if command_index_raw.isdigit() else None,
            "error": failure_message[:4096],
            "commands": steps,
            "source_projection": projection_step,
        }
        try:
            write_exclusive(bundle, "failure.json", canonical_json(failure))
        except BaseException:
            pass
        try:
            seal_bundle(bundle)
        except BaseException:
            pass
    print(f"ERROR: {failure_message}", file=sys.stderr)
    raise SystemExit(1)
finally:
    if lock_fd >= 0:
        try:
            os.close(lock_fd)
        except OSError:
            pass
PY
