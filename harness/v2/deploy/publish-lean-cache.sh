#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  printf 'Usage: %s [--source-root exact-base-checkout] (--provenance absolute-json | --print-source-projection) [environment-file]\n' "${0##*/}"
}

source_override=
provenance_path=
config_file=
projection_only=0
while (( $# > 0 )); do
  case "$1" in
    --source-root)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      source_override=$2
      shift 2
      ;;
    --provenance)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      provenance_path=$2
      shift 2
      ;;
    --print-source-projection)
      projection_only=1
      shift
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
if (( projection_only == 1 )); then
  [[ -z "$provenance_path" ]] || { usage >&2; exit 64; }
else
  [[ -n "$provenance_path" ]] || { usage >&2; exit 64; }
  [[ "$provenance_path" = /* ]] || die "--provenance must be absolute"
fi

load_config "${config_file:-$SCRIPT_DIR/.env}"
require_command mktemp
require_command mv
require_command rsync
[[ -n "${HARNESS_PI_PYTHON:-}" && -x "$HARNESS_PI_PYTHON" ]] ||
  die "the pinned Python executable is unavailable: ${HARNESS_PI_PYTHON:-unset}"
[[ -n "${HARNESS_PI_FLOCK:-}" && -x "$HARNESS_PI_FLOCK" ]] ||
  die "the pinned flock executable is unavailable: ${HARNESS_PI_FLOCK:-unset}"
[[ -x "$HARNESS_PI_GIT" && ! -L "$HARNESS_PI_GIT" ]] ||
  die "the pinned Git executable is unavailable: $HARNESS_PI_GIT"
[[ "$(canonical_path "$HARNESS_PI_GIT")" == "$HARNESS_PI_GIT" ]] ||
  die "the pinned Git executable must be canonical: $HARNESS_PI_GIT"
ensure_runtime_layout
assert_deploy_code_committed

readonly PUBLISH_LOG="$POINCARE_DEPLOY_STATE_DIR/cache-publish.jsonl"
readonly BUILD_JOB_LOCK="$POINCARE_STATE_DIR/build-job.lock"

[[ -d "$POINCARE_PI_LAKE_CACHE_ROOT" ]] ||
  die "immutable Lake cache root does not exist: $POINCARE_PI_LAKE_CACHE_ROOT"
[[ ! -L "$POINCARE_PI_LAKE_CACHE_ROOT" ]] ||
  die "immutable Lake cache root must not be a symbolic link"
[[ -O "$POINCARE_PI_LAKE_CACHE_ROOT" ]] ||
  die "immutable Lake cache root is not owned by the current user"
[[ -w "$POINCARE_PI_LAKE_CACHE_ROOT" ]] ||
  die "immutable Lake cache root is not writable"

# This lock is shared with every root build and Job Lean check. Publication is
# exclusive and nonblocking: an active build/check is a hard stop, never a cue
# to wait while .lake may be changing.
exec 9>"$BUILD_JOB_LOCK"
"$HARNESS_PI_FLOCK" --exclusive --nonblock 9 ||
  die "a root build or Harness Job holds the shared build/job exclusion lock"
exec 8>"$POINCARE_PI_LAKE_CACHE_ROOT/.publish.lock"
"$HARNESS_PI_FLOCK" --exclusive --nonblock 8 ||
  die "another cache publication is active"

if [[ -n "$source_override" ]]; then
  [[ "$source_override" = /* ]] || die "--source-root must be absolute"
  SOURCE_ROOT=$(canonical_path "$source_override") || die "cannot resolve --source-root"
else
  SOURCE_ROOT=$POINCARE_REPO_ROOT
fi
readonly SOURCE_ROOT
[[ -e "$SOURCE_ROOT/.git" || -L "$SOURCE_ROOT/.git" ]] ||
  die "cache source is not a Git worktree"
[[ "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse --show-toplevel)" == "$SOURCE_ROOT" ]] ||
  die "cache source does not match its Git top level"

git_common_dir() {
  local worktree=$1
  local common
  common=$("$HARNESS_PI_GIT" -C "$worktree" rev-parse --git-common-dir)
  if [[ "$common" != /* ]]; then
    common="$worktree/$common"
  fi
  canonical_path "$common"
}

[[ "$(git_common_dir "$SOURCE_ROOT")" == "$(git_common_dir "$POINCARE_REPO_ROOT")" ]] ||
  die "cache source is not a worktree of the configured repository"
case "$SOURCE_ROOT/" in
  "$POINCARE_PI_LAKE_CACHE_ROOT"/*)
    die "cache source must not live below the immutable cache root"
    ;;
esac
case "$POINCARE_PI_LAKE_CACHE_ROOT/" in
  "$SOURCE_ROOT"/*)
    die "immutable cache root must not live below the cache source"
    ;;
esac
if [[ "$SOURCE_ROOT" == "$POINCARE_REPO_ROOT" ]]; then
  current_branch=$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" symbolic-ref --quiet --short HEAD) ||
    die "the integration checkout is detached; refusing to publish a cache"
  [[ "$current_branch" == "$POINCARE_INTEGRATION_BRANCH" ]] ||
    die "cache publication requires integration branch '$POINCARE_INTEGRATION_BRANCH'"
fi

readonly BASE_COMMIT=$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse HEAD)
readonly BASE_TREE=$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse 'HEAD^{tree}')
[[ "$BASE_COMMIT" =~ ^[0-9a-f]{40}$ ]] || die "HEAD is not a full Git commit ID"
[[ "$BASE_TREE" =~ ^[0-9a-f]{40}$ ]] || die "HEAD tree is not a full Git tree ID"

assert_source_stable() {
  [[ "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse HEAD)" == "$BASE_COMMIT" ]] ||
    die "cache source HEAD changed during publication"
  [[ "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse 'HEAD^{tree}')" == "$BASE_TREE" ]] ||
    die "cache source tree changed during publication"
  [[ -z "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" status --porcelain --untracked-files=all)" ]] ||
    die "cache publication requires a stable clean exact-base source checkout"
}

assert_source_stable

readonly SOURCE_CACHE="$SOURCE_ROOT/.lake"
readonly FINAL_CACHE="$POINCARE_PI_LAKE_CACHE_ROOT/$BASE_COMMIT"
readonly PROVENANCE_ROOT="$POINCARE_STATE_DIR/cache-provenance/$BASE_COMMIT"
[[ -d "$SOURCE_CACHE" && ! -L "$SOURCE_CACHE" ]] ||
  die "the clean integration checkout has no real .lake directory"
for required in packages build config; do
  [[ -d "$SOURCE_CACHE/$required" && ! -L "$SOURCE_CACHE/$required" ]] ||
    die "the completed build cache lacks .lake/$required/"
done
for reserved in \
  .harness-cache.json \
  .harness-package-overrides.json \
  .harness-cache-provenance.json \
  .harness-package-identities.json
do
  [[ ! -e "$SOURCE_CACHE/$reserved" && ! -L "$SOURCE_CACHE/$reserved" ]] ||
    die "source .lake contains the reserved path $reserved"
done
validate_source_cache() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$SOURCE_CACHE" <<'PY'
import os
import stat
import sys
from pathlib import Path

root = Path(sys.argv[1]).absolute()
if root.is_symlink() or not root.is_dir():
    raise SystemExit("source .lake must be a real directory")
root = root.resolve(strict=True)
pending = [root]
while pending:
    directory = pending.pop()
    for entry in os.scandir(directory):
        if entry.name == ".git":
            continue
        if "\n" in entry.name or "\r" in entry.name:
            raise SystemExit("source .lake contains an unsafe filename")
        path = Path(entry.path)
        info = entry.stat(follow_symlinks=False)
        if stat.S_ISDIR(info.st_mode):
            pending.append(path)
            continue
        if stat.S_ISREG(info.st_mode):
            continue
        if not stat.S_ISLNK(info.st_mode):
            raise SystemExit(f"source .lake contains a special file: {path.relative_to(root)}")
        target = os.readlink(path)
        if not target or os.path.isabs(target) or "\x00" in target:
            raise SystemExit(f"source .lake contains an unsafe symlink: {path.relative_to(root)}")
        lexical_target = Path(os.path.abspath(path.parent / target))
        try:
            lexical_target.relative_to(root)
            resolved = path.resolve(strict=True)
            resolved.relative_to(root)
        except (OSError, ValueError) as exc:
            raise SystemExit(
                f"source .lake symlink escapes or is broken: {path.relative_to(root)}"
            ) from exc
        if not resolved.is_file():
            raise SystemExit(
                f"source .lake symlink must resolve to an internal regular file: {path.relative_to(root)}"
            )
PY
}

source_cache_projection() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$SOURCE_CACHE" <<'PY'
import hashlib
import json
import os
import stat
import sys
from pathlib import Path, PurePosixPath

root = Path(sys.argv[1]).resolve(strict=True)
reserved = {
    PurePosixPath(".harness-cache.json"),
    PurePosixPath(".harness-package-overrides.json"),
    PurePosixPath(".harness-cache-provenance.json"),
    PurePosixPath(".harness-package-identities.json"),
}
records = []
pending = [(root, PurePosixPath("."))]
while pending:
    directory, relative_directory = pending.pop()
    entries = sorted(os.scandir(directory), key=lambda item: item.name)
    children = []
    for entry in entries:
        relative = (
            PurePosixPath(entry.name)
            if relative_directory == PurePosixPath(".")
            else relative_directory / entry.name
        )
        if entry.name == ".git" or relative in reserved:
            continue
        info = entry.stat(follow_symlinks=False)
        if stat.S_ISDIR(info.st_mode):
            records.append({"kind": "directory", "path": relative.as_posix()})
            children.append((Path(entry.path), relative))
            continue
        if stat.S_ISLNK(info.st_mode):
            target = Path(entry.path).resolve(strict=True)
            target.relative_to(root)
            target_info = target.stat()
            if not stat.S_ISREG(target_info.st_mode):
                raise SystemExit(f"source projection symlink is not a file: {relative}")
            file_path = target
            size = target_info.st_size
        elif stat.S_ISREG(info.st_mode):
            file_path = Path(entry.path)
            size = info.st_size
        else:
            raise SystemExit(f"source projection contains a special file: {relative}")
        digest = hashlib.sha256()
        with file_path.open("rb") as stream:
            while chunk := stream.read(1024 * 1024):
                digest.update(chunk)
        records.append({
            "kind": "file",
            "path": relative.as_posix(),
            "sha256": digest.hexdigest(),
            "size": size,
        })
    pending.extend(reversed(children))
raw = json.dumps(records, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")
print(hashlib.sha256(raw).hexdigest())
PY
}

validate_cache_provenance() {
  local output_path=${1:-}
  PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
  PYTHONDONTWRITEBYTECODE=1 \
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$provenance_path" "$PROVENANCE_ROOT" "$SOURCE_ROOT" \
    "$BASE_COMMIT" "$BASE_TREE" "$BUILD_JOB_LOCK" \
    "$SOURCE_PROJECTION_SHA256" "$output_path" <<'PY'
import datetime as dt
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path, PurePosixPath

from harness.v2.pi.security import SecurityError, _sealed_tree_attestation

(
    record_raw,
    provenance_root_raw,
    source_raw,
    base_commit,
    base_tree,
    lock_raw,
    source_projection,
    output_raw,
) = sys.argv[1:]
hex64 = re.compile(r"[0-9a-f]{64}")
task_id = re.compile(r"[a-z0-9][a-z0-9-]{0,127}")

def immutable_file(path: Path, *, cap: int, label: str) -> tuple[Path, bytes]:
    lexical = Path(os.path.abspath(path))
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise SystemExit(f"{label} cannot be resolved: {exc}") from exc
    if lexical != resolved or path.is_symlink():
        raise SystemExit(f"{label} must not traverse a symbolic link")
    info = os.lstat(resolved)
    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
        raise SystemExit(f"{label} must be a singly linked regular file")
    if info.st_uid != os.getuid() or info.st_mode & 0o222:
        raise SystemExit(f"{label} must be owner-controlled and immutable")
    if info.st_size > cap:
        raise SystemExit(f"{label} exceeds its byte cap")
    return resolved, resolved.read_bytes()

record_path, raw = immutable_file(Path(record_raw), cap=64 * 1024, label="cache provenance")
root = Path(os.path.abspath(provenance_root_raw))
if root.is_symlink() or not root.is_dir() or root.resolve(strict=True) != root:
    raise SystemExit("exact-base cache provenance root must be a real directory")
try:
    record_path.relative_to(root)
except ValueError as exc:
    raise SystemExit("cache provenance must live below the exact-base append-only evidence root") from exc
bundle = record_path.parent

try:
    document = json.loads(raw)
except (UnicodeDecodeError, json.JSONDecodeError) as exc:
    raise SystemExit("cache provenance is not valid UTF-8 JSON") from exc
canonical = (json.dumps(document, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii")
if raw != canonical:
    raise SystemExit("cache provenance must use canonical JSON bytes")
top_keys = {
    "schema_version", "base_commit", "base_tree", "source_root",
    "source_cache_projection_sha256", "exclusion_lock", "root_build",
    "selected_task", "module_gate", "executables", "lean_toolchain",
}
if not isinstance(document, dict) or set(document) != top_keys:
    raise SystemExit("cache provenance has an invalid top-level shape")
if document["schema_version"] != "poincare.cache-provenance.v1":
    raise SystemExit("cache provenance schema version is unsupported")
if document["base_commit"] != base_commit or document["base_tree"] != base_tree:
    raise SystemExit("cache provenance is not for the exact source commit and tree")
if document["source_cache_projection_sha256"] != source_projection:
    raise SystemExit("cache provenance does not bind the post-build source cache projection")
source = Path(source_raw).resolve(strict=True)
if document["source_root"] != str(source):
    raise SystemExit("cache provenance names a different exact-base source root")
lock = Path(lock_raw).absolute()
if document["exclusion_lock"] != str(lock):
    raise SystemExit("cache provenance names a different build/job exclusion lock")

def current_executable_record(raw_path: str, label: str) -> dict[str, object]:
    path = Path(raw_path)
    if not path.is_absolute() or os.path.normpath(raw_path) != raw_path or path.is_symlink():
        raise SystemExit(f"{label} executable path is invalid")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise SystemExit(f"cannot resolve {label} executable: {exc}") from exc
    before = os.lstat(path)
    if resolved != path or not stat.S_ISREG(before.st_mode) or not os.access(path, os.X_OK):
        raise SystemExit(f"{label} is not a canonical executable regular file")
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        opened = os.fstat(descriptor)
        identity = (
            before.st_dev, before.st_ino, before.st_mode, before.st_nlink,
            before.st_size, before.st_mtime_ns, before.st_ctime_ns,
        )
        if identity != (
            opened.st_dev, opened.st_ino, opened.st_mode, opened.st_nlink,
            opened.st_size, opened.st_mtime_ns, opened.st_ctime_ns,
        ):
            raise SystemExit(f"{label} executable changed while opening")
        digest = hashlib.sha256()
        total = 0
        while chunk := os.read(descriptor, 1024 * 1024):
            total += len(chunk)
            if total > 256 * 1024 * 1024:
                raise SystemExit(f"{label} executable exceeds its byte cap")
            digest.update(chunk)
        after = os.fstat(descriptor)
        if identity != (
            after.st_dev, after.st_ino, after.st_mode, after.st_nlink,
            after.st_size, after.st_mtime_ns, after.st_ctime_ns,
        ) or total != before.st_size:
            raise SystemExit(f"{label} executable changed while hashing")
        return {
            "path": str(path), "sha256": digest.hexdigest(),
            "size_bytes": total, "mode": stat.S_IMODE(before.st_mode),
        }
    finally:
        os.close(descriptor)

expected_executables = {
    "git": current_executable_record(os.environ["HARNESS_PI_GIT"], "Git"),
    "lake": current_executable_record(
        str(Path(os.environ["POINCARE_PI_TOOLCHAIN_ROOT"]) / "bin/lake"), "Lake"
    ),
    "lean": current_executable_record(
        str(Path(os.environ["POINCARE_PI_TOOLCHAIN_ROOT"]) / "bin/lean"), "Lean"
    ),
}
if document["executables"] != expected_executables:
    raise SystemExit(
        "cache provenance executable identity does not match pinned Git/Lake/Lean"
    )

def current_lean_toolchain() -> dict[str, object]:
    root_raw = os.environ["POINCARE_PI_TOOLCHAIN_ROOT"]
    root = Path(root_raw)
    if (
        not root.is_absolute()
        or os.path.normpath(root_raw) != root_raw
        or root.is_symlink()
        or not root.is_dir()
    ):
        raise SystemExit("Lean toolchain root is not a canonical real directory")
    try:
        resolved_root = root.resolve(strict=True)
    except OSError as exc:
        raise SystemExit(f"cannot resolve Lean toolchain root: {exc}") from exc
    if resolved_root != root:
        raise SystemExit("Lean toolchain root is not canonical")
    compiler_lib = root / "lib" / "lean"
    if compiler_lib.is_symlink() or not compiler_lib.is_dir():
        raise SystemExit("Lean compiler library is not a real directory")
    try:
        resolved_lib = compiler_lib.resolve(strict=True)
        resolved_lib.relative_to(root)
    except (OSError, ValueError) as exc:
        raise SystemExit("Lean compiler library escapes its toolchain root") from exc
    if resolved_lib != compiler_lib:
        raise SystemExit("Lean compiler library path is not canonical")
    try:
        digest, entry_count, _ = _sealed_tree_attestation(
            compiler_lib,
            "Lean compiler library",
            require_sealed=False,
            allow_internal_symlinks=True,
        )
    except SecurityError as exc:
        raise SystemExit(f"cannot attest Lean compiler library: {exc}") from exc
    return {
        "root": str(root),
        "compiler_lib": {
            "path": str(compiler_lib),
            "tree_sha256": digest,
            "entry_count": entry_count,
        },
    }

if document["lean_toolchain"] != current_lean_toolchain():
    raise SystemExit("cache provenance Lean toolchain closure identity changed")

def relative_artifact(reference: object, label: str, cap: int) -> bytes:
    if not isinstance(reference, dict) or set(reference) != {"path", "sha256"}:
        raise SystemExit(f"{label} reference has an invalid shape")
    raw_path = reference["path"]
    digest = reference["sha256"]
    if not isinstance(raw_path, str) or not raw_path or len(raw_path) > 512:
        raise SystemExit(f"{label} path is invalid")
    pure = PurePosixPath(raw_path)
    if pure.is_absolute() or any(part in {"", ".", ".."} for part in pure.parts):
        raise SystemExit(f"{label} path must be a normalized bundle-relative path")
    if "\\" in raw_path or "\n" in raw_path or "\r" in raw_path:
        raise SystemExit(f"{label} path contains unsafe characters")
    if not isinstance(digest, str) or hex64.fullmatch(digest) is None:
        raise SystemExit(f"{label} SHA-256 is invalid")
    candidate, content = immutable_file(bundle / Path(*pure.parts), cap=cap, label=label)
    try:
        candidate.relative_to(bundle)
    except ValueError as exc:
        raise SystemExit(f"{label} escaped its immutable evidence bundle") from exc
    if hashlib.sha256(content).hexdigest() != digest:
        raise SystemExit(f"{label} SHA-256 mismatch")
    return content

def timestamp(value: object, label: str) -> dt.datetime:
    if not isinstance(value, str) or re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", value) is None:
        raise SystemExit(f"{label} is not a canonical UTC timestamp")
    return dt.datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)

step_keys = {"argv", "status", "exit_code", "started_at", "completed_at", "stdout", "stderr"}
def checked_step(value: object, label: str) -> tuple[list[str], dt.datetime, dt.datetime]:
    if not isinstance(value, dict) or set(value) != step_keys:
        raise SystemExit(f"{label} has an invalid shape")
    argv = value["argv"]
    if not isinstance(argv, list) or not argv or any(not isinstance(item, str) or not item for item in argv):
        raise SystemExit(f"{label} argv is invalid")
    if value["status"] != "passed" or value["exit_code"] != 0:
        raise SystemExit(f"{label} did not record a successful completion")
    started = timestamp(value["started_at"], f"{label}.started_at")
    completed = timestamp(value["completed_at"], f"{label}.completed_at")
    if completed < started:
        raise SystemExit(f"{label} completion predates its start")
    relative_artifact(value["stdout"], f"{label} stdout", 256 * 1024 * 1024)
    relative_artifact(value["stderr"], f"{label} stderr", 256 * 1024 * 1024)
    return argv, started, completed

root_build = document["root_build"]
if not isinstance(root_build, dict) or set(root_build) != {"commands"}:
    raise SystemExit("root-build provenance has an invalid shape")
root_commands = root_build["commands"]
if not isinstance(root_commands, list) or len(root_commands) != 2:
    raise SystemExit("root-build provenance must contain the build and root elaboration")
root_build_argv, _, root_build_completed = checked_step(root_commands[0], "root build")
root_lean_argv, root_lean_started, root_completed = checked_step(
    root_commands[1], "root elaboration"
)
if root_build_argv != ["env", "LEAN_NUM_THREADS=1", "lake", "build"]:
    raise SystemExit("root-build provenance must record the exact single-threaded lake build argv")
if root_lean_argv != [
    "env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "Poincare.lean"
]:
    raise SystemExit("root-build provenance must record exact Poincare.lean elaboration")
if root_lean_started < root_build_completed:
    raise SystemExit("root elaboration must run after the completed root build")

task = document["selected_task"]
if not isinstance(task, dict) or set(task) != {"id", "revision", "base_commit", "source"}:
    raise SystemExit("selected Task provenance has an invalid shape")
if not isinstance(task["id"], str) or task_id.fullmatch(task["id"]) is None:
    raise SystemExit("selected Task ID is invalid")
if isinstance(task["revision"], bool) or not isinstance(task["revision"], int) or task["revision"] < 1:
    raise SystemExit("selected Task revision is invalid")
if task["base_commit"] != base_commit:
    raise SystemExit("selected Task does not use the cache base commit")
task_raw = relative_artifact(task["source"], "selected Task source", 1024 * 1024)
try:
    task_document = json.loads(task_raw)
except (UnicodeDecodeError, json.JSONDecodeError) as exc:
    raise SystemExit("selected Task source is not valid JSON") from exc
if (
    not isinstance(task_document, dict)
    or task_document.get("id") != task["id"]
    or task_document.get("revision") != task["revision"]
    or task_document.get("base_commit") != base_commit
):
    raise SystemExit("selected Task identity does not match its source record")
commands = task_document.get("acceptance", {}).get("commands")
if not isinstance(commands, list) or not commands:
    raise SystemExit("selected Task has no acceptance commands")

gate = document["module_gate"]
gate_keys = step_keys | {"command_index"}
if not isinstance(gate, dict) or set(gate) != gate_keys:
    raise SystemExit("module-gate provenance has an invalid shape")
command_index = gate["command_index"]
if isinstance(command_index, bool) or not isinstance(command_index, int) or not 0 <= command_index < len(commands):
    raise SystemExit("module-gate command index is invalid")
gate_step = {key: gate[key] for key in step_keys}
gate_argv, gate_started, _ = checked_step(gate_step, "module gate")
if gate_argv != commands[command_index]:
    raise SystemExit("module gate is not the selected Task acceptance command")
lean_prefix = ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean"]
build_prefix = ["env", "LEAN_NUM_THREADS=1", "lake", "build"]
if gate_argv[:5] == lean_prefix and len(gate_argv) == 6:
    module_path = gate_argv[5]
    pure = PurePosixPath(module_path)
    if pure.is_absolute() or pure.suffix != ".lean" or any(part in {"", ".", ".."} for part in pure.parts):
        raise SystemExit("selected Lean module gate path is unsafe")
    candidate = source / Path(*pure.parts)
    if candidate.is_symlink() or not candidate.is_file() or candidate.resolve(strict=True) != candidate.absolute():
        raise SystemExit("selected Lean module gate source is not a real exact-base file")
elif gate_argv[:4] == build_prefix and len(gate_argv) == 5:
    if re.fullmatch(r"[A-Za-z0-9_.-]+", gate_argv[4]) is None:
        raise SystemExit("selected Lake module target is unsafe")
else:
    raise SystemExit("selected Task provenance must name one focused Lean/module build gate")
if gate_started < root_completed:
    raise SystemExit("selected module gate must run after the completed root build")

digest = hashlib.sha256(raw).hexdigest()
if output_raw:
    output = Path(output_raw)
    flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(output, flags, 0o400)
    try:
        os.write(descriptor, raw)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
print(digest)
PY
}

package_identities() {
  local mode=$1
  local output=$2
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$SOURCE_ROOT" "$mode" "$output" "$HARNESS_PI_GIT" <<'PY'
import json
import os
import re
import stat
import subprocess
import sys
from pathlib import Path

source = Path(sys.argv[1]).resolve(strict=True)
mode, output_raw, git_executable = sys.argv[2:]
output = Path(output_raw)
manifest_path = source / "lake-manifest.json"
raw_manifest = manifest_path.read_bytes()
if len(raw_manifest) > 1024 * 1024:
    raise SystemExit("lake-manifest.json exceeds its byte cap")
try:
    manifest = json.loads(raw_manifest)
except (UnicodeDecodeError, json.JSONDecodeError) as exc:
    raise SystemExit("lake-manifest.json is not valid JSON") from exc
if (
    not isinstance(manifest, dict)
    or manifest.get("version") != "1.1.0"
    or manifest.get("packagesDir") != ".lake/packages"
    or manifest.get("lakeDir") != ".lake"
    or not isinstance(manifest.get("packages"), list)
    or not manifest["packages"]
    or len(manifest["packages"]) > 256
):
    raise SystemExit("lake-manifest.json is not the supported Lake 1.1.0 layout")

packages_root = source / ".lake/packages"
if packages_root.is_symlink() or not packages_root.is_dir():
    raise SystemExit("source cache has no real dependency package directory")
records = []
seen = set()
expected_names = set()
git_env = os.environ.copy()
git_env["GIT_NO_REPLACE_OBJECTS"] = "1"
git_env["GIT_OPTIONAL_LOCKS"] = "0"

def run_git(package: Path, *arguments: str, allow_empty: bool = False) -> str:
    result = subprocess.run(
        [git_executable, "-c", "core.fsmonitor=false", "-c", "core.untrackedCache=false", "-C", str(package), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=git_env,
    )
    if result.returncode != 0:
        error = result.stderr.decode("utf-8", "replace").strip()
        raise SystemExit(f"cannot audit dependency package {package.name}: {error or result.returncode}")
    text = result.stdout.decode("utf-8", "strict").strip()
    if not allow_empty and not text:
        raise SystemExit(f"dependency package {package.name} returned an empty Git identity")
    return text

for package_record in manifest["packages"]:
    if not isinstance(package_record, dict) or package_record.get("type") != "git":
        raise SystemExit("every lake-manifest dependency must be a Git package")
    name = package_record.get("name")
    url = package_record.get("url")
    revision = package_record.get("rev")
    if not isinstance(name, str) or re.fullmatch(r"[A-Za-z0-9_.-]+", name) is None or name in seen:
        raise SystemExit("lake-manifest package name is unsafe or duplicated")
    if not isinstance(url, str) or not url or len(url) > 2048 or "\n" in url or "\r" in url:
        raise SystemExit(f"lake-manifest package URL is invalid: {name}")
    if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
        raise SystemExit(f"lake-manifest package revision is not exact: {name}")
    seen.add(name)
    expected_names.add(name)
    package = packages_root / name
    if package.is_symlink() or not package.is_dir() or package.resolve(strict=True) != package.absolute():
        raise SystemExit(f"dependency package is not a real in-cache directory: {name}")
    git_marker = package / ".git"
    if git_marker.is_symlink() or not (git_marker.is_dir() or git_marker.is_file()):
        raise SystemExit(f"dependency package has no real Git metadata: {name}")
    if Path(run_git(package, "rev-parse", "--show-toplevel")).resolve(strict=True) != package:
        raise SystemExit(f"dependency package Git root is redirected: {name}")
    status = run_git(package, "status", "--porcelain=v1", "--untracked-files=all", allow_empty=True)
    if status:
        raise SystemExit(f"dependency package is dirty: {name}")
    head = run_git(package, "rev-parse", "--verify", "HEAD^{commit}")
    recorded = run_git(package, "rev-parse", "--verify", f"{revision}^{{commit}}")
    if head != revision or recorded != revision:
        raise SystemExit(f"dependency package HEAD does not match lake-manifest rev: {name}")
    expected_tree = run_git(package, "rev-parse", "--verify", f"{revision}^{{tree}}")
    checkout_tree = run_git(package, "rev-parse", "--verify", "HEAD^{tree}")
    if re.fullmatch(r"[0-9a-f]{40}", expected_tree) is None or checkout_tree != expected_tree:
        raise SystemExit(f"dependency package tree does not match its recorded revision: {name}")
    tree_rows = run_git(package, "ls-tree", "-r", "--full-tree", revision, allow_empty=True)
    if any(row.startswith("160000 ") for row in tree_rows.splitlines()):
        raise SystemExit(f"dependency package contains an unaudited Git submodule: {name}")
    origin = run_git(package, "config", "--get", "remote.origin.url")
    if origin != url:
        raise SystemExit(f"dependency package origin does not match lake-manifest URL: {name}")
    records.append({
        "checkout_head": head,
        "checkout_tree": checkout_tree,
        "expected_tree": expected_tree,
        "manifest_rev": revision,
        "manifest_url": url,
        "name": name,
    })

actual_names = set()
for entry in os.scandir(packages_root):
    info = entry.stat(follow_symlinks=False)
    if not stat.S_ISDIR(info.st_mode) or stat.S_ISLNK(info.st_mode):
        raise SystemExit(f"dependency package root has a non-directory entry: {entry.name}")
    actual_names.add(entry.name)
if actual_names != expected_names:
    raise SystemExit("source cache dependency directories do not exactly match lake-manifest packages")

payload = {
    "schema_version": "poincare.lake-package-identities.v1",
    "packages": sorted(records, key=lambda item: item["name"]),
}
raw = (json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii")
if mode == "write":
    flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(output, flags, 0o400)
    try:
        os.write(descriptor, raw)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
elif mode == "check":
    if output.is_symlink() or not output.is_file() or output.read_bytes() != raw:
        raise SystemExit("dependency package identities changed during publication")
else:
    raise SystemExit("invalid package-identity audit mode")
PY
}

validate_source_cache
readonly SOURCE_PROJECTION_SHA256=$(source_cache_projection)
[[ "$SOURCE_PROJECTION_SHA256" =~ ^[0-9a-f]{64}$ ]] ||
  die "source cache projection digest failed"
if (( projection_only == 1 )); then
  validate_source_cache
  assert_source_stable
  [[ "$(source_cache_projection)" == "$SOURCE_PROJECTION_SHA256" ]] ||
    die "source cache changed while its provenance projection was computed"
  printf '%s\n' "$SOURCE_PROJECTION_SHA256"
  exit 0
fi

readonly PROVENANCE_SHA256=$(validate_cache_provenance)
[[ "$PROVENANCE_SHA256" =~ ^[0-9a-f]{64}$ ]] || die "cache provenance digest failed"

# The shared lock is the admission boundary. If a runtime database already
# exists, independently require that it records no active Job even though a
# correctly coordinated Job would also prevent this exclusive lock.
if [[ -e "$POINCARE_STATE_DIR/harness.sqlite3" || -L "$POINCARE_STATE_DIR/harness.sqlite3" ]]; then
  "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_STATE_DIR/harness.sqlite3" <<'PY'
import os
import sqlite3
import stat
import sys
from pathlib import Path

path = Path(sys.argv[1]).absolute()
if path.is_symlink() or not path.is_file() or path.resolve(strict=True) != path:
    raise SystemExit("Harness runtime database is not a real file")
info = os.lstat(path)
if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
    raise SystemExit("Harness runtime database is not owner-controlled")
connection = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
try:
    row = connection.execute(
        "SELECT COUNT(*) FROM jobs WHERE state IN ('preparing','running','reviewing')"
    ).fetchone()
except sqlite3.DatabaseError as exc:
    raise SystemExit(f"cannot audit active Harness Jobs: {exc}") from exc
finally:
    connection.close()
if row is None or row[0] != 0:
    raise SystemExit("cache publication requires zero active Harness Jobs")
PY
fi

# An exact, fully valid final snapshot can exist when the process crashed after
# atomic rename but before its success event. Revalidate and recover that event
# without modifying or replacing any cache byte.
if [[ -e "$FINAL_CACHE" || -L "$FINAL_CACHE" ]]; then
  [[ -d "$FINAL_CACHE" && ! -L "$FINAL_CACHE" ]] ||
    die "the existing exact-base cache path is not a real directory"
  "$SCRIPT_DIR/verify-lean-cache.sh" --source-root "$SOURCE_ROOT" \
    "$POINCARE_CONFIG_FILE" >/dev/null ||
    die "an existing exact-base cache is invalid and must be preserved for human review"
  package_identities check "$FINAL_CACHE/.harness-package-identities.json"
  readonly EXISTING_PROVENANCE_SHA256=$(
    "$HARNESS_PI_PYTHON" -S -P -B - \
      "$FINAL_CACHE/.harness-cache-provenance.json" <<'PY'
import hashlib
import sys
from pathlib import Path

digest = hashlib.sha256()
with Path(sys.argv[1]).open("rb") as stream:
    while chunk := stream.read(1024 * 1024):
        digest.update(chunk)
print(digest.hexdigest())
PY
  )
  [[ "$EXISTING_PROVENANCE_SHA256" == "$PROVENANCE_SHA256" ]] ||
    die "an existing cache has different publication provenance; it will not be overwritten"
  append_event "$PUBLISH_LOG" cache_publish_recovered \
    base_commit "$BASE_COMMIT" base_tree "$BASE_TREE" \
    provenance_sha256 "$PROVENANCE_SHA256"
  note "Recovered the verified immutable Lake cache publication for $BASE_COMMIT."
  exit 0
fi

# Require enough free space for a conservative logical-size copy while leaving
# the configured operational reserve available on the cache volume.
read -r CACHE_AVAILABLE_BYTES CACHE_REQUIRED_BYTES < <(
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$SOURCE_CACHE" "$POINCARE_PI_LAKE_CACHE_ROOT" \
    "$POINCARE_MIN_FREE_GIB" <<'PY'
import os
import stat
import sys
from pathlib import Path

source = Path(sys.argv[1]).resolve(strict=True)
cache_root = Path(sys.argv[2]).resolve(strict=True)
reserve = int(sys.argv[3]) * 1024**3
logical_size = 0
pending = [source]
while pending:
    directory = pending.pop()
    for entry in os.scandir(directory):
        if entry.name == ".git":
            continue
        info = entry.stat(follow_symlinks=False)
        if stat.S_ISDIR(info.st_mode):
            pending.append(Path(entry.path))
        elif stat.S_ISREG(info.st_mode):
            logical_size += info.st_size
        elif stat.S_ISLNK(info.st_mode):
            logical_size += Path(entry.path).resolve(strict=True).stat().st_size
filesystem = os.statvfs(cache_root)
available = filesystem.f_bavail * filesystem.f_frsize
print(available, logical_size + reserve)
PY
)
[[ "$CACHE_AVAILABLE_BYTES" =~ ^[0-9]+$ && "$CACHE_REQUIRED_BYTES" =~ ^[0-9]+$ ]] ||
  die "could not determine cache-root free space"
(( CACHE_AVAILABLE_BYTES >= CACHE_REQUIRED_BYTES )) ||
  die "cache root lacks space for the snapshot plus ${POINCARE_MIN_FREE_GIB} GiB reserve"

STAGING_CACHE=$(mktemp -d "$POINCARE_PI_LAKE_CACHE_ROOT/.staging.$BASE_COMMIT.XXXXXX") ||
  die "could not create cache staging directory"
readonly STAGING_CACHE
readonly COPY_AUDIT="$POINCARE_DEPLOY_STATE_DIR/cache-copy-${STAGING_CACHE##*/}.txt"
"$HARNESS_PI_PYTHON" -S -P -B - "$COPY_AUDIT" <<'PY'
import os
import sys

flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, "O_NOFOLLOW", 0)
descriptor = os.open(sys.argv[1], flags, 0o600)
os.close(descriptor)
PY
append_event "$PUBLISH_LOG" cache_publish_started \
  base_commit "$BASE_COMMIT" base_tree "$BASE_TREE" staging "${STAGING_CACHE##*/}" \
  provenance_sha256 "$PROVENANCE_SHA256" \
  cache_available_bytes "$CACHE_AVAILABLE_BYTES" cache_required_bytes "$CACHE_REQUIRED_BYTES"

publish_complete=0
record_publish_exit() {
  local status=$?
  if (( publish_complete == 0 )); then
    append_event "$PUBLISH_LOG" cache_publish_failed \
      base_commit "$BASE_COMMIT" exit_code "$status" staging "${STAGING_CACHE##*/}" \
      provenance_sha256 "$PROVENANCE_SHA256" || true
  fi
}
trap record_publish_exit EXIT

rsync --archive --copy-links --sparse \
  --exclude='.git' --exclude='.git/' -- "$SOURCE_CACHE/" "$STAGING_CACHE/"

# Validate both the Git checkout and copied bytes after rsync. The audit file is
# opened once with O_EXCL and only appended, so a failed comparison remains
# durable evidence associated with the preserved staging directory.
validate_source_cache
assert_source_stable
[[ "$(source_cache_projection)" == "$SOURCE_PROJECTION_SHA256" ]] ||
  die "post-build source cache projection changed before publication"
rsync --archive --copy-links --sparse --checksum --dry-run --itemize-changes \
  --delete --exclude='.git' --exclude='.git/' -- "$SOURCE_CACHE/" "$STAGING_CACHE/" \
  >> "$COPY_AUDIT"
[[ ! -s "$COPY_AUDIT" ]] ||
  die "source .lake changed while it was copied; failed staging is preserved"

"$HARNESS_PI_PYTHON" -S -P -B - "$STAGING_CACHE" <<'PY'
import os
import stat
import sys
from pathlib import Path

root = Path(sys.argv[1]).absolute()
if root.is_symlink() or not root.is_dir():
    raise SystemExit("staging cache must be a real directory")
root = root.resolve(strict=True)
pending = [root]
while pending:
    directory = pending.pop()
    for entry in os.scandir(directory):
        relative = Path(entry.path).relative_to(root)
        if entry.name == ".git":
            raise SystemExit(f"staging cache contains forbidden Git metadata: {relative}")
        if "\n" in entry.name or "\r" in entry.name:
            raise SystemExit("staging cache contains an unsafe filename")
        info = entry.stat(follow_symlinks=False)
        if stat.S_ISLNK(info.st_mode):
            raise SystemExit(f"staging cache contains a symlink: {relative}")
        if stat.S_ISDIR(info.st_mode):
            pending.append(Path(entry.path))
        elif not stat.S_ISREG(info.st_mode):
            raise SystemExit(f"staging cache contains a special file: {relative}")
        elif info.st_nlink != 1:
            raise SystemExit(f"staging cache contains a hard-linked file: {relative}")
PY

package_identities write "$STAGING_CACHE/.harness-package-identities.json"
readonly COPIED_PROVENANCE_SHA256=$(
  validate_cache_provenance "$STAGING_CACHE/.harness-cache-provenance.json"
)
[[ "$COPIED_PROVENANCE_SHA256" == "$PROVENANCE_SHA256" ]] ||
  die "cache provenance changed during publication"

# Replace Lake's Git package locations with the exact in-sandbox immutable
# package paths. Without this canonical override, stripping dependency .git
# metadata can make Lake attempt a network clone inside the isolated Job.
(
  cd "$POINCARE_DEPLOY_CODE_ROOT"
  PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B - "$SOURCE_ROOT" \
      "$STAGING_CACHE/.harness-package-overrides.json" <<'PY'
import os
import sys
from pathlib import Path

from harness.v2.pi.security import canonical_package_overrides

source, output = map(Path, sys.argv[1:])
raw = canonical_package_overrides(source)
flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, "O_NOFOLLOW", 0)
fd = os.open(output, flags, 0o400)
try:
    os.write(fd, raw)
    os.fsync(fd)
finally:
    os.close(fd)
PY
)

# Create the reserved manifest before freezing permissions. The Pi digest
# deliberately excludes only this root manifest, so compiled content, both
# audit sidecars, and all final content modes are covered by the digest.
"$HARNESS_PI_PYTHON" -S -P -B - "$STAGING_CACHE/.harness-cache.json" <<'PY'
import os
import sys

path = sys.argv[1]
flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, "O_NOFOLLOW", 0)
fd = os.open(path, flags, 0o600)
try:
    os.write(fd, b"{}\n")
finally:
    os.close(fd)
PY
chmod -R a-w -- "$STAGING_CACHE"

readonly CACHE_TREE_SHA256=$(
  cd "$POINCARE_DEPLOY_CODE_ROOT"
  PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B - "$STAGING_CACHE" <<'PY'
import sys
from pathlib import Path

from harness.v2.pi.security import lake_cache_tree_digest

print(lake_cache_tree_digest(Path(sys.argv[1])))
PY
)
[[ "$CACHE_TREE_SHA256" =~ ^[0-9a-f]{64}$ ]] || die "cache content digest failed"

chmod u+w -- "$STAGING_CACHE/.harness-cache.json"
(
  cd "$POINCARE_DEPLOY_CODE_ROOT"
  PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B - \
      "$STAGING_CACHE/.harness-cache.json" "$BASE_COMMIT" "$BASE_TREE" \
      "$CACHE_TREE_SHA256" "$SOURCE_ROOT/lean-toolchain" \
      "$SOURCE_ROOT/lake-manifest.json" \
      "$STAGING_CACHE/.harness-package-overrides.json" <<'PY'
import hashlib
import json
import os
import sys
from pathlib import Path

from harness.v2.pi.security import CACHE_MANIFEST_VERSION

(
    manifest_path,
    base_commit,
    base_tree,
    cache_digest,
    toolchain_path,
    lake_manifest_path,
    package_overrides_path,
) = sys.argv[1:]

def sha256_file(raw: str) -> str:
    digest = hashlib.sha256()
    with Path(raw).open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()

payload = {
    "schema_version": CACHE_MANIFEST_VERSION,
    "base_commit": base_commit,
    "base_tree": base_tree,
    "cache_tree_sha256": cache_digest,
    "package_overrides_sha256": sha256_file(package_overrides_path),
    "lean_toolchain_sha256": sha256_file(toolchain_path),
    "lake_manifest_sha256": sha256_file(lake_manifest_path),
}
raw = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")
fd = os.open(manifest_path, os.O_WRONLY | os.O_TRUNC | getattr(os, "O_NOFOLLOW", 0))
try:
    os.write(fd, raw)
    os.fsync(fd)
finally:
    os.close(fd)
PY
)
chmod a-w -- "$STAGING_CACHE/.harness-cache.json"

"$SCRIPT_DIR/verify-lean-cache.sh" --source-root "$SOURCE_ROOT" \
  --path "$STAGING_CACHE" "$POINCARE_CONFIG_FILE"
package_identities check "$STAGING_CACHE/.harness-package-identities.json"
[[ "$(validate_cache_provenance)" == "$PROVENANCE_SHA256" ]] ||
  die "external cache provenance changed before publication"
validate_source_cache
assert_source_stable
[[ "$(source_cache_projection)" == "$SOURCE_PROJECTION_SHA256" ]] ||
  die "post-build source cache projection changed before atomic publication"
rsync --archive --no-perms --omit-dir-times --copy-links --sparse \
  --checksum --dry-run --itemize-changes \
  --delete --exclude='.git' --exclude='.git/' \
  --exclude='.harness-cache.json' \
  --exclude='.harness-package-overrides.json' \
  --exclude='.harness-cache-provenance.json' \
  --exclude='.harness-package-identities.json' \
  -- "$SOURCE_CACHE/" "$STAGING_CACHE/" >> "$COPY_AUDIT"
[[ ! -s "$COPY_AUDIT" ]] ||
  die "source .lake changed before atomic publication; failed staging is preserved"
package_identities check "$STAGING_CACHE/.harness-package-identities.json"
[[ ! -e "$FINAL_CACHE" && ! -L "$FINAL_CACHE" ]] ||
  die "a cache snapshot appeared during publication; failed staging is preserved"
append_event "$PUBLISH_LOG" cache_publish_ready \
  base_commit "$BASE_COMMIT" base_tree "$BASE_TREE" \
  staging "${STAGING_CACHE##*/}" cache_tree_sha256 "$CACHE_TREE_SHA256" \
  provenance_sha256 "$PROVENANCE_SHA256"

# GNU mv -n never replaces an existing destination. The two held flock file
# descriptors serialize publication against builds/Jobs and other publishers;
# retaining STAGING_CACHE detects a lost destination race.
mv -T -n -- "$STAGING_CACHE" "$FINAL_CACHE"
[[ ! -e "$STAGING_CACHE" && ! -L "$STAGING_CACHE" ]] ||
  die "cache destination appeared during atomic publish; failed staging is preserved"

publish_complete=1
append_event "$PUBLISH_LOG" cache_published \
  base_commit "$BASE_COMMIT" base_tree "$BASE_TREE" \
  cache_tree_sha256 "$CACHE_TREE_SHA256" \
  provenance_sha256 "$PROVENANCE_SHA256"
trap - EXIT
note "Published and fully verified immutable Lake cache for $BASE_COMMIT."
