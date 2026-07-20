#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  printf 'Usage: %s [--source-root exact-base-checkout] [--path absolute-staging-path] [environment-file]\n' "${0##*/}"
}

cache_override=
source_override=
while (( $# > 0 )); do
  case "$1" in
    --source-root)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      source_override=$2
      shift 2
      ;;
    --path)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      cache_override=$2
      shift 2
      ;;
    *)
      break
      ;;
  esac
done
if (( $# > 1 )); then
  usage >&2
  exit 64
fi

load_config "${1:-$SCRIPT_DIR/.env}"
[[ -n "${HARNESS_PI_PYTHON:-}" && -x "$HARNESS_PI_PYTHON" ]] ||
  die "the pinned Python executable is unavailable: ${HARNESS_PI_PYTHON:-unset}"
[[ -x "$HARNESS_PI_GIT" && ! -L "$HARNESS_PI_GIT" ]] ||
  die "the pinned Git executable is unavailable: $HARNESS_PI_GIT"
[[ "$(canonical_path "$HARNESS_PI_GIT")" == "$HARNESS_PI_GIT" ]] ||
  die "the pinned Git executable must be canonical: $HARNESS_PI_GIT"
assert_deploy_code_committed

if [[ -n "$source_override" ]]; then
  [[ "$source_override" = /* ]] || die "--source-root must be absolute"
  SOURCE_ROOT=$(canonical_path "$source_override") || die "cannot resolve --source-root"
else
  SOURCE_ROOT=$POINCARE_REPO_ROOT
fi
readonly SOURCE_ROOT
[[ "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse --show-toplevel)" == "$SOURCE_ROOT" ]] ||
  die "cache source does not match its Git top level"
readonly BASE_COMMIT=$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse HEAD)
readonly BASE_TREE=$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse 'HEAD^{tree}')
[[ "$BASE_COMMIT" =~ ^[0-9a-f]{40}$ ]] || die "HEAD is not a full Git commit ID"
[[ "$BASE_TREE" =~ ^[0-9a-f]{40}$ ]] || die "HEAD tree is not a full Git tree ID"

if [[ -n "$cache_override" ]]; then
  [[ "$cache_override" = /* ]] || die "--path must be absolute"
  CACHE_PATH=$(canonical_path "$cache_override") || die "cannot resolve --path"
else
  CACHE_PATH="$POINCARE_PI_LAKE_CACHE_ROOT/$BASE_COMMIT"
fi
readonly CACHE_PATH

(
  cd "$POINCARE_DEPLOY_CODE_ROOT"
  PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B - "$CACHE_PATH" "$SOURCE_ROOT" \
      "$BASE_COMMIT" "$BASE_TREE" <<'PY'
import datetime as dt
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path, PurePosixPath

from harness.v2.pi.security import (
    SecurityError,
    _load_cache_manifest,
    _sealed_tree_attestation,
    _validate_package_overrides,
    lake_cache_tree_digest,
)

cache, worktree = map(Path, sys.argv[1:3])
base_commit, base_tree = sys.argv[3:5]
for required in ("packages", "build", "config"):
    candidate = cache / required
    if candidate.is_symlink() or not candidate.is_dir():
        raise SecurityError(f"immutable Lake cache lacks prebuilt {required}/")

# Every invocation performs the expensive content walk first. This is
# intentionally not a metadata-only or memoized verification shortcut.
actual_cache_digest = lake_cache_tree_digest(cache)
manifest, _ = _load_cache_manifest(
    cache,
    worktree=worktree,
    base_commit=base_commit,
    base_tree=base_tree,
)
if actual_cache_digest != manifest["cache_tree_sha256"]:
    raise SecurityError("immutable Lake cache content digest mismatch")
if _validate_package_overrides(cache, worktree) != manifest["package_overrides_sha256"]:
    raise SecurityError("immutable Lake package override digest mismatch")

hex40 = re.compile(r"[0-9a-f]{40}")
hex64 = re.compile(r"[0-9a-f]{64}")
safe_task_id = re.compile(r"[a-z0-9][a-z0-9-]{0,127}")
reserved = {
    PurePosixPath(".harness-cache.json"),
    PurePosixPath(".harness-package-overrides.json"),
    PurePosixPath(".harness-cache-provenance.json"),
    PurePosixPath(".harness-package-identities.json"),
}

def cache_file(name: str, *, cap: int) -> bytes:
    path = cache / name
    if path.is_symlink() or not path.is_file():
        raise SecurityError(f"immutable Lake cache is missing {name}")
    info = path.stat(follow_symlinks=False)
    if info.st_mode & 0o222 or info.st_nlink != 1 or info.st_size > cap:
        raise SecurityError(f"immutable Lake cache has an unsafe {name}")
    try:
        return path.read_bytes()
    except OSError as exc:
        raise SecurityError(f"cannot read immutable Lake cache {name}: {exc}") from exc

def canonical_document(name: str, *, cap: int) -> dict:
    raw = cache_file(name, cap=cap)
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SecurityError(f"immutable Lake cache {name} is not valid JSON") from exc
    if not isinstance(value, dict):
        raise SecurityError(f"immutable Lake cache {name} is not an object")
    expected = (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n"
    ).encode("ascii")
    if raw != expected:
        raise SecurityError(f"immutable Lake cache {name} is not canonical JSON")
    return value

def safe_reference(value: object, label: str) -> None:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        raise SecurityError(f"cache provenance {label} reference has an invalid shape")
    path = value["path"]
    digest = value["sha256"]
    if not isinstance(path, str) or not path or len(path) > 512:
        raise SecurityError(f"cache provenance {label} path is invalid")
    pure = PurePosixPath(path)
    if (
        pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
        or "\\" in path
        or "\n" in path
        or "\r" in path
    ):
        raise SecurityError(f"cache provenance {label} path is unsafe")
    if not isinstance(digest, str) or hex64.fullmatch(digest) is None:
        raise SecurityError(f"cache provenance {label} digest is invalid")

def timestamp(value: object, label: str) -> dt.datetime:
    if not isinstance(value, str) or re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", value) is None:
        raise SecurityError(f"cache provenance {label} timestamp is invalid")
    return dt.datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)

step_keys = {"argv", "status", "exit_code", "started_at", "completed_at", "stdout", "stderr"}
def checked_step(value: object, label: str) -> tuple[list[str], dt.datetime, dt.datetime]:
    if not isinstance(value, dict) or set(value) != step_keys:
        raise SecurityError(f"cache provenance {label} has an invalid shape")
    argv = value["argv"]
    if not isinstance(argv, list) or not argv or any(not isinstance(item, str) or not item for item in argv):
        raise SecurityError(f"cache provenance {label} argv is invalid")
    if value["status"] != "passed" or value["exit_code"] != 0:
        raise SecurityError(f"cache provenance {label} did not pass")
    started = timestamp(value["started_at"], f"{label}.started_at")
    completed = timestamp(value["completed_at"], f"{label}.completed_at")
    if completed < started:
        raise SecurityError(f"cache provenance {label} completion predates its start")
    safe_reference(value["stdout"], f"{label} stdout")
    safe_reference(value["stderr"], f"{label} stderr")
    return argv, started, completed

provenance = canonical_document(".harness-cache-provenance.json", cap=64 * 1024)
provenance_keys = {
    "schema_version", "base_commit", "base_tree", "source_root",
    "source_cache_projection_sha256", "exclusion_lock", "root_build",
    "selected_task", "module_gate", "executables", "lean_toolchain",
}
if set(provenance) != provenance_keys:
    raise SecurityError("immutable Lake cache provenance has an invalid shape")
if provenance["schema_version"] != "poincare.cache-provenance.v1":
    raise SecurityError("immutable Lake cache provenance version is unsupported")
if provenance["base_commit"] != base_commit or provenance["base_tree"] != base_tree:
    raise SecurityError("immutable Lake cache provenance has the wrong exact base")
projection_digest = provenance["source_cache_projection_sha256"]
if not isinstance(projection_digest, str) or hex64.fullmatch(projection_digest) is None:
    raise SecurityError("immutable Lake cache source projection digest is invalid")
for path_name in ("source_root", "exclusion_lock"):
    raw_path = provenance[path_name]
    if not isinstance(raw_path, str) or not Path(raw_path).is_absolute() or os.path.normpath(raw_path) != raw_path:
        raise SecurityError(f"immutable Lake cache provenance {path_name} is invalid")
if not provenance["exclusion_lock"].endswith("/harness/v2/state/build-job.lock"):
    raise SecurityError("immutable Lake cache provenance names the wrong exclusion lock")

def current_executable_record(raw_path: str, label: str) -> dict[str, object]:
    path = Path(raw_path)
    if not path.is_absolute() or os.path.normpath(raw_path) != raw_path or path.is_symlink():
        raise SecurityError(f"immutable Lake {label} executable path is invalid")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise SecurityError(f"cannot resolve immutable Lake {label} executable: {exc}") from exc
    before = os.lstat(path)
    if resolved != path or not stat.S_ISREG(before.st_mode) or not os.access(path, os.X_OK):
        raise SecurityError(f"immutable Lake {label} executable is invalid")
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
            raise SecurityError(f"immutable Lake {label} executable changed while opening")
        digest = hashlib.sha256()
        total = 0
        while chunk := os.read(descriptor, 1024 * 1024):
            total += len(chunk)
            if total > 256 * 1024 * 1024:
                raise SecurityError(f"immutable Lake {label} executable exceeds its byte cap")
            digest.update(chunk)
        after = os.fstat(descriptor)
        if identity != (
            after.st_dev, after.st_ino, after.st_mode, after.st_nlink,
            after.st_size, after.st_mtime_ns, after.st_ctime_ns,
        ) or total != before.st_size:
            raise SecurityError(f"immutable Lake {label} executable changed while hashing")
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
if provenance["executables"] != expected_executables:
    raise SecurityError("immutable Lake provenance executable identity changed")

def current_lean_toolchain() -> dict[str, object]:
    root_raw = os.environ["POINCARE_PI_TOOLCHAIN_ROOT"]
    root = Path(root_raw)
    if (
        not root.is_absolute()
        or os.path.normpath(root_raw) != root_raw
        or root.is_symlink()
        or not root.is_dir()
    ):
        raise SecurityError("immutable Lake Lean toolchain root is invalid")
    try:
        resolved_root = root.resolve(strict=True)
    except OSError as exc:
        raise SecurityError(f"cannot resolve immutable Lake Lean toolchain root: {exc}") from exc
    if resolved_root != root:
        raise SecurityError("immutable Lake Lean toolchain root is not canonical")
    compiler_lib = root / "lib" / "lean"
    if compiler_lib.is_symlink() or not compiler_lib.is_dir():
        raise SecurityError("immutable Lake Lean compiler library is invalid")
    try:
        resolved_lib = compiler_lib.resolve(strict=True)
        resolved_lib.relative_to(root)
    except (OSError, ValueError) as exc:
        raise SecurityError("immutable Lake Lean compiler library escapes its root") from exc
    if resolved_lib != compiler_lib:
        raise SecurityError("immutable Lake Lean compiler library path is not canonical")
    digest, entry_count, _ = _sealed_tree_attestation(
        compiler_lib,
        "Lean compiler library",
        require_sealed=False,
        allow_internal_symlinks=True,
    )
    return {
        "root": str(root),
        "compiler_lib": {
            "path": str(compiler_lib),
            "tree_sha256": digest,
            "entry_count": entry_count,
        },
    }

if provenance["lean_toolchain"] != current_lean_toolchain():
    raise SecurityError("immutable Lake Lean toolchain closure identity changed")

root_build = provenance["root_build"]
if not isinstance(root_build, dict) or set(root_build) != {"commands"}:
    raise SecurityError("immutable Lake root-build provenance has an invalid shape")
root_commands = root_build["commands"]
if not isinstance(root_commands, list) or len(root_commands) != 2:
    raise SecurityError("immutable Lake root-build provenance lacks required commands")
build_argv, _, build_completed = checked_step(root_commands[0], "root build")
lean_argv, lean_started, root_completed = checked_step(root_commands[1], "root elaboration")
if build_argv != ["env", "LEAN_NUM_THREADS=1", "lake", "build"]:
    raise SecurityError("immutable Lake root-build argv is not canonical")
if lean_argv != ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "Poincare.lean"]:
    raise SecurityError("immutable Lake root-elaboration argv is not canonical")
if lean_started < build_completed:
    raise SecurityError("immutable Lake root elaboration predates the root build")

task = provenance["selected_task"]
if not isinstance(task, dict) or set(task) != {"id", "revision", "base_commit", "source"}:
    raise SecurityError("immutable Lake selected-Task provenance has an invalid shape")
if not isinstance(task["id"], str) or safe_task_id.fullmatch(task["id"]) is None:
    raise SecurityError("immutable Lake selected Task ID is invalid")
if isinstance(task["revision"], bool) or not isinstance(task["revision"], int) or task["revision"] < 1:
    raise SecurityError("immutable Lake selected Task revision is invalid")
if task["base_commit"] != base_commit:
    raise SecurityError("immutable Lake selected Task has the wrong base")
safe_reference(task["source"], "selected Task source")

gate = provenance["module_gate"]
if not isinstance(gate, dict) or set(gate) != step_keys | {"command_index"}:
    raise SecurityError("immutable Lake module-gate provenance has an invalid shape")
command_index = gate["command_index"]
if isinstance(command_index, bool) or not isinstance(command_index, int) or command_index < 0:
    raise SecurityError("immutable Lake module-gate command index is invalid")
gate_step = {key: gate[key] for key in step_keys}
gate_argv, gate_started, _ = checked_step(gate_step, "module gate")
lean_prefix = ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean"]
build_prefix = ["env", "LEAN_NUM_THREADS=1", "lake", "build"]
valid_lean = gate_argv[:5] == lean_prefix and len(gate_argv) == 6 and gate_argv[5].endswith(".lean")
if valid_lean:
    lean_path = PurePosixPath(gate_argv[5])
    valid_lean = (
        not lean_path.is_absolute()
        and all(part not in {"", ".", ".."} for part in lean_path.parts)
        and "\\" not in gate_argv[5]
    )
valid_build = (
    gate_argv[:4] == build_prefix
    and len(gate_argv) == 5
    and re.fullmatch(r"[A-Za-z0-9_.-]+", gate_argv[4]) is not None
)
if not (valid_lean or valid_build):
    raise SecurityError("immutable Lake selected module gate is not a focused Lean command")
if gate_started < root_completed:
    raise SecurityError("immutable Lake selected module gate predates the root build")

# Recompute the provenance-bound projection from the frozen cache itself,
# excluding only the four Harness metadata files added by publication.
projection_records = []
pending = [(cache, PurePosixPath("."))]
while pending:
    directory, relative_directory = pending.pop()
    try:
        entries = sorted(os.scandir(directory), key=lambda item: item.name)
    except OSError as exc:
        raise SecurityError(f"cannot enumerate immutable cache projection: {exc}") from exc
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
            projection_records.append({"kind": "directory", "path": relative.as_posix()})
            children.append((Path(entry.path), relative))
        elif stat.S_ISREG(info.st_mode):
            digest = hashlib.sha256()
            with Path(entry.path).open("rb") as stream:
                while chunk := stream.read(1024 * 1024):
                    digest.update(chunk)
            projection_records.append({
                "kind": "file",
                "path": relative.as_posix(),
                "sha256": digest.hexdigest(),
                "size": info.st_size,
            })
        else:
            raise SecurityError(f"immutable cache projection contains an unsafe entry: {relative}")
    pending.extend(reversed(children))
projection_raw = json.dumps(
    projection_records, sort_keys=True, separators=(",", ":"), ensure_ascii=True
).encode("ascii")
if hashlib.sha256(projection_raw).hexdigest() != projection_digest:
    raise SecurityError("immutable Lake cache does not match its post-build source projection")

identities = canonical_document(".harness-package-identities.json", cap=256 * 1024)
if set(identities) != {"schema_version", "packages"}:
    raise SecurityError("immutable Lake dependency identities have an invalid shape")
if identities["schema_version"] != "poincare.lake-package-identities.v1":
    raise SecurityError("immutable Lake dependency identity version is unsupported")
identity_packages = identities["packages"]
if not isinstance(identity_packages, list) or not identity_packages or len(identity_packages) > 256:
    raise SecurityError("immutable Lake dependency identity list is invalid")
try:
    lake_manifest = json.loads((worktree / "lake-manifest.json").read_bytes())
except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
    raise SecurityError("cannot read exact-base lake-manifest for package identities") from exc
manifest_packages = lake_manifest.get("packages") if isinstance(lake_manifest, dict) else None
if not isinstance(manifest_packages, list) or len(manifest_packages) != len(identity_packages):
    raise SecurityError("immutable Lake dependency identities disagree with lake-manifest")
manifest_by_name = {}
for value in manifest_packages:
    if not isinstance(value, dict) or value.get("type") != "git":
        raise SecurityError("exact-base lake-manifest contains a non-Git dependency")
    name, url, revision = value.get("name"), value.get("url"), value.get("rev")
    if (
        not isinstance(name, str)
        or re.fullmatch(r"[A-Za-z0-9_.-]+", name) is None
        or name in manifest_by_name
        or not isinstance(url, str)
        or not url
        or not isinstance(revision, str)
        or hex40.fullmatch(revision) is None
    ):
        raise SecurityError("exact-base lake-manifest dependency identity is invalid")
    manifest_by_name[name] = (url, revision)
identity_names = []
identity_keys = {
    "checkout_head", "checkout_tree", "expected_tree", "manifest_rev",
    "manifest_url", "name",
}
for value in identity_packages:
    if not isinstance(value, dict) or set(value) != identity_keys:
        raise SecurityError("immutable Lake dependency identity record has an invalid shape")
    name = value["name"]
    if name not in manifest_by_name or name in identity_names:
        raise SecurityError("immutable Lake dependency identity name is missing or duplicated")
    url, revision = manifest_by_name[name]
    if value["manifest_url"] != url or value["manifest_rev"] != revision:
        raise SecurityError(f"immutable Lake dependency identity disagrees with manifest: {name}")
    if value["checkout_head"] != revision:
        raise SecurityError(f"immutable Lake dependency checkout has the wrong revision: {name}")
    expected_tree = value["expected_tree"]
    if not isinstance(expected_tree, str) or hex40.fullmatch(expected_tree) is None:
        raise SecurityError(f"immutable Lake dependency expected tree is invalid: {name}")
    if value["checkout_tree"] != expected_tree:
        raise SecurityError(f"immutable Lake dependency checkout has the wrong tree: {name}")
    identity_names.append(name)
if identity_names != sorted(manifest_by_name):
    raise SecurityError("immutable Lake dependency identities are not canonical and complete")
package_entries = list(os.scandir(cache / "packages"))
if any(not entry.is_dir(follow_symlinks=False) or entry.is_symlink() for entry in package_entries):
    raise SecurityError("immutable Lake package root contains a non-directory entry")
if {entry.name for entry in package_entries} != set(manifest_by_name):
    raise SecurityError("immutable Lake package directories disagree with package identities")
PY
)

note "Immutable Lake cache fully rehashed and verified for $BASE_COMMIT."
