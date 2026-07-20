#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  printf 'Usage: %s [--source-root exact-base-checkout] [environment-file]\n' "${0##*/}"
}

source_override=
config_file=
while (( $# > 0 )); do
  case "$1" in
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

load_config "${config_file:-$SCRIPT_DIR/.env}"
require_command mktemp
require_command rmdir
[[ -n "${HARNESS_PI_PYTHON:-}" && -x "$HARNESS_PI_PYTHON" ]] ||
  die "the pinned Python executable is unavailable: ${HARNESS_PI_PYTHON:-unset}"
[[ -n "${HARNESS_PI_FLOCK:-}" && -x "$HARNESS_PI_FLOCK" ]] ||
  die "the pinned flock executable is unavailable: ${HARNESS_PI_FLOCK:-unset}"
[[ -x "$HARNESS_PI_GIT" && ! -L "$HARNESS_PI_GIT" ]] ||
  die "the pinned Git executable is unavailable: $HARNESS_PI_GIT"
ensure_runtime_layout
assert_deploy_code_committed
mkdir -p -- "$POINCARE_WORKTREE_ROOT"
[[ -O "$POINCARE_WORKTREE_ROOT" && -w "$POINCARE_WORKTREE_ROOT" ]] ||
  die "cache smoke worktree root must be owned and writable by the current user"

if [[ -n "$source_override" ]]; then
  [[ "$source_override" = /* ]] || die "--source-root must be absolute"
  SOURCE_ROOT=$(canonical_path "$source_override") || die "cannot resolve --source-root"
else
  SOURCE_ROOT=$POINCARE_REPO_ROOT
fi
readonly SOURCE_ROOT
[[ "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse --show-toplevel)" == "$SOURCE_ROOT" ]] ||
  die "cache smoke source does not match its Git top level"

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
  die "cache smoke source is not a worktree of the configured repository"

# Lean cache users hold this lock shared. Cache publication and completed-root
# builds hold the same descriptor exclusively, so a smoke can never cross an
# atomic publication or a mutable build interval.
exec 9>"$POINCARE_STATE_DIR/build-job.lock"
"$HARNESS_PI_FLOCK" --shared --nonblock 9 ||
  die "cache smoke is excluded by an active cache publication or root build"

readonly BASE_COMMIT=$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse HEAD)
readonly BASE_TREE=$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse 'HEAD^{tree}')
readonly CACHE_PATH="$POINCARE_PI_LAKE_CACHE_ROOT/$BASE_COMMIT"
readonly SMOKE_SOURCE="Poincare/Statement.lean"
readonly SMOKE_ID="$(date -u '+%Y%m%dT%H%M%SZ')-$$"
SCRATCH_PARENT=$(mktemp -d "$POINCARE_WORKTREE_ROOT/.cache-smoke.$BASE_COMMIT.XXXXXX") ||
  die "could not create cache-smoke scratch directory"
readonly SCRATCH_PARENT
readonly SMOKE_WORKTREE="$SCRATCH_PARENT/worktree"
readonly SMOKE_LOG="$POINCARE_DEPLOY_STATE_DIR/cache-sandbox-smoke-$BASE_COMMIT-$SMOKE_ID.log"
readonly PYTHON_CACHE="$POINCARE_DEPLOY_STATE_DIR/cache-sandbox-python-$BASE_COMMIT-$$"
mkdir -- "$PYTHON_CACHE"
chmod 700 -- "$PYTHON_CACHE"

smoke_complete=0
record_smoke_exit() {
  local status=$?
  if (( smoke_complete == 0 )); then
    append_event "$POINCARE_DEPLOY_STATE_DIR/events.jsonl" cache_sandbox_smoke_failed \
      base_commit "$BASE_COMMIT" exit_code "$status" scratch "${SCRATCH_PARENT##*/}" || true
  fi
}
trap record_smoke_exit EXIT

"$HARNESS_PI_GIT" -C "$SOURCE_ROOT" worktree add --detach \
  "$SMOKE_WORKTREE" "$BASE_COMMIT" \
  > "$SMOKE_LOG" 2>&1
[[ -z "$("$HARNESS_PI_GIT" -C "$SMOKE_WORKTREE" status --porcelain --untracked-files=all)" ]] ||
  die "fresh cache sandbox smoke worktree is unexpectedly dirty"

(
  cd "$POINCARE_DEPLOY_CODE_ROOT"
  PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
    PYTHONDONTWRITEBYTECODE=1 PYTHONPYCACHEPREFIX="$PYTHON_CACHE" \
    "$HARNESS_PI_PYTHON" -S -P -B - \
      "$POINCARE_DEPLOY_CODE_ROOT" "$SMOKE_WORKTREE" "$POINCARE_STATE_DIR" \
      "$POINCARE_PI_TOOLCHAIN_ROOT" "$CACHE_PATH" "$BASE_COMMIT" "$BASE_TREE" \
      "$SMOKE_SOURCE" "$HARNESS_PI_GIT" <<'PY'
import subprocess
import sys
from pathlib import Path

from harness.v2.pi.security import (
    SecurityError,
    audit_bubblewrap,
    bubblewrap_lean_argv,
    run_limited,
)

control, worktree, state, toolchain, cache = map(Path, sys.argv[1:6])
base_commit, base_tree, source, git_executable = sys.argv[6:10]
common_raw = subprocess.run(
    [git_executable, "-C", str(worktree), "rev-parse", "--git-common-dir"],
    check=True,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
).stdout.decode("utf-8").strip()
git_common = Path(common_raw)
if not git_common.is_absolute():
    git_common = worktree / git_common
git_common = git_common.resolve(strict=True)

spec = audit_bubblewrap(
    configured_path="/usr/bin/bwrap",
    control_root=control,
    worktree=worktree,
    forbidden_paths=(state, git_common),
    extra_toolchain_roots=str(toolchain),
    immutable_lake_cache=cache,
    base_commit=base_commit,
    base_tree=base_tree,
)
argv = bubblewrap_lean_argv(
    spec=spec,
    worktree=worktree,
    command=("env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", source),
)
result = run_limited(
    argv,
    cwd=worktree,
    env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"},
    timeout_seconds=600,
    output_limit_bytes=1024 * 1024,
    supervise_parent=True,
)
if result.returncode != 0 or result.timed_out or result.output_limited:
    error = result.stderr.decode("utf-8", "replace").strip()
    raise SecurityError(f"real immutable-cache Lean smoke failed: {error or result.returncode}")
PY
) >> "$SMOKE_LOG" 2>&1

[[ "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse HEAD)" == "$BASE_COMMIT" ]] ||
  die "cache smoke source HEAD changed during verification"
[[ "$("$HARNESS_PI_GIT" -C "$SOURCE_ROOT" rev-parse 'HEAD^{tree}')" == "$BASE_TREE" ]] ||
  die "cache smoke source tree changed during verification"
[[ -z "$("$HARNESS_PI_GIT" -C "$SMOKE_WORKTREE" status --porcelain --untracked-files=all)" ]] ||
  die "cache sandbox smoke changed its temporary worktree; it is preserved"
"$HARNESS_PI_GIT" -C "$SOURCE_ROOT" worktree remove "$SMOKE_WORKTREE" \
  >> "$SMOKE_LOG" 2>&1
rmdir -- "$SCRATCH_PARENT"

smoke_complete=1
append_event "$POINCARE_DEPLOY_STATE_DIR/events.jsonl" cache_sandbox_smoke_passed \
  base_commit "$BASE_COMMIT" source "$SMOKE_SOURCE" evidence "${SMOKE_LOG##*/}"
trap - EXIT
note "Immutable cache passed the exact Bubblewrap Lean smoke at $BASE_COMMIT."
