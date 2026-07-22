#!/usr/bin/env bash

# Shared helpers for the mj-zima Harness v2 launcher. This file is sourced by
# the executable scripts; it intentionally performs no work on its own.

set -euo pipefail

readonly POINCARE_CONTROL_SESSION="poincare-control"
readonly POINCARE_WORKERS_SESSION="poincare-workers"
readonly POINCARE_OBSERVE_SESSION="poincare-observe"
readonly POINCARE_HEARTBEAT_SECONDS=10800
readonly POINCARE_CODEX_REVIEW_RESERVE_SECONDS=3600
readonly POINCARE_MIN_CODEX_CYCLE_SECONDS=14400
if [[ "$(/usr/bin/uname -s)" == Linux ]]; then
  readonly HARNESS_PI_PYTHON=/usr/bin/python3
  readonly HARNESS_PI_FLOCK=/usr/bin/flock
else
  _harness_python=
  for _harness_candidate in /opt/homebrew/bin/python3 /usr/local/bin/python3 /usr/bin/python3; do
    if [[ -x "$_harness_candidate" ]]; then
      _harness_python=$_harness_candidate
      break
    fi
  done
  [[ -n "$_harness_python" ]] || {
    printf 'ERROR: a Python 3 interpreter is required\n' >&2
    return 1 2>/dev/null || exit 1
  }
  readonly HARNESS_PI_PYTHON=$("$_harness_python" -S -B -c \
    'import os,sys; print(os.path.realpath(sys.executable))')
  _harness_flock=
  for _harness_candidate in /opt/homebrew/bin/flock /usr/local/bin/flock /usr/bin/flock; do
    if [[ -x "$_harness_candidate" ]]; then
      _harness_flock=$("$HARNESS_PI_PYTHON" -S -B -c \
        'import os,sys; print(os.path.realpath(sys.argv[1]))' "$_harness_candidate")
      break
    fi
  done
  _harness_flock=${_harness_flock:-/usr/bin/flock}
  readonly HARNESS_PI_FLOCK=$_harness_flock
  unset _harness_flock
  unset _harness_candidate _harness_python
fi
export HARNESS_PI_PYTHON HARNESS_PI_FLOCK

deploy_dir() {
  CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd
}

die() {
  printf 'ERROR: %s\n' "$*" >&2
  exit 1
}

note() {
  printf '%s\n' "$*"
}

utc_now() {
  date -u '+%Y-%m-%dT%H:%M:%SZ'
}

monotonic_ns() {
  "$HARNESS_PI_PYTHON" -S -P -B -c 'import time; print(time.monotonic_ns())'
}

utc_from_epoch() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$1" <<'PY'
from datetime import datetime, timezone
import sys

print(datetime.fromtimestamp(int(sys.argv[1]), timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))
PY
}

seal_evidence_file() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$1" <<'PY'
import hashlib
import json
import os
import stat
import sys

path = os.path.abspath(sys.argv[1])
if os.path.realpath(path) != path:
    raise SystemExit("evidence path is not canonical")
flags = os.O_RDONLY
if hasattr(os, "O_NOFOLLOW"):
    flags |= os.O_NOFOLLOW
descriptor = os.open(path, flags)
try:
    before = os.fstat(descriptor)
    if not stat.S_ISREG(before.st_mode) or before.st_uid != os.geteuid():
        raise SystemExit("evidence is not a current-user-owned regular file")
    digest = hashlib.sha256()
    total = 0
    while True:
        chunk = os.read(descriptor, 1024 * 1024)
        if not chunk:
            break
        digest.update(chunk)
        total += len(chunk)
    after = os.fstat(descriptor)
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    ) or total != before.st_size:
        raise SystemExit("evidence changed while being hashed")
finally:
    os.close(descriptor)
os.chmod(path, 0o400, follow_symlinks=False)
directory = os.open(os.path.dirname(path), os.O_RDONLY)
try:
    os.fsync(directory)
finally:
    os.close(directory)
print(json.dumps({"sha256": digest.hexdigest(), "size_bytes": total}, sort_keys=True))
PY
}

heartbeat_timing_metrics() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$1" "$2" "$3" <<'PY'
import json
import sys

started, finished, interval = map(int, sys.argv[1:])
if started < 0 or finished < started or interval <= 0:
    raise SystemExit("invalid monotonic heartbeat timing")
deadline = started + interval
overrun = max(0, finished - deadline)
remaining = max(0, deadline - finished)
print(
    json.dumps(
        {
            "deadline_monotonic_ns": deadline,
            "duration_ns": finished - started,
            "overrun_ns": overrun,
            "remaining_ns": remaining,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
)
PY
}

canonical_path() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$1" <<'PY'
import os
import sys

print(os.path.realpath(sys.argv[1]))
PY
}

secure_config_payload() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$1" <<'PY'
import hashlib
import json
import os
import stat
import sys

raw = os.path.expanduser(sys.argv[1])
if not os.path.isabs(raw) or os.path.normpath(raw) != raw:
    raise SystemExit("configuration path must be an absolute normalized canonical path")
lexical = raw
if os.path.realpath(lexical) != lexical:
    raise SystemExit("configuration path is not canonical or has a symbolic-link ancestor")
try:
    before = os.lstat(lexical)
except OSError as exc:
    raise SystemExit(f"cannot inspect configuration: {exc}") from exc
if not stat.S_ISREG(before.st_mode) or stat.S_ISLNK(before.st_mode):
    raise SystemExit("configuration is not a regular non-symlink file")
if before.st_uid != os.geteuid():
    raise SystemExit("configuration is not owned by the current user")
mode = stat.S_IMODE(before.st_mode)
if mode not in {0o400, 0o600}:
    raise SystemExit(
        f"configuration mode must be 0400 or 0600 before sourcing, found {mode:04o}"
    )
flags = os.O_RDONLY
if hasattr(os, "O_NOFOLLOW"):
    flags |= os.O_NOFOLLOW
if hasattr(os, "O_CLOEXEC"):
    flags |= os.O_CLOEXEC
try:
    descriptor = os.open(lexical, flags)
except OSError as exc:
    raise SystemExit(f"cannot open configuration safely: {exc}") from exc
try:
    opened = os.fstat(descriptor)
    identity = (
        before.st_dev,
        before.st_ino,
        before.st_uid,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    opened_identity = (
        opened.st_dev,
        opened.st_ino,
        opened.st_uid,
        opened.st_mode,
        opened.st_size,
        opened.st_mtime_ns,
        opened.st_ctime_ns,
    )
    if opened_identity != identity:
        raise SystemExit("configuration changed while it was being opened")
    chunks = []
    total = 0
    while True:
        chunk = os.read(descriptor, 65536)
        if not chunk:
            break
        chunks.append(chunk)
        total += len(chunk)
        if total > 1024 * 1024:
            raise SystemExit("configuration exceeds the 1 MiB safety limit")
    after = os.fstat(descriptor)
    after_identity = (
        after.st_dev,
        after.st_ino,
        after.st_uid,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if after_identity != identity or total != opened.st_size:
        raise SystemExit("configuration changed while it was being read")
finally:
    os.close(descriptor)
data = b"".join(chunks)
if b"\0" in data:
    raise SystemExit("configuration contains a NUL byte")
try:
    text = data.decode("utf-8")
except UnicodeDecodeError as exc:
    raise SystemExit("configuration is not valid UTF-8") from exc
print(
    json.dumps(
        {
            "canonical_path": lexical,
            "sha256": hashlib.sha256(data).hexdigest(),
            "text": text,
        },
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )
)
PY
}

secure_sealed_input_payload() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$1" <<'PY'
import hashlib
import json
import os
import stat
import sys

raw = sys.argv[1]
if not os.path.isabs(raw) or os.path.normpath(raw) != raw or os.path.realpath(raw) != raw:
    raise SystemExit("sealed input path must be absolute, normalized, and canonical")
before = os.lstat(raw)
if (
    not stat.S_ISREG(before.st_mode)
    or stat.S_ISLNK(before.st_mode)
    or before.st_uid != os.geteuid()
    or stat.S_IMODE(before.st_mode) != 0o400
    or before.st_nlink != 1
):
    raise SystemExit("sealed input must be an owner-only 0400 regular file with one link")
flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
descriptor = os.open(raw, flags)
try:
    opened = os.fstat(descriptor)
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
    if identity != (
        opened.st_dev,
        opened.st_ino,
        opened.st_mode,
        opened.st_uid,
        opened.st_nlink,
        opened.st_size,
        opened.st_mtime_ns,
        opened.st_ctime_ns,
    ):
        raise SystemExit("sealed input changed while opening")
    digest = hashlib.sha256()
    total = 0
    while True:
        chunk = os.read(descriptor, 1024 * 1024)
        if not chunk:
            break
        digest.update(chunk)
        total += len(chunk)
        if total > 128 * 1024 * 1024:
            raise SystemExit("sealed input exceeds the 128 MiB bound")
    after = os.fstat(descriptor)
    if identity != (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_uid,
        after.st_nlink,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    ) or total != opened.st_size:
        raise SystemExit("sealed input changed while hashing")
finally:
    os.close(descriptor)
print(json.dumps({"canonical_path": raw, "sha256": digest.hexdigest(), "size_bytes": total}, sort_keys=True))
PY
}

secure_executable_payload() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$1" <<'PY'
import hashlib
import json
import os
import stat
import sys

raw = sys.argv[1]
if not os.path.isabs(raw) or os.path.normpath(raw) != raw or os.path.realpath(raw) != raw:
    raise SystemExit("executable path must be absolute, normalized, and canonical")
try:
    before = os.lstat(raw)
except OSError as exc:
    raise SystemExit(f"cannot inspect executable: {exc}") from exc
mode = stat.S_IMODE(before.st_mode)
if (
    not stat.S_ISREG(before.st_mode)
    or stat.S_ISLNK(before.st_mode)
    or before.st_uid not in {0, os.geteuid()}
    or mode & 0o022
    or not os.access(raw, os.X_OK)
):
    raise SystemExit(
        "executable must be a root-or-current-user-owned, non-writable, executable regular file"
    )
flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
try:
    descriptor = os.open(raw, flags)
except OSError as exc:
    raise SystemExit(f"cannot open executable safely: {exc}") from exc
try:
    opened = os.fstat(descriptor)
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
    if identity != (
        opened.st_dev,
        opened.st_ino,
        opened.st_mode,
        opened.st_uid,
        opened.st_nlink,
        opened.st_size,
        opened.st_mtime_ns,
        opened.st_ctime_ns,
    ):
        raise SystemExit("executable changed while opening")
    digest = hashlib.sha256()
    total = 0
    while True:
        chunk = os.read(descriptor, 1024 * 1024)
        if not chunk:
            break
        digest.update(chunk)
        total += len(chunk)
        if total > 256 * 1024 * 1024:
            raise SystemExit("executable exceeds the 256 MiB attestation bound")
    after = os.fstat(descriptor)
    if identity != (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_uid,
        after.st_nlink,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    ) or total != opened.st_size:
        raise SystemExit("executable changed while hashing")
finally:
    os.close(descriptor)
print(
    json.dumps(
        {"canonical_path": raw, "sha256": digest.hexdigest(), "size_bytes": total},
        sort_keys=True,
    )
)
PY
}

# Every deployment tmux operation resolves through this function. The configured
# absolute executable is re-attested before use so a writable PATH entry or
# post-preflight binary replacement cannot gain session authority.
tmux() {
  local payload current_sha256
  [[ "${HARNESS_PI_TMUX:-}" = /* && -n "${HARNESS_PI_TMUX_SHA256:-}" ]] ||
    die "tmux authority is not configured"
  if ! payload=$(secure_executable_payload "$HARNESS_PI_TMUX"); then
    die "configured tmux executable failed re-attestation"
  fi
  current_sha256=$(printf '%s' "$payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  [[ "$current_sha256" == "$HARNESS_PI_TMUX_SHA256" ]] ||
    die "configured tmux executable changed after attestation"
  "$HARNESS_PI_TMUX" "$@"
}

require_uint_range() {
  local name=$1
  local value=$2
  local minimum=$3
  local maximum=$4

  [[ "$value" =~ ^[0-9]+$ ]] || die "$name must be an integer"
  (( value >= minimum && value <= maximum )) ||
    die "$name must be between $minimum and $maximum"
}

load_config() {
  local config_file=${1:-"$(deploy_dir)/.env"}
  local config_payload config_contents

  set +e
  config_payload=$(secure_config_payload "$config_file")
  local config_status=$?
  set -e
  (( config_status == 0 )) ||
    die "configuration failed canonical ownership/mode validation: $config_file"
  POINCARE_CONFIG_FILE=$(printf '%s' "$config_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["canonical_path"])')
  POINCARE_CONFIG_SHA256=$(printf '%s' "$config_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  config_contents=$(printf '%s' "$config_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["text"], end="")')

  # The configuration is owner-managed shell syntax. It must never be copied
  # from an untrusted source or contain credentials. Source only the bytes read
  # through the validated regular-file descriptor above, not a path that can be
  # swapped between validation and evaluation.
  unset POINCARE_REPO_ROOT POINCARE_WORKTREE_ROOT POINCARE_CODEX_BIN
  unset POINCARE_PI_INSTALL_MANIFEST POINCARE_PI_DEPENDENCY_GRAPH
  unset POINCARE_PI_LAKE_CACHE_ROOT POINCARE_PI_TOOLCHAIN_ROOT POINCARE_EXTRA_PATH
  unset POINCARE_GIT_BIN POINCARE_TMUX_BIN
  unset POINCARE_INTEGRATION_BRANCH POINCARE_LEANSTRAL_BASE_URL
  unset POINCARE_LEANSTRAL_SERVED_MODEL POINCARE_LEANSTRAL_ARTIFACT
  unset POINCARE_LEANSTRAL_REVISION POINCARE_MAX_LEANSTRAL_JOBS
  unset POINCARE_INTEGRATION_BATCH_SIZE
  unset POINCARE_CYCLE_COOLDOWN_SECONDS POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS
  unset POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS POINCARE_EXACT_PROBE_TIMEOUT_SECONDS
  unset POINCARE_CODEX_MODEL POINCARE_CODEX_REASONING_EFFORT POINCARE_MIN_FREE_GIB
  set -a
  # shellcheck disable=SC1091
  source /dev/stdin <<< "$config_contents"
  set +a

  : "${POINCARE_REPO_ROOT:?set POINCARE_REPO_ROOT in the environment file}"
  : "${POINCARE_LEANSTRAL_BASE_URL:?set POINCARE_LEANSTRAL_BASE_URL in the environment file}"
  : "${POINCARE_LEANSTRAL_SERVED_MODEL:?set POINCARE_LEANSTRAL_SERVED_MODEL in the environment file}"
  : "${POINCARE_LEANSTRAL_ARTIFACT:?set POINCARE_LEANSTRAL_ARTIFACT in the environment file}"
  : "${POINCARE_LEANSTRAL_REVISION:?set POINCARE_LEANSTRAL_REVISION in the environment file}"
  : "${POINCARE_PI_INSTALL_MANIFEST:?set POINCARE_PI_INSTALL_MANIFEST in the environment file}"
  : "${POINCARE_PI_DEPENDENCY_GRAPH:?set POINCARE_PI_DEPENDENCY_GRAPH in the environment file}"
  : "${POINCARE_PI_LAKE_CACHE_ROOT:?set POINCARE_PI_LAKE_CACHE_ROOT in the environment file}"
  : "${POINCARE_PI_TOOLCHAIN_ROOT:?set POINCARE_PI_TOOLCHAIN_ROOT in the environment file}"
  : "${POINCARE_INTEGRATION_BRANCH:?set POINCARE_INTEGRATION_BRANCH explicitly in the environment file}"

  export PATH="${POINCARE_EXTRA_PATH:-${HOME}/.elan/bin:${HOME}/.local/bin:/usr/local/bin:/usr/bin:/bin}:${PATH}"
  POINCARE_WORKTREE_ROOT=${POINCARE_WORKTREE_ROOT:-/srv/projects/poincare-worktrees}
  POINCARE_CODEX_BIN=${POINCARE_CODEX_BIN:-"${HOME}/.local/bin/codex"}
  POINCARE_GIT_BIN=${POINCARE_GIT_BIN:-/usr/bin/git}
  POINCARE_TMUX_BIN=${POINCARE_TMUX_BIN:-/usr/bin/tmux}
  POINCARE_MAX_LEANSTRAL_JOBS=${POINCARE_MAX_LEANSTRAL_JOBS:-4}
  POINCARE_INTEGRATION_BATCH_SIZE=${POINCARE_INTEGRATION_BATCH_SIZE:-4}
  POINCARE_CYCLE_COOLDOWN_SECONDS=${POINCARE_CYCLE_COOLDOWN_SECONDS:-300}
  POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS=${POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS:-14400}
  POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS=${POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS:-21600}
  POINCARE_EXACT_PROBE_TIMEOUT_SECONDS=${POINCARE_EXACT_PROBE_TIMEOUT_SECONDS:-300}
  POINCARE_CODEX_MODEL=${POINCARE_CODEX_MODEL:-}
  POINCARE_CODEX_REASONING_EFFORT=${POINCARE_CODEX_REASONING_EFFORT:-xhigh}
  POINCARE_MIN_FREE_GIB=${POINCARE_MIN_FREE_GIB:-20}

  export POINCARE_WORKTREE_ROOT POINCARE_CODEX_BIN
  export POINCARE_GIT_BIN POINCARE_TMUX_BIN
  export POINCARE_PI_INSTALL_MANIFEST POINCARE_PI_DEPENDENCY_GRAPH
  export POINCARE_INTEGRATION_BRANCH
  export POINCARE_MAX_LEANSTRAL_JOBS POINCARE_INTEGRATION_BATCH_SIZE
  export POINCARE_CYCLE_COOLDOWN_SECONDS
  export POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS
  export POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS POINCARE_EXACT_PROBE_TIMEOUT_SECONDS
  export POINCARE_CODEX_MODEL POINCARE_CODEX_REASONING_EFFORT
  export POINCARE_MIN_FREE_GIB

  [[ "$POINCARE_REPO_ROOT" = /* ]] || die "POINCARE_REPO_ROOT must be absolute"
  [[ "$POINCARE_WORKTREE_ROOT" = /* ]] || die "POINCARE_WORKTREE_ROOT must be absolute"
  [[ "$POINCARE_CODEX_BIN" = /* ]] || die "POINCARE_CODEX_BIN must be absolute"
  [[ "$POINCARE_GIT_BIN" = /* ]] || die "POINCARE_GIT_BIN must be absolute"
  [[ "$POINCARE_TMUX_BIN" = /* ]] || die "POINCARE_TMUX_BIN must be absolute"
  [[ "$POINCARE_PI_INSTALL_MANIFEST" = /* ]] ||
    die "POINCARE_PI_INSTALL_MANIFEST must be absolute"
  [[ "$POINCARE_PI_DEPENDENCY_GRAPH" = /* ]] ||
    die "POINCARE_PI_DEPENDENCY_GRAPH must be absolute"
  [[ "$POINCARE_PI_LAKE_CACHE_ROOT" = /* ]] ||
    die "POINCARE_PI_LAKE_CACHE_ROOT must be absolute"
  [[ "$POINCARE_PI_TOOLCHAIN_ROOT" = /* ]] ||
    die "POINCARE_PI_TOOLCHAIN_ROOT must be absolute"
  [[ "$POINCARE_LEANSTRAL_BASE_URL" != *example.invalid* ]] ||
    die "replace the placeholder Leanstral endpoint"
  [[ "$POINCARE_LEANSTRAL_SERVED_MODEL" != replace-* ]] ||
    die "replace the placeholder served model ID"
  [[ "$POINCARE_LEANSTRAL_ARTIFACT" == "mistralai/Leanstral-1.5-119B-A6B" ]] ||
    die "POINCARE_LEANSTRAL_ARTIFACT must pin mistralai/Leanstral-1.5-119B-A6B"
  [[ "$POINCARE_LEANSTRAL_REVISION" =~ ^[0-9a-fA-F]{40}$ ]] ||
    die "POINCARE_LEANSTRAL_REVISION must be a 40-character git revision"
  [[ "$POINCARE_INTEGRATION_BRANCH" =~ ^[A-Za-z0-9._/-]+$ ]] ||
    die "POINCARE_INTEGRATION_BRANCH contains unsupported characters"
  [[ "$POINCARE_CODEX_REASONING_EFFORT" =~ ^(high|xhigh|max)$ ]] ||
    die "POINCARE_CODEX_REASONING_EFFORT must be high, xhigh, or max"

  require_uint_range POINCARE_MAX_LEANSTRAL_JOBS "$POINCARE_MAX_LEANSTRAL_JOBS" 1 4
  require_uint_range POINCARE_INTEGRATION_BATCH_SIZE \
    "$POINCARE_INTEGRATION_BATCH_SIZE" 1 4
  require_uint_range POINCARE_CYCLE_COOLDOWN_SECONDS "$POINCARE_CYCLE_COOLDOWN_SECONDS" 30 3600
  require_uint_range POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS \
    "$POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS" "$POINCARE_MIN_CODEX_CYCLE_SECONDS" 86400
  require_uint_range POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS \
    "$POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS" 1800 86400
  require_uint_range POINCARE_EXACT_PROBE_TIMEOUT_SECONDS \
    "$POINCARE_EXACT_PROBE_TIMEOUT_SECONDS" 30 1800
  require_uint_range POINCARE_MIN_FREE_GIB "$POINCARE_MIN_FREE_GIB" 1 1000

  POINCARE_REPO_ROOT=$(canonical_path "$POINCARE_REPO_ROOT")
  POINCARE_WORKTREE_ROOT=$(canonical_path "$POINCARE_WORKTREE_ROOT")
  POINCARE_PI_LAKE_CACHE_ROOT=$(canonical_path "$POINCARE_PI_LAKE_CACHE_ROOT")
  POINCARE_PI_TOOLCHAIN_ROOT=$(canonical_path "$POINCARE_PI_TOOLCHAIN_ROOT")
  local pi_manifest_payload pi_graph_payload git_payload tmux_payload
  set +e
  pi_manifest_payload=$(secure_sealed_input_payload "$POINCARE_PI_INSTALL_MANIFEST")
  local pi_manifest_status=$?
  pi_graph_payload=$(secure_sealed_input_payload "$POINCARE_PI_DEPENDENCY_GRAPH")
  local pi_graph_status=$?
  git_payload=$(secure_executable_payload "$POINCARE_GIT_BIN")
  local git_status=$?
  tmux_payload=$(secure_executable_payload "$POINCARE_TMUX_BIN")
  local tmux_status=$?
  set -e
  (( pi_manifest_status == 0 )) || die "Pi install manifest is not safely sealed"
  (( pi_graph_status == 0 )) || die "Pi dependency graph is not safely sealed"
  (( git_status == 0 )) || die "configured Git executable is not safely attested"
  (( tmux_status == 0 )) || die "configured tmux executable is not safely attested"
  POINCARE_PI_INSTALL_MANIFEST=$(printf '%s' "$pi_manifest_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["canonical_path"])')
  POINCARE_PI_INSTALL_MANIFEST_SHA256=$(printf '%s' "$pi_manifest_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  POINCARE_PI_DEPENDENCY_GRAPH=$(printf '%s' "$pi_graph_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["canonical_path"])')
  POINCARE_PI_DEPENDENCY_GRAPH_SHA256=$(printf '%s' "$pi_graph_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  export POINCARE_PI_INSTALL_MANIFEST POINCARE_PI_INSTALL_MANIFEST_SHA256
  export POINCARE_PI_DEPENDENCY_GRAPH POINCARE_PI_DEPENDENCY_GRAPH_SHA256
  HARNESS_PI_GIT=$(printf '%s' "$git_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["canonical_path"])')
  HARNESS_PI_GIT_SHA256=$(printf '%s' "$git_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  HARNESS_PI_TMUX=$(printf '%s' "$tmux_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["canonical_path"])')
  HARNESS_PI_TMUX_SHA256=$(printf '%s' "$tmux_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  export HARNESS_PI_GIT HARNESS_PI_GIT_SHA256 HARNESS_PI_TMUX HARNESS_PI_TMUX_SHA256
  POINCARE_DEPLOY_CODE_ROOT=$(canonical_path "$(deploy_dir)/../../..")
  [[ "$POINCARE_WORKTREE_ROOT" != / ]] || die "POINCARE_WORKTREE_ROOT cannot be /"
  [[ "$POINCARE_WORKTREE_ROOT" != "$HOME" ]] ||
    die "POINCARE_WORKTREE_ROOT cannot be the home directory"
  [[ "$POINCARE_WORKTREE_ROOT" != "$POINCARE_REPO_ROOT" ]] ||
    die "POINCARE_WORKTREE_ROOT must differ from the integration checkout"
  [[ "$POINCARE_PI_LAKE_CACHE_ROOT" != / ]] || die "POINCARE_PI_LAKE_CACHE_ROOT cannot be /"
  [[ "$POINCARE_PI_LAKE_CACHE_ROOT" != "$HOME" ]] ||
    die "POINCARE_PI_LAKE_CACHE_ROOT cannot be the home directory"
  [[ "$POINCARE_PI_LAKE_CACHE_ROOT" != "$POINCARE_REPO_ROOT" ]] ||
    die "POINCARE_PI_LAKE_CACHE_ROOT must differ from the integration checkout"
  [[ "$POINCARE_PI_LAKE_CACHE_ROOT" != "$POINCARE_WORKTREE_ROOT" ]] ||
    die "POINCARE_PI_LAKE_CACHE_ROOT must differ from the worktree root"
  [[ "$POINCARE_PI_TOOLCHAIN_ROOT" != / ]] ||
    die "POINCARE_PI_TOOLCHAIN_ROOT cannot be /"
  case "$POINCARE_PI_TOOLCHAIN_ROOT" in
    /usr|/home|/srv)
      die "POINCARE_PI_TOOLCHAIN_ROOT is overly broad"
      ;;
  esac
  case "$POINCARE_REPO_ROOT/" in
    "$POINCARE_WORKTREE_ROOT"/*)
      die "POINCARE_WORKTREE_ROOT cannot contain the integration checkout"
      ;;
  esac
  case "$POINCARE_WORKTREE_ROOT/" in
    "$POINCARE_REPO_ROOT"/*)
      die "POINCARE_WORKTREE_ROOT must be external to the integration checkout"
      ;;
  esac
  for protected_root in \
    "$POINCARE_REPO_ROOT" "$POINCARE_DEPLOY_CODE_ROOT" "$POINCARE_WORKTREE_ROOT"
  do
    case "$protected_root/" in
      "$POINCARE_PI_LAKE_CACHE_ROOT"/*)
        die "POINCARE_PI_LAKE_CACHE_ROOT cannot contain $protected_root"
        ;;
    esac
    case "$POINCARE_PI_LAKE_CACHE_ROOT/" in
      "$protected_root"/*)
        die "POINCARE_PI_LAKE_CACHE_ROOT must be external to $protected_root"
        ;;
    esac
    case "$protected_root/" in
      "$POINCARE_PI_TOOLCHAIN_ROOT"/*)
        die "POINCARE_PI_TOOLCHAIN_ROOT cannot contain $protected_root"
        ;;
    esac
    case "$POINCARE_PI_TOOLCHAIN_ROOT/" in
      "$protected_root"/*)
        die "POINCARE_PI_TOOLCHAIN_ROOT must be external to $protected_root"
        ;;
    esac
  done
  case "$POINCARE_PI_LAKE_CACHE_ROOT/" in
    "$POINCARE_PI_TOOLCHAIN_ROOT"/*)
      die "POINCARE_PI_TOOLCHAIN_ROOT cannot contain the Lake cache root"
      ;;
  esac
  case "$POINCARE_PI_TOOLCHAIN_ROOT/" in
    "$POINCARE_PI_LAKE_CACHE_ROOT"/*)
      die "POINCARE_PI_TOOLCHAIN_ROOT must be external to the Lake cache root"
      ;;
  esac

  if ! "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_LEANSTRAL_BASE_URL" <<'PY'
import sys
import urllib.parse

url = urllib.parse.urlsplit(sys.argv[1].rstrip("/"))
valid = (
    url.scheme in {"http", "https"}
    and bool(url.netloc)
    and url.username is None
    and url.password is None
    and not url.query
    and not url.fragment
    and url.path.rstrip("/").endswith("/v1")
)
raise SystemExit(0 if valid else 1)
PY
  then
    die "POINCARE_LEANSTRAL_BASE_URL must be a credential-free http(s) URL ending in /v1"
  fi

  POINCARE_STATE_DIR="$POINCARE_REPO_ROOT/harness/v2/state"
  POINCARE_DEPLOY_STATE_DIR="$POINCARE_STATE_DIR/deploy"
  POINCARE_PROMPT_FILE="$POINCARE_DEPLOY_CODE_ROOT/harness/v2/prompts/orchestrator.md"
  POINCARE_CYCLE_RESULT_SCHEMA="$POINCARE_DEPLOY_CODE_ROOT/harness/v2/prompts/cycle-result.schema.json"
  POINCARE_CONFIG_FINGERPRINT=$("$HARNESS_PI_PYTHON" -S -P -B - \
    "$POINCARE_CONFIG_FILE" "$POINCARE_CONFIG_SHA256" \
    "$POINCARE_REPO_ROOT" "$POINCARE_DEPLOY_CODE_ROOT" \
    "$POINCARE_WORKTREE_ROOT" "$POINCARE_CODEX_BIN" \
    "$HARNESS_PI_GIT" "$HARNESS_PI_GIT_SHA256" \
    "$HARNESS_PI_TMUX" "$HARNESS_PI_TMUX_SHA256" \
    "$POINCARE_PI_INSTALL_MANIFEST" "$POINCARE_PI_INSTALL_MANIFEST_SHA256" \
    "$POINCARE_PI_DEPENDENCY_GRAPH" "$POINCARE_PI_DEPENDENCY_GRAPH_SHA256" \
    "$POINCARE_INTEGRATION_BRANCH" \
    "$POINCARE_PI_LAKE_CACHE_ROOT" "$POINCARE_PI_TOOLCHAIN_ROOT" \
    "$POINCARE_LEANSTRAL_BASE_URL" "$POINCARE_LEANSTRAL_SERVED_MODEL" \
    "$POINCARE_LEANSTRAL_ARTIFACT" "$POINCARE_LEANSTRAL_REVISION" \
    "$POINCARE_MAX_LEANSTRAL_JOBS" "$POINCARE_INTEGRATION_BATCH_SIZE" \
    "$POINCARE_CYCLE_COOLDOWN_SECONDS" \
    "$POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS" \
    "$POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS" \
    "$POINCARE_EXACT_PROBE_TIMEOUT_SECONDS" "$POINCARE_CODEX_MODEL" \
    "$POINCARE_CODEX_REASONING_EFFORT" "$POINCARE_MIN_FREE_GIB" <<'PY'
import hashlib
import sys

digest = hashlib.sha256()
for value in sys.argv[1:]:
    digest.update(value.encode("utf-8"))
    digest.update(b"\0")
print(digest.hexdigest())
PY
  )
  POINCARE_SESSION_OWNER="poincare-harness-v2:$POINCARE_CONFIG_FINGERPRINT"

  LEANSTRAL_BASE_URL=$POINCARE_LEANSTRAL_BASE_URL
  LEANSTRAL_MODEL=$POINCARE_LEANSTRAL_SERVED_MODEL
  LEANSTRAL_MODEL_REVISION=$POINCARE_LEANSTRAL_REVISION
  HARNESS_PI_BWRAP=/usr/bin/bwrap
  HARNESS_PI_SYSTEMD_RUN=/usr/bin/systemd-run
  HARNESS_PI_LAKE_CACHE_ROOT=$POINCARE_PI_LAKE_CACHE_ROOT
  HARNESS_PI_TOOLCHAIN_ROOTS=$POINCARE_PI_TOOLCHAIN_ROOT
  export LEANSTRAL_BASE_URL LEANSTRAL_MODEL LEANSTRAL_MODEL_REVISION
  export HARNESS_PI_BWRAP HARNESS_PI_SYSTEMD_RUN
  export HARNESS_PI_LAKE_CACHE_ROOT HARNESS_PI_TOOLCHAIN_ROOTS

  export POINCARE_REPO_ROOT POINCARE_WORKTREE_ROOT
  export POINCARE_DEPLOY_CODE_ROOT
  export POINCARE_PI_LAKE_CACHE_ROOT POINCARE_PI_TOOLCHAIN_ROOT
  export POINCARE_STATE_DIR POINCARE_DEPLOY_STATE_DIR
  export POINCARE_PROMPT_FILE POINCARE_CYCLE_RESULT_SCHEMA
  export POINCARE_CONFIG_FILE POINCARE_CONFIG_SHA256
  export POINCARE_CONFIG_FINGERPRINT POINCARE_SESSION_OWNER
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || die "required command is missing: $1"
}

cache_publish_reexec_args() {
  local source_root=$1
  local provenance_file=$2
  local config_file=$3

  POINCARE_CACHE_PUBLISH_REEXEC_ARGS=()
  if [[ -n "$source_root" ]]; then
    POINCARE_CACHE_PUBLISH_REEXEC_ARGS+=(--source-root "$source_root")
  fi
  POINCARE_CACHE_PUBLISH_REEXEC_ARGS+=(--provenance "$provenance_file")
  POINCARE_CACHE_PUBLISH_REEXEC_ARGS+=("$config_file")
}

assert_committed_deploy_paths() {
  local label=$1
  shift
  local required=("$@")
  local relative
  [[ "$("$HARNESS_PI_GIT" -C "$POINCARE_DEPLOY_CODE_ROOT" rev-parse --show-toplevel)" == \
      "$POINCARE_DEPLOY_CODE_ROOT" ]] ||
    die "deployment scripts are not running from their Git checkout root"
  for relative in "${required[@]}"; do
    "$HARNESS_PI_GIT" -C "$POINCARE_DEPLOY_CODE_ROOT" ls-files --error-unmatch "$relative" \
      >/dev/null 2>&1 || die "$label input is not committed: $relative"
    [[ -f "$POINCARE_DEPLOY_CODE_ROOT/$relative" && \
       ! -L "$POINCARE_DEPLOY_CODE_ROOT/$relative" ]] ||
      die "$label input is not a regular file: $relative"
    [[ "$("$HARNESS_PI_GIT" -C "$POINCARE_DEPLOY_CODE_ROOT" hash-object --no-filters \
      "$POINCARE_DEPLOY_CODE_ROOT/$relative")" == \
      "$("$HARNESS_PI_GIT" -C "$POINCARE_DEPLOY_CODE_ROOT" rev-parse "HEAD:$relative")" ]] ||
      die "$label input bytes differ from committed HEAD: $relative"
  done
  [[ -z "$("$HARNESS_PI_GIT" -C "$POINCARE_DEPLOY_CODE_ROOT" status --porcelain \
    --untracked-files=all -- "${required[@]}")" ]] ||
    die "$label inputs differ from committed HEAD"
}

assert_deploy_code_committed() {
  local required=(
    harness/v2/pi/__init__.py
    harness/v2/pi/security.py
    harness/v2/deploy/common.sh
    harness/v2/deploy/record-lean-cache-provenance.sh
    harness/v2/deploy/publish-lean-cache.sh
    harness/v2/deploy/verify-lean-cache.sh
    harness/v2/deploy/cache-sandbox-smoke.sh
  )

  assert_committed_deploy_paths "deployment cache control" "${required[@]}"
}

assert_review_control_committed() {
  local required=(
    harness/v2/deploy/common.sh
    harness/v2/deploy/codex-cycle.sh
    harness/v2/deploy/focused_review.py
    harness/v2/deploy/review-job-focused.sh
    harness/v2/prompts/orchestrator.md
    harness/v2/prompts/cycle-result.schema.json
  )

  assert_committed_deploy_paths "focused review control" "${required[@]}"
}

ensure_runtime_layout() {
  umask 077
  "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_REPO_ROOT" "$POINCARE_STATE_DIR" <<'PY'
import os
import stat
import sys
from pathlib import Path

repo_raw, state_raw = sys.argv[1:]
repo = Path(repo_raw)
state = Path(state_raw)
if (
    not repo.is_absolute()
    or not state.is_absolute()
    or os.path.normpath(repo_raw) != repo_raw
    or os.path.normpath(state_raw) != state_raw
):
    raise SystemExit("repository and state paths must be absolute and normalized")
if repo.is_symlink() or repo.resolve(strict=True) != repo:
    raise SystemExit("repository root must be canonical and symlink-free")
if state != repo / "harness/v2/state":
    raise SystemExit("runtime state must be the canonical ignored Harness path")

flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
uid = os.geteuid()

def ensure(parts: tuple[str, ...]) -> None:
    descriptor = os.open(repo, flags)
    try:
        for index, part in enumerate(parts):
            try:
                child = os.open(part, flags, dir_fd=descriptor)
            except FileNotFoundError:
                os.mkdir(part, 0o700, dir_fd=descriptor)
                os.fsync(descriptor)
                child = os.open(part, flags, dir_fd=descriptor)
            info = os.fstat(child)
            if not stat.S_ISDIR(info.st_mode) or info.st_uid != uid:
                os.close(child)
                raise SystemExit(f"runtime path component is not an owned real directory: {part}")
            if index >= 2 and info.st_mode & 0o022:
                os.close(child)
                raise SystemExit(f"runtime directory is group/world writable: {part}")
            os.close(descriptor)
            descriptor = child
    finally:
        os.close(descriptor)

for relative in (
    ("harness", "v2", "state", "execution-locks"),
    ("harness", "v2", "state", "deploy"),
    ("harness", "v2", "state", "deploy", "control", "cycles"),
    ("harness", "v2", "state", "deploy", "control", "completions"),
    ("harness", "v2", "state", "deploy", "workers", "supervisors"),
    ("harness", "v2", "state", "deploy", "workers", "staging"),
    ("harness", "v2", "state", "deploy", "workers", "slots"),
    ("harness", "v2", "state", "deploy", "observe"),
    ("harness", "v2", "state", "deploy", "observe", "snapshots"),
):
    ensure(relative)

def ensure_lock(relative_directory: tuple[str, ...], name: str) -> None:
    descriptor = os.open(repo, flags)
    try:
        for part in relative_directory:
            child = os.open(part, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        lock_flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_CLOEXEC", 0)
        lock_flags |= getattr(os, "O_NOFOLLOW", 0)
        lock_descriptor = os.open(name, lock_flags, 0o600, dir_fd=descriptor)
        try:
            info = os.fstat(lock_descriptor)
            if (
                not stat.S_ISREG(info.st_mode)
                or info.st_uid != uid
                or stat.S_IMODE(info.st_mode) != 0o600
                or info.st_nlink != 1
            ):
                raise SystemExit(f"runtime lock is not an owned 0600 single-link file: {name}")
        finally:
            os.close(lock_descriptor)
    finally:
        os.close(descriptor)

ensure_lock(("harness", "v2", "state", "deploy"), "lifecycle.lock")
ensure_lock(
    ("harness", "v2", "state", "deploy", "control"),
    "codex-cycle.lock",
)
ensure_lock(
    ("harness", "v2", "state", "deploy", "workers"),
    "worker-plane.lock",
)
ensure_lock(
    ("harness", "v2", "state", "deploy", "observe"),
    "heartbeat-loop.lock",
)
for slot in range(1, 5):
    ensure_lock(
        ("harness", "v2", "state", "deploy", "workers", "slots"),
        f"slot-{slot}.lock",
    )
PY
}

job_execution_lock_path() {
  local job_id=$1
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$POINCARE_STATE_DIR/execution-locks" "$job_id" <<'PY'
import os
import re
import stat
import sys
from pathlib import Path

root_raw, job_id = sys.argv[1:]
if re.fullmatch(r"[a-z0-9][a-z0-9._-]{2,119}", job_id) is None:
    raise SystemExit("invalid Job ID for execution lock")
root = Path(root_raw)
if not root.is_absolute() or os.path.normpath(root_raw) != root_raw:
    raise SystemExit("execution-lock root must be absolute and normalized")
if root.is_symlink() or root.resolve(strict=True) != root:
    raise SystemExit("execution-lock root must be canonical and symlink-free")
root_info = root.stat()
if (
    not stat.S_ISDIR(root_info.st_mode)
    or root_info.st_uid != os.geteuid()
    or stat.S_IMODE(root_info.st_mode) & 0o077
):
    raise SystemExit("execution-lock root must be an owner-only owned directory")
directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
directory = os.open(root, directory_flags)
try:
    name = f"{job_id}.lock"
    lock_flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_CLOEXEC", 0)
    lock_flags |= getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(name, lock_flags, 0o600, dir_fd=directory)
    try:
        opened = os.fstat(descriptor)
        linked = os.stat(name, dir_fd=directory, follow_symlinks=False)
        if (
            not stat.S_ISREG(opened.st_mode)
            or not stat.S_ISREG(linked.st_mode)
            or opened.st_uid != os.geteuid()
            or stat.S_IMODE(opened.st_mode) != 0o600
            or opened.st_nlink != 1
            or (opened.st_dev, opened.st_ino) != (linked.st_dev, linked.st_ino)
        ):
            raise SystemExit("execution lock must be an owned 0600 single-link file")
    finally:
        os.close(descriptor)
finally:
    os.close(directory)
print(root / f"{job_id}.lock")
PY
}

append_event() {
  local output_file=$1
  local event_name=$2
  shift 2

  (( $# % 2 == 0 )) || die "append_event requires key/value pairs"
  "$HARNESS_PI_PYTHON" -S -P -B - "$output_file" "$(utc_now)" "$event_name" "$@" <<'PY'
import json
import os
import sys

path, timestamp, event, *items = sys.argv[1:]
payload = {"timestamp": timestamp, "event": event}
for index in range(0, len(items), 2):
    payload[items[index]] = items[index + 1]
line = json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
fd = os.open(path, os.O_APPEND | os.O_CREAT | os.O_WRONLY, 0o600)
try:
    os.write(fd, line.encode("utf-8"))
finally:
    os.close(fd)
PY
}

session_exists() {
  tmux has-session -t "=$1" 2>/dev/null
}

session_id_exact() {
  local wanted=$1
  local name id

  while IFS='|' read -r name id; do
    if [[ "$name" == "$wanted" ]]; then
      printf '%s\n' "$id"
      return 0
    fi
  done < <(tmux list-sessions -F '#{session_name}|#{session_id}' 2>/dev/null || true)
  return 1
}

session_marker() {
  local id
  id=$(session_id_exact "$1") || return 0
  tmux show-options -v -t "$id" @poincare_harness_owner 2>/dev/null || true
}

expected_session_role() {
  case "$1" in
    "$POINCARE_CONTROL_SESSION") printf 'control\n' ;;
    "$POINCARE_WORKERS_SESSION") printf 'workers\n' ;;
    "$POINCARE_OBSERVE_SESSION") printf 'observe\n' ;;
    *) return 1 ;;
  esac
}

expected_session_program() {
  case "$1" in
    "$POINCARE_CONTROL_SESSION") printf '%s/codex-cycle.sh\n' "$(deploy_dir)" ;;
    "$POINCARE_WORKERS_SESSION") printf '%s/worker-plane.sh\n' "$(deploy_dir)" ;;
    "$POINCARE_OBSERVE_SESSION") printf '%s/heartbeat-loop.sh\n' "$(deploy_dir)" ;;
    *) return 1 ;;
  esac
}

expected_session_command() {
  local program
  program=$(expected_session_program "$1") || return 1
  shell_join "$program" "$POINCARE_CONFIG_FILE"
  printf '%s\n' "$REPLY"
}

bootstrap_session_command() {
  printf 'while :; do sleep 3600; done\n'
}

normalize_tmux_start_command() {
  REPLY=$1
  if [[ "$REPLY" == \"*\" ]]; then
    REPLY=${REPLY#\"}
    REPLY=${REPLY%\"}
  fi
}

session_id_matches_static_identity() {
  local id=$1
  local expected_name=$2
  local actual_name owner role expected_role base_pane

  actual_name=$(tmux display-message -p -t "$id" '#{session_name}' 2>/dev/null) || return 1
  [[ "$actual_name" == "$expected_name" ]] || return 1
  owner=$(tmux show-options -v -t "$id" @poincare_harness_owner 2>/dev/null) || return 1
  [[ "$owner" == "$POINCARE_SESSION_OWNER" ]] || return 1
  role=$(tmux show-options -v -t "$id" @poincare_harness_role 2>/dev/null) || return 1
  expected_role=$(expected_session_role "$expected_name") || return 1
  [[ "$role" == "$expected_role" ]] || return 1
  base_pane=$(tmux show-options -v -t "$id" @poincare_harness_base_pane 2>/dev/null) || return 1
  [[ -n "$base_pane" ]] || return 1
  [[ "$(tmux display-message -p -t "$base_pane" '#{session_id}' 2>/dev/null)" == "$id" ]] ||
    return 1
}

session_id_program_is_live() {
  local id=$1
  local expected_name=$2
  local base_pane start_command expected_command pane_dead

  session_id_matches_static_identity "$id" "$expected_name" || return 1
  base_pane=$(tmux show-options -v -t "$id" @poincare_harness_base_pane 2>/dev/null) || return 1
  start_command=$(tmux display-message -p -t "$base_pane" '#{pane_start_command}' 2>/dev/null) || return 1
  normalize_tmux_start_command "$start_command"
  start_command=$REPLY
  expected_command=$(expected_session_command "$expected_name") || return 1
  [[ "$start_command" == "$expected_command" ]] || return 1
  pane_dead=$(tmux display-message -p -t "$base_pane" '#{pane_dead}' 2>/dev/null) || return 1
  [[ "$pane_dead" == 0 ]]
}

session_id_is_owned() {
  local id=$1
  local expected_name=$2
  local lifecycle_state

  session_id_matches_static_identity "$id" "$expected_name" || return 1
  lifecycle_state=$(tmux show-options -v -t "$id" @poincare_harness_state 2>/dev/null) || return 1
  [[ "$lifecycle_state" == running ]] || return 1
  local base_pane start_command expected_command
  base_pane=$(tmux show-options -v -t "$id" @poincare_harness_base_pane 2>/dev/null) || return 1
  start_command=$(tmux display-message -p -t "$base_pane" '#{pane_start_command}' 2>/dev/null) || return 1
  normalize_tmux_start_command "$start_command"
  start_command=$REPLY
  expected_command=$(expected_session_command "$expected_name") || return 1
  [[ "$start_command" == "$expected_command" ]]
}

session_id_is_bootstrap_owned() {
  local id=$1
  local expected_name=$2
  local lifecycle_state base_pane start_command expected_command bootstrap_command

  session_id_matches_static_identity "$id" "$expected_name" || return 1
  lifecycle_state=$(tmux show-options -v -t "$id" @poincare_harness_state 2>/dev/null) || return 1
  [[ "$lifecycle_state" == bootstrap ]] || return 1
  base_pane=$(tmux show-options -v -t "$id" @poincare_harness_base_pane 2>/dev/null) || return 1
  start_command=$(tmux display-message -p -t "$base_pane" '#{pane_start_command}' 2>/dev/null) || return 1
  normalize_tmux_start_command "$start_command"
  start_command=$REPLY
  expected_command=$(expected_session_command "$expected_name") || return 1
  bootstrap_command=$(bootstrap_session_command)
  [[ "$start_command" == "$bootstrap_command" || "$start_command" == "$expected_command" ]]
}

session_id_is_owned_or_bootstrap() {
  session_id_is_owned "$1" "$2" || session_id_is_bootstrap_owned "$1" "$2"
}

session_is_owned() {
  local session=$1
  local id
  id=$(session_id_exact "$session") || return 1
  session_id_is_owned "$id" "$session"
}

session_is_bootstrap_owned() {
  local session=$1
  local id
  id=$(session_id_exact "$session") || return 1
  session_id_is_bootstrap_owned "$id" "$session"
}

session_id_is_live_owned() {
  local id=$1
  local expected_name=$2
  local base_pane pane_dead

  session_id_is_owned "$id" "$expected_name" || return 1
  base_pane=$(tmux show-options -v -t "$id" @poincare_harness_base_pane 2>/dev/null) || return 1
  pane_dead=$(tmux display-message -p -t "$base_pane" '#{pane_dead}' 2>/dev/null) || return 1
  [[ "$pane_dead" == 0 ]]
}

session_is_live_owned() {
  local session=$1
  local id
  id=$(session_id_exact "$session") || return 1
  session_id_is_live_owned "$id" "$session"
}

start_or_recover_session() {
  local session=$1
  local window_name=$2
  local program=$3
  local command session_id pane_id role start_command pane_dead bootstrap_command

  shell_join "$program" "$POINCARE_CONFIG_FILE"
  command=$REPLY

  if session_is_owned "$session"; then
    if session_is_live_owned "$session"; then
      note "$session is already running and owned by this Harness; preserving it."
      return 0
    fi
    session_id=$(session_id_exact "$session") ||
      die "owned tmux session disappeared during recovery: $session"
    pane_id=$(tmux show-options -v -t "$session_id" @poincare_harness_base_pane) ||
      die "owned tmux session lost its base pane: $session"
    tmux set-option -t "$session_id" @poincare_harness_state bootstrap
    tmux set-window-option -t "$pane_id" remain-on-exit off
    tmux respawn-pane -k -t "$pane_id" "$command"
    session_id_program_is_live "$session_id" "$session" ||
      die "could not recover the stopped owned session $session"
    tmux set-option -t "$session_id" @poincare_harness_state running
    session_id_is_live_owned "$session_id" "$session" ||
      die "recovered session failed final ownership validation: $session"
    note "restarted stopped owned session $session ($window_name)"
    return 0
  fi

  if session_is_bootstrap_owned "$session"; then
    session_id=$(session_id_exact "$session") ||
      die "bootstrap tmux session disappeared during recovery: $session"
    pane_id=$(tmux show-options -v -t "$session_id" @poincare_harness_base_pane) ||
      die "bootstrap tmux session lost its base pane: $session"
    start_command=$(tmux display-message -p -t "$pane_id" '#{pane_start_command}' 2>/dev/null) ||
      die "bootstrap tmux session lost its start command: $session"
    normalize_tmux_start_command "$start_command"
    start_command=$REPLY
    pane_dead=$(tmux display-message -p -t "$pane_id" '#{pane_dead}' 2>/dev/null) ||
      die "bootstrap tmux session lost its pane state: $session"
    if [[ "$start_command" == "$command" && "$pane_dead" == 0 ]]; then
      tmux set-option -t "$session_id" @poincare_harness_state running
    else
      tmux set-window-option -t "$pane_id" remain-on-exit off
      tmux respawn-pane -k -t "$pane_id" "$command"
      session_id_program_is_live "$session_id" "$session" ||
        die "could not respawn authenticated bootstrap session $session"
      tmux set-option -t "$session_id" @poincare_harness_state running
    fi
    session_id_is_live_owned "$session_id" "$session" ||
      die "authenticated bootstrap recovery failed final validation: $session"
    note "recovered authenticated bootstrap session $session ($window_name)"
    return 0
  fi

  session_exists "$session" &&
    die "tmux session '$session' exists without recoverable Harness identity"

  role=$(expected_session_role "$session") || die "unknown Harness session: $session"
  bootstrap_command=$(bootstrap_session_command)
  tmux new-session -d -s "$session" -c "$POINCARE_REPO_ROOT" "$bootstrap_command"
  session_id=$(session_id_exact "$session") ||
    die "tmux did not retain the newly created session $session"
  pane_id=$(tmux list-panes -t "$session_id" -F '#{pane_id}' | head -n 1)
  [[ -n "$pane_id" ]] || die "could not identify the bootstrap pane for $session"
  tmux set-option -t "$session_id" @poincare_harness_owner "$POINCARE_SESSION_OWNER"
  tmux set-option -t "$session_id" @poincare_harness_role "$role"
  tmux set-option -t "$session_id" @poincare_harness_base_pane "$pane_id"
  tmux set-option -t "$session_id" @poincare_harness_state bootstrap
  session_id_is_bootstrap_owned "$session_id" "$session" ||
    die "could not establish authenticated bootstrap identity for $session"
  tmux set-window-option -t "$pane_id" remain-on-exit off
  tmux rename-window -t "$pane_id" "$window_name"
  tmux respawn-pane -k -t "$pane_id" "$command"
  session_id_program_is_live "$session_id" "$session" ||
    die "created $session but its expected program is not live"
  tmux set-option -t "$session_id" @poincare_harness_state running
  session_id_is_live_owned "$session_id" "$session" ||
    die "created $session but could not establish its running Harness identity"
  note "started $session ($window_name)"
}

write_desired_state() {
  local desired=$1
  local path="$POINCARE_DEPLOY_STATE_DIR/desired-state.json"
  [[ "$desired" == running || "$desired" == stopped ]] || die "invalid desired state: $desired"
  "$HARNESS_PI_PYTHON" -S -P -B - "$path" "$desired" "$POINCARE_CONFIG_FINGERPRINT" "$(utc_now)" <<'PY'
import json
import os
import sys

path, desired, fingerprint, timestamp = sys.argv[1:]
temporary = f"{path}.tmp.{os.getpid()}"
with open(temporary, "x", encoding="utf-8") as handle:
    json.dump(
        {"desired": desired, "config_fingerprint": fingerprint, "updated_at": timestamp},
        handle,
        sort_keys=True,
        separators=(",", ":"),
    )
    handle.write("\n")
os.replace(temporary, path)
PY
}

runtime_cli() {
  (
    cd "$POINCARE_REPO_ROOT"
    /usr/bin/env -i \
      HOME="$HOME" LANG="${LANG:-C.UTF-8}" PATH=/usr/bin:/bin \
      PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 \
      PYTHONDONTWRITEBYTECODE=1 \
      HARNESS_PI_GIT="$HARNESS_PI_GIT" \
      HARNESS_PI_GIT_SHA256="$HARNESS_PI_GIT_SHA256" \
      "$HARNESS_PI_PYTHON" -S -P -B -m harness.v2.runtime \
      --state-dir "$POINCARE_STATE_DIR" "$@"
  )
}

set_deployment_desired_state() {
  local desired=$1
  local actor=$2
  [[ "$desired" == running || "$desired" == stopped ]] ||
    die "invalid desired state: $desired"
  [[ -n "$actor" && "$actor" != *$'\n'* && "$actor" != *$'\t'* ]] ||
    die "invalid desired-state actor"
  runtime_cli dispatch set "$desired" --actor "$actor" >/dev/null ||
    die "could not set the durable SQLite dispatch state to $desired"
  write_desired_state "$desired"
}

deployment_dispatch_state() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_STATE_DIR/harness.sqlite3" <<'PY'
import sqlite3
import sys

try:
    connection = sqlite3.connect(f"file:{sys.argv[1]}?mode=ro", uri=True, timeout=5)
    row = connection.execute(
        "SELECT desired_state FROM dispatch_control WHERE singleton = 1"
    ).fetchone()
except (OSError, sqlite3.Error):
    raise SystemExit(2)
finally:
    if "connection" in locals():
        connection.close()
if row is None or row[0] not in {"running", "stopped"}:
    raise SystemExit(2)
print(row[0])
PY
}

deployment_stop_requested() {
  local state
  set +e
  state=$(deployment_dispatch_state)
  local status=$?
  set -e
  if (( status != 0 )); then
    printf 'ERROR: durable dispatch state is unreadable; treating deployment as stopped\n' >&2
    return 0
  fi
  [[ "$state" == stopped ]]
}

active_job_count() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_STATE_DIR/harness.sqlite3" <<'PY'
import sqlite3
import sys

try:
    connection = sqlite3.connect(f"file:{sys.argv[1]}?mode=ro", uri=True)
    row = connection.execute(
        "SELECT COUNT(*) FROM jobs WHERE state IN ('preparing','running','reviewing')"
    ).fetchone()
except (OSError, sqlite3.Error):
    raise SystemExit(2)
finally:
    if "connection" in locals():
        connection.close()
print(row[0])
PY
}

job_pipeline_counts() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_STATE_DIR/harness.sqlite3" <<'PY'
import json
import sqlite3
import sys

states = ("queued", "preparing", "running", "reviewing")
try:
    connection = sqlite3.connect(f"file:{sys.argv[1]}?mode=ro", uri=True, timeout=5)
    rows = connection.execute(
        "SELECT state, COUNT(*) FROM jobs "
        "WHERE state IN ('queued','preparing','running','reviewing') GROUP BY state"
    ).fetchall()
except (OSError, sqlite3.Error):
    raise SystemExit(2)
finally:
    if "connection" in locals():
        connection.close()
counts = {state: 0 for state in states}
counts.update({state: int(count) for state, count in rows})
counts["executing"] = counts["preparing"] + counts["running"]
print(json.dumps(counts, sort_keys=True, separators=(",", ":")))
PY
}

queued_job_count() {
  job_pipeline_counts | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["queued"])'
}

active_job_rows() {
  "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_STATE_DIR/harness.sqlite3" <<'PY'
import re
import sqlite3
import sys

try:
    connection = sqlite3.connect(f"file:{sys.argv[1]}?mode=ro", uri=True, timeout=5)
    connection.row_factory = sqlite3.Row
    rows = connection.execute(
        """
        SELECT job_id, state, lease_owner, lease_generation
        FROM jobs
        WHERE state IN ('preparing', 'running', 'reviewing')
        ORDER BY created_at, job_id
        """
    ).fetchall()
except (OSError, sqlite3.Error):
    raise SystemExit(2)
finally:
    if "connection" in locals():
        connection.close()
for row in rows:
    values = (
        row["job_id"],
        row["state"],
        row["lease_owner"] or "",
        str(int(row["lease_generation"] or 0)),
    )
    if re.fullmatch(r"[a-z0-9][a-z0-9._-]{2,119}", values[0]) is None:
        raise SystemExit("runtime contains an unsafe Job ID")
    if any("\t" in value or "\n" in value for value in values):
        raise SystemExit("runtime contains an unsafe active Job field")
    print("\t".join(values))
PY
}

job_runtime_state() {
  local job_id=$1
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$POINCARE_STATE_DIR/harness.sqlite3" "$job_id" <<'PY'
import sqlite3
import sys

try:
    connection = sqlite3.connect(f"file:{sys.argv[1]}?mode=ro", uri=True, timeout=5)
    row = connection.execute("SELECT state FROM jobs WHERE job_id = ?", (sys.argv[2],)).fetchone()
except (OSError, sqlite3.Error):
    raise SystemExit(2)
finally:
    if "connection" in locals():
        connection.close()
if row is None:
    raise SystemExit(2)
print(row[0])
PY
}

job_supervisor_report() {
  local proc_root=${1:-/proc}
  local max_jobs=${POINCARE_MAX_LEANSTRAL_JOBS:-4}
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$POINCARE_STATE_DIR/harness.sqlite3" \
    "$POINCARE_DEPLOY_STATE_DIR/workers/supervisors" \
    "$POINCARE_CONFIG_FINGERPRINT" "$proc_root" "$max_jobs" <<'PY'
import json
import os
import re
import sqlite3
import stat
import sys
import time
from pathlib import Path

database = Path(sys.argv[1]).absolute()
supervisor_root = Path(sys.argv[2]).absolute()
fingerprint = sys.argv[3]
proc_root = Path(sys.argv[4]).absolute()
max_jobs = int(sys.argv[5])
anomalies = []


def anomaly(code: str, **details: object) -> None:
    anomalies.append({"code": code, **details})


def safe_record(path: Path, expected_mode: int) -> dict | None:
    if path.is_symlink() or not path.is_file():
        anomaly("record_missing_or_redirected", path=str(path))
        return None
    metadata = path.stat()
    if metadata.st_uid != os.geteuid() or stat.S_IMODE(metadata.st_mode) != expected_mode:
        anomaly(
            "record_ownership_or_mode_invalid",
            path=str(path),
            mode=f"{stat.S_IMODE(metadata.st_mode):04o}",
        )
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        anomaly("record_invalid_json", path=str(path), error=str(exc))
        return None
    if not isinstance(value, dict):
        anomaly("record_not_object", path=str(path))
        return None
    return value


def process_identity(pid: int) -> dict | None:
    try:
        raw = (proc_root / str(pid) / "stat").read_text(encoding="utf-8")
    except OSError:
        return None
    close = raw.rfind(")")
    if close < 0:
        return None
    fields = raw[close + 2 :].split()
    if len(fields) < 20:
        return None
    try:
        return {
            "state": fields[0],
            "ppid": int(fields[1]),
            "pgid": int(fields[2]),
            "sid": int(fields[3]),
            "start_ticks": int(fields[19]),
        }
    except ValueError:
        return None


try:
    boot_id = (proc_root / "sys/kernel/random/boot_id").read_text(encoding="ascii").strip()
except OSError:
    boot_id = ""
if not re.fullmatch(r"[0-9a-fA-F-]{36}", boot_id):
    anomaly("proc_boot_id_unavailable", proc_root=str(proc_root))

group_members: dict[int, list[int]] = {}
try:
    proc_entries = list(proc_root.iterdir())
except OSError as exc:
    proc_entries = []
    anomaly("proc_unreadable", error=str(exc))
for entry in proc_entries:
    if not entry.name.isdecimal():
        continue
    identity = process_identity(int(entry.name))
    if identity is None or identity["state"] in {"Z", "X"}:
        continue
    group_members.setdefault(identity["pgid"], []).append(int(entry.name))

active_jobs: dict[str, dict] = {}
try:
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True, timeout=5)
    connection.row_factory = sqlite3.Row
    rows = connection.execute(
        """
        SELECT job_id, state, lease_owner, lease_generation, lease_expires_at
        FROM jobs
        WHERE state IN ('preparing','running','reviewing')
        ORDER BY job_id
        """
    ).fetchall()
    connection.close()
    for row in rows:
        active_jobs[row["job_id"]] = {
            "job_id": row["job_id"],
            "state": row["state"],
            "lease_owner": row["lease_owner"],
            "lease_token": int(row["lease_generation"] or 0),
            "lease_expires_at": row["lease_expires_at"],
            "lease_active": bool(
                row["lease_expires_at"] is not None and row["lease_expires_at"] > time.time()
            ),
        }
except (OSError, sqlite3.Error) as exc:
    anomaly("runtime_database_unreadable", error=str(exc))

records: dict[str, dict] = {}
if supervisor_root.is_symlink() or not supervisor_root.is_dir():
    anomaly("supervisor_root_missing_or_redirected", path=str(supervisor_root))
else:
    root_metadata = supervisor_root.stat()
    if root_metadata.st_uid != os.geteuid() or stat.S_IMODE(root_metadata.st_mode) & 0o077:
        anomaly(
            "supervisor_root_ownership_or_mode_invalid",
            path=str(supervisor_root),
            mode=f"{stat.S_IMODE(root_metadata.st_mode):04o}",
        )
    for directory in sorted(supervisor_root.iterdir(), key=lambda item: item.name):
        if directory.is_symlink() or not directory.is_dir():
            anomaly("supervisor_entry_not_directory", path=str(directory))
            continue
        if re.fullmatch(r"[a-z0-9][a-z0-9._-]{2,119}", directory.name) is None:
            anomaly("supervisor_directory_job_id_invalid", path=str(directory))
            continue
        launch_path = directory / "launch.json"
        launch = safe_record(launch_path, 0o400)
        if launch is None:
            continue
        required_launch = {
            "schema_version",
            "job_id",
            "lease_owner",
            "lease_token",
            "supervisor_pid",
            "supervisor_start_ticks",
            "process_group_id",
            "session_id",
            "boot_id",
            "config_fingerprint",
            "started_at",
            "argv",
            "cwd",
        }
        version = launch.get("schema_version")
        if version == "poincare.job-supervisor.v2":
            required_launch.add("capacity_slot")
        elif version != "poincare.job-supervisor.v1":
            anomaly("supervisor_launch_shape_invalid", job_id=directory.name)
            continue
        if set(launch) != required_launch:
            anomaly("supervisor_launch_shape_invalid", job_id=directory.name)
            continue
        job_id = launch.get("job_id")
        if job_id != directory.name or job_id in records:
            anomaly("supervisor_job_identity_invalid", job_id=directory.name)
            continue
        integer_fields = [
            "lease_token",
            "supervisor_pid",
            "supervisor_start_ticks",
            "process_group_id",
            "session_id",
        ]
        if version == "poincare.job-supervisor.v2":
            integer_fields.append("capacity_slot")
        if any(
            isinstance(launch.get(name), bool)
            or not isinstance(launch.get(name), int)
            or launch[name] < 1
            for name in integer_fields
        ):
            anomaly("supervisor_numeric_identity_invalid", job_id=job_id)
            continue
        fingerprint_matches = launch.get("config_fingerprint") == fingerprint
        if launch.get("boot_id") != boot_id:
            live_identity = None
        else:
            live_identity = process_identity(launch["supervisor_pid"])
        exact_live = bool(
            live_identity is not None
            and live_identity["state"] not in {"Z", "X"}
            and live_identity["start_ticks"] == launch["supervisor_start_ticks"]
            and live_identity["pgid"] == launch["process_group_id"]
            and live_identity["sid"] == launch["session_id"]
            and launch["supervisor_pid"] == launch["process_group_id"] == launch["session_id"]
        )
        members = sorted(group_members.get(launch["process_group_id"], []))
        exit_path = directory / "exit.json"
        exit_record = None
        if exit_path.exists() or exit_path.is_symlink():
            exit_record = safe_record(exit_path, 0o400)
            required_exit = {
                "schema_version",
                "job_id",
                "finished_at",
                "outcome",
                "exit_code",
                "recorded_by",
            }
            if exit_record is not None and (
                set(exit_record) != required_exit
                or exit_record.get("schema_version") != "poincare.job-supervisor-exit.v1"
                or exit_record.get("job_id") != job_id
                or isinstance(exit_record.get("exit_code"), bool)
                or (
                    exit_record.get("exit_code") is not None
                    and not isinstance(exit_record.get("exit_code"), int)
                )
            ):
                anomaly("supervisor_exit_shape_invalid", job_id=job_id)
                exit_record = None
        live = exact_live and exit_record is None
        if not fingerprint_matches and (exit_record is None or exact_live or members):
            anomaly("supervisor_config_fingerprint_mismatch", job_id=job_id)
        if (
            live
            and version == "poincare.job-supervisor.v2"
            and launch["capacity_slot"] > max_jobs
        ):
            anomaly(
                "supervisor_capacity_slot_outside_configured_ceiling",
                job_id=job_id,
                capacity_slot=launch["capacity_slot"],
                configured_ceiling=max_jobs,
            )
        if live and version == "poincare.job-supervisor.v1":
            anomaly("live_supervisor_lacks_capacity_slot", job_id=job_id)
        if exit_record is None and not exact_live:
            anomaly("supervisor_missing_exit", job_id=job_id, group_members=members)
            if members:
                anomaly("orphaned_supervisor_process_group", job_id=job_id, members=members)
        if exit_record is not None and (exact_live or members):
            anomaly("exited_supervisor_still_live", job_id=job_id, group_members=members)
        records[job_id] = {
            **launch,
            "capacity_slot": launch.get("capacity_slot"),
            "live": live,
            "group_members": members,
            "exit_recorded": exit_record is not None,
        }

for job_id, active in active_jobs.items():
    record = records.get(job_id)
    if record is None:
        anomaly("active_job_without_supervisor", job_id=job_id)
        continue
    # Pi execution ends before Codex-owned review begins. Reviewing keeps its
    # fenced lease and launch/exit evidence, but intentionally has no live
    # execution supervisor and must not block another queued Job.
    if active["state"] in {"preparing", "running"} and not record["live"]:
        anomaly("active_job_supervisor_not_live", job_id=job_id)
        continue
    if (
        record["lease_owner"] != active["lease_owner"]
        or record["lease_token"] != active["lease_token"]
    ):
        anomaly(
            "active_job_supervisor_lease_mismatch",
            job_id=job_id,
            database_owner=active["lease_owner"],
            database_token=active["lease_token"],
        )
    if not active["lease_active"]:
        anomaly("active_job_lease_expired", job_id=job_id)

for job_id, record in records.items():
    if record["live"] and job_id not in active_jobs:
        anomaly("live_supervisor_without_active_job", job_id=job_id)

live_slots: dict[int, str] = {}
for job_id, record in records.items():
    if not record["live"]:
        continue
    slot = record["capacity_slot"]
    if slot is None:
        continue
    prior = live_slots.get(slot)
    if prior is not None:
        anomaly(
            "duplicate_live_supervisor_capacity_slot",
            job_id=job_id,
            other_job_id=prior,
            capacity_slot=slot,
        )
    else:
        live_slots[slot] = job_id

payload = {
    "schema_version": "poincare.job-supervisor-report.v1",
    "active_jobs": [active_jobs[key] for key in sorted(active_jobs)],
    "records": [records[key] for key in sorted(records)],
    "live_supervisors": sum(1 for record in records.values() if record["live"]),
    "anomalies": anomalies,
}
print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
raise SystemExit(0 if not anomalies else 2)
PY
}

write_supervisor_exit_once() {
  local job_id=$1
  local outcome=$2
  local exit_code=$3
  local recorded_by=$4
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$POINCARE_DEPLOY_STATE_DIR/workers/supervisors/$job_id/exit.json" \
    "$job_id" "$outcome" "$exit_code" "$recorded_by" "$(utc_now)" <<'PY'
import json
import os
import sys

path, job_id, outcome, raw_exit, recorded_by, timestamp = sys.argv[1:]
exit_code = None if raw_exit == "null" else int(raw_exit)
payload = {
    "schema_version": "poincare.job-supervisor-exit.v1",
    "job_id": job_id,
    "finished_at": timestamp,
    "outcome": outcome,
    "exit_code": exit_code,
    "recorded_by": recorded_by,
}
data = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()
try:
    descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o400)
except FileExistsError:
    raise SystemExit(0)
try:
    os.write(descriptor, data)
    os.fsync(descriptor)
finally:
    os.close(descriptor)
directory = os.open(os.path.dirname(path), os.O_RDONLY)
try:
    os.fsync(directory)
finally:
    os.close(directory)
PY
}

signal_recorded_supervisor_group() {
  local pid=$1
  local start_ticks=$2
  local pgid=$3
  local session_id=$4
  local boot_id=$5
  local signal_name=$6
  "$HARNESS_PI_PYTHON" -S -P -B - "$pid" "$start_ticks" "$pgid" "$session_id" "$boot_id" "$signal_name" <<'PY'
import os
import signal
import sys
from pathlib import Path

pid, start_ticks, pgid, session_id = map(int, sys.argv[1:5])
expected_boot, signal_name = sys.argv[5:]
actual_boot = Path("/proc/sys/kernel/random/boot_id").read_text(encoding="ascii").strip()
if actual_boot != expected_boot:
    raise SystemExit("supervisor boot identity changed")
if pid != pgid or pid != session_id:
    raise SystemExit("supervisor is not its recorded process-group/session leader")
selected = {"TERM": signal.SIGTERM, "KILL": signal.SIGKILL}.get(signal_name)
if selected is None:
    raise SystemExit("unsupported supervisor signal")

def identity(candidate: Path) -> tuple[int, int, int, str] | None:
    try:
        raw = candidate.read_text(encoding="utf-8")
        fields = raw[raw.rfind(")") + 2 :].split()
        if len(fields) < 20:
            return None
        return int(fields[19]), int(fields[2]), int(fields[3]), fields[0]
    except (FileNotFoundError, ProcessLookupError, PermissionError, ValueError):
        return None

leader_path = Path(f"/proc/{pid}/stat")
leader = identity(leader_path)
if leader is not None:
    if leader[:3] != (start_ticks, pgid, session_id) or leader[3] in {"Z", "X"}:
        raise SystemExit("supervisor PID/start-time/PGID/session identity changed")
else:
    members: list[int] = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        current = identity(entry / "stat")
        if current is None or current[3] in {"Z", "X"}:
            continue
        _, current_pgid, current_sid, _ = current
        if current_pgid == pgid:
            if current_sid != session_id:
                raise SystemExit(
                    "orphaned supervisor group contains a process from another session"
                )
            members.append(int(entry.name))
    if not members:
        raise SystemExit(0)
os.killpg(pgid, selected)
PY
}

control_surface_manifest() {
  local git_executable=${HARNESS_PI_GIT:-/usr/bin/git}
  [[ -x "$git_executable" && ! -L "$git_executable" ]] ||
    die "the pinned Git executable is unavailable: $git_executable"
  [[ "$(canonical_path "$git_executable")" == "$git_executable" ]] ||
    die "the pinned Git executable must be canonical: $git_executable"
  "$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_REPO_ROOT" "$git_executable" <<'PY'
import hashlib
import json
import os
import stat
import subprocess
import sys
from pathlib import Path, PurePosixPath

lexical_root = Path(sys.argv[1]).absolute()
git_executable = sys.argv[2]
if lexical_root.is_symlink():
    raise SystemExit("control root must not be a symbolic link")
root = lexical_root.resolve(strict=True)
if root != lexical_root:
    raise SystemExit("control root path is not canonical")

fixed_files = {
    "AGENTS.md",
    "harness/__init__.py",
    "harness/v2/__init__.py",
    "harness/v2/SPEC.md",
    "harness/v2/RUNBOOK.md",
}
included_roots = (
    "harness/v2/runtime",
    "harness/v2/pi",
    "harness/v2/worker",
    "harness/v2/schemas",
    "harness/v2/deploy",
    "harness/v2/prompts",
)
excluded_directories = {
    "__pycache__",
    "node_modules",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".coverage",
}
excluded_files = {".env", ".DS_Store"}


def included(relative: str) -> bool:
    if relative in fixed_files:
        return True
    parsed = PurePosixPath(relative)
    if any(part in excluded_directories for part in parsed.parts):
        return False
    if parsed.name in excluded_files or parsed.suffix in {".pyc", ".pyo"}:
        return False
    return any(relative == prefix or relative.startswith(prefix + "/") for prefix in included_roots)


def git(*arguments: str) -> bytes:
    environment = {
        "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
        "HOME": os.environ.get("HOME", str(root)),
        "LANG": os.environ.get("LANG", "C.UTF-8"),
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_PAGER": "cat",
        "PAGER": "cat",
        "GIT_EXTERNAL_DIFF": "",
    }
    result = subprocess.run(
        (
            git_executable,
            "-c",
            "core.fsmonitor=false",
            "-c",
            f"core.hooksPath={os.devnull}",
            "-c",
            "diff.external=",
            *arguments,
        ),
        cwd=root,
        env=environment,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    if result.returncode != 0:
        error = result.stderr.decode("utf-8", "replace").strip()
        raise SystemExit(f"control-surface Git audit failed: {error or result.returncode}")
    return result.stdout


top = Path(git("rev-parse", "--show-toplevel").decode().strip()).resolve(strict=True)
if top != root:
    raise SystemExit("control root is not its Git checkout top level")
head = git("rev-parse", "HEAD").decode().strip()
tree = git("rev-parse", "HEAD^{tree}").decode().strip()


def discover() -> set[str]:
    paths = set(fixed_files)
    for prefix in included_roots:
        directory = root / Path(*PurePosixPath(prefix).parts)
        if directory.is_symlink() or not directory.is_dir():
            raise SystemExit(f"control-surface directory is missing or redirected: {prefix}")
        if directory.resolve(strict=True) != directory.absolute():
            raise SystemExit(f"control-surface directory has a redirected ancestor: {prefix}")
        for current, directories, filenames in os.walk(directory, followlinks=False):
            retained = []
            for name in sorted(directories):
                candidate = Path(current) / name
                if name in excluded_directories:
                    continue
                if candidate.is_symlink():
                    relative = candidate.relative_to(root).as_posix()
                    raise SystemExit(f"control-surface directory is a symlink: {relative}")
                retained.append(name)
            directories[:] = retained
            for name in sorted(filenames):
                candidate = Path(current) / name
                relative = candidate.relative_to(root).as_posix()
                if not included(relative):
                    continue
                if candidate.is_symlink():
                    raise SystemExit(f"control input is a symlink: {relative}")
                paths.add(relative)
    return paths


disk_paths = discover()
tracked_rows = git("ls-tree", "-r", "-z", "HEAD").split(b"\0")
tracked_modes = {}
for row in tracked_rows:
    if not row:
        continue
    metadata, raw_path = row.split(b"\t", 1)
    mode, kind, _object_id = metadata.decode("ascii").split()
    relative = raw_path.decode("utf-8")
    if included(relative):
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise SystemExit(f"control input is not a tracked regular file: {relative}")
        tracked_modes[relative] = mode
tracked_paths = set(tracked_modes)
if disk_paths != tracked_paths:
    missing = sorted(tracked_paths - disk_paths)
    extra = sorted(disk_paths - tracked_paths)
    raise SystemExit(
        "control-surface path set differs from HEAD; "
        f"missing={missing[:5]!r} extra={extra[:5]!r}"
    )

status = git(
    "status",
    "--porcelain=v1",
    "-z",
    "--untracked-files=all",
    "--ignored=no",
    "--",
    "AGENTS.md",
    "harness/__init__.py",
    "harness/v2/__init__.py",
    "harness/v2/SPEC.md",
    "harness/v2/RUNBOOK.md",
    *included_roots,
)
if status:
    raise SystemExit("the complete Harness control surface is not clean at HEAD")

aggregate = hashlib.sha256()
aggregate.update(b"poincare-deploy-control-surface-v1\0")
entries = []
for relative in sorted(tracked_paths):
    path = root / Path(*PurePosixPath(relative).parts)
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise SystemExit(f"control input is not a regular file: {relative}")
        expected_executable = tracked_modes[relative] == "100755"
        if bool(stat.S_IMODE(before.st_mode) & 0o111) != expected_executable:
            raise SystemExit(f"control input executable mode differs from HEAD: {relative}")
        chunks = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        after = os.fstat(descriptor)
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise SystemExit(f"control input changed while being read: {relative}")
    finally:
        os.close(descriptor)
    data = b"".join(chunks)
    committed = git("cat-file", "blob", f"HEAD:{relative}")
    if data != committed:
        raise SystemExit(f"control input bytes differ from HEAD: {relative}")
    digest = hashlib.sha256(data).hexdigest()
    entries.append({"path": relative, "sha256": digest, "size_bytes": len(data)})
    aggregate.update(relative.encode("utf-8"))
    aggregate.update(b"\0")
    aggregate.update(digest.encode("ascii"))
    aggregate.update(b"\0")
    aggregate.update(str(len(data)).encode("ascii"))
    aggregate.update(b"\n")

if discover() != disk_paths:
    raise SystemExit("the control-surface path set changed during attestation")
if git("rev-parse", "HEAD").decode().strip() != head:
    raise SystemExit("control checkout HEAD changed during attestation")
if git("rev-parse", "HEAD^{tree}").decode().strip() != tree:
    raise SystemExit("control checkout tree changed during attestation")
print(
    json.dumps(
        {
            "schema_version": "poincare.deploy-control-surface.v1",
            "git_commit": head,
            "git_tree": tree,
            "aggregate_sha256": aggregate.hexdigest(),
            "files": entries,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
)
PY
}

control_surface_hash() {
  control_surface_manifest | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["aggregate_sha256"])'
}

assert_session_available_or_owned() {
  local session=$1
  if session_exists "$session" && \
      ! session_is_owned "$session" && \
      ! session_is_bootstrap_owned "$session"; then
    die "tmux session '$session' exists without this harness ownership marker; refusing to touch it"
  fi
}

curl_models() {
  curl --fail --silent \
    --connect-timeout 5 --max-time 30 \
    "${POINCARE_LEANSTRAL_BASE_URL%/}/models"
}

models_include_expected_id() {
  "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys

expected = sys.argv[1]
try:
    payload = json.load(sys.stdin)
    model_ids = [entry.get("id") for entry in payload.get("data", [])]
except (AttributeError, json.JSONDecodeError, TypeError):
    raise SystemExit(2)
raise SystemExit(0 if expected in model_ids else 1)
' "$POINCARE_LEANSTRAL_SERVED_MODEL"
}

endpoint_models_healthy() {
  local response
  response=$(curl_models) || return 1
  printf '%s' "$response" | models_include_expected_id
}

endpoint_chat_smoke() {
  local request response
  request=$("$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_LEANSTRAL_SERVED_MODEL" <<'PY'
import json
import sys

print(json.dumps({
    "model": sys.argv[1],
    "messages": [{"role": "user", "content": "Reply with OK."}],
    "temperature": 1.0,
    "max_tokens": 16,
}))
PY
)
  response=$(curl --fail --silent \
    --connect-timeout 5 --max-time 120 \
    -H 'Content-Type: application/json' \
    --data-binary "$request" \
    "${POINCARE_LEANSTRAL_BASE_URL%/}/chat/completions") || return 1

  printf '%s' "$response" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys

try:
    payload = json.load(sys.stdin)
    choices = payload.get("choices")
except (AttributeError, json.JSONDecodeError, TypeError):
    raise SystemExit(2)
raise SystemExit(0 if isinstance(choices, list) and choices else 1)
'
}

shell_join() {
  printf -v REPLY '%q ' "$@"
  REPLY=${REPLY% }
}
