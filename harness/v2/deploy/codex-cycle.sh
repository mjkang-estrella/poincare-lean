#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

if (( $# > 1 )); then
  printf 'Usage: %s [environment-file]\n' "${0##*/}" >&2
  exit 64
fi

load_config "${1:-$SCRIPT_DIR/.env}"
unset POINCARE_LIFECYCLE_LOCKED POINCARE_CONTROL_LOCKED \
  POINCARE_WORKERS_LOCKED POINCARE_OBSERVE_LOCKED \
  POINCARE_JOB_SUPERVISOR_SESSION
[[ -x "$HARNESS_PI_FLOCK" ]] || die "flock is required at $HARNESS_PI_FLOCK"
ensure_runtime_layout

readonly CONTROL_DIR="$POINCARE_DEPLOY_STATE_DIR/control"
readonly CONTROL_LOG="$CONTROL_DIR/events.jsonl"
readonly COMPLETION_MARKER="$CONTROL_DIR/completion-verified.json"
readonly COMPLETION_DIR="$CONTROL_DIR/completions"

exec 7<> "$CONTROL_DIR/codex-cycle.lock"
"$HARNESS_PI_FLOCK" --nonblock 7 ||
  die "another authenticated Codex control loop holds the lock"

verify_existing_completion_marker() {
  "$HARNESS_PI_PYTHON" -S -P -B - \
    "$COMPLETION_MARKER" "$POINCARE_DEPLOY_STATE_DIR" "$POINCARE_REPO_ROOT" \
    "$POINCARE_INTEGRATION_BRANCH" "$POINCARE_CONFIG_FINGERPRINT" \
    "$HARNESS_PI_GIT" <<'PY'
import hashlib
import json
import os
import stat
import subprocess
import sys
from pathlib import Path, PurePosixPath

marker = Path(sys.argv[1]).absolute()
state_dir = Path(sys.argv[2]).resolve(strict=True)
repo_root = Path(sys.argv[3]).resolve(strict=True)
configured_branch = sys.argv[4]
fingerprint = sys.argv[5]
git_executable = sys.argv[6]
if (
    not os.path.isabs(git_executable)
    or os.path.realpath(git_executable) != git_executable
    or not os.access(git_executable, os.X_OK)
):
    raise SystemExit("completion marker Git authority is not a canonical executable")
if marker.is_symlink() or not marker.is_file():
    raise SystemExit("completion marker is missing, redirected, or non-regular")
metadata = marker.stat()
if metadata.st_uid != os.geteuid() or stat.S_IMODE(metadata.st_mode) != 0o400:
    raise SystemExit("completion marker ownership or sealed mode is invalid")
try:
    payload = json.loads(marker.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as exc:
    raise SystemExit(f"completion marker is unreadable: {exc}") from exc
required = {
    "schema_version",
    "status",
    "evidence_id",
    "evidence_file",
    "timestamp",
    "head",
    "tree",
    "branch",
    "working_tree_clean",
    "config_fingerprint",
    "control_surface_sha256",
    "exact_probe",
    "completion_audit",
}
if set(payload) != required:
    raise SystemExit("completion marker has an invalid field set")
if payload["schema_version"] != "poincare.exact-completion-evidence.v1" or payload["status"] != "verified":
    raise SystemExit("completion marker schema or status is invalid")
if payload["config_fingerprint"] != fingerprint:
    raise SystemExit("completion marker belongs to another deployment configuration")
if payload["branch"] != configured_branch or payload["working_tree_clean"] is not True:
    raise SystemExit("completion marker branch or cleanliness claim is invalid")
evidence_relative = PurePosixPath(payload["evidence_file"])
if evidence_relative.is_absolute() or ".." in evidence_relative.parts:
    raise SystemExit("completion evidence path is unsafe")
evidence_path = state_dir / Path(*evidence_relative.parts)
if evidence_path.is_symlink() or not evidence_path.is_file():
    raise SystemExit("unique completion evidence file is missing or redirected")
if (marker.stat().st_dev, marker.stat().st_ino) != (
    evidence_path.stat().st_dev,
    evidence_path.stat().st_ino,
):
    raise SystemExit("completion marker is not the write-once evidence inode")

for label in ("exact_probe", "completion_audit"):
    entry = payload[label]
    if not isinstance(entry, dict) or set(entry) != {
        "argv",
        "cwd",
        "exit_code",
        "log",
        "sha256",
        "size_bytes",
    }:
        raise SystemExit(f"{label} evidence has an invalid shape")
    if entry["exit_code"] != 0 or not isinstance(entry["argv"], list) or not entry["argv"]:
        raise SystemExit(f"{label} did not record a successful exact argv")
    relative = PurePosixPath(entry["log"])
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit(f"{label} log path is unsafe")
    log_path = state_dir / Path(*relative.parts)
    if log_path.is_symlink() or not log_path.is_file():
        raise SystemExit(f"{label} log is missing or redirected")
    log_metadata = log_path.stat()
    if log_metadata.st_uid != os.geteuid() or stat.S_IMODE(log_metadata.st_mode) != 0o400:
        raise SystemExit(f"{label} log is not sealed")
    data = log_path.read_bytes()
    if len(data) != entry["size_bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise SystemExit(f"{label} log hash or size differs from the marker")

def git(*arguments: str) -> str:
    result = subprocess.run(
        (git_executable, *arguments),
        cwd=repo_root,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=20,
        env={
            "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
            "HOME": os.environ.get("HOME", str(repo_root)),
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_NO_REPLACE_OBJECTS": "1",
        },
    )
    if result.returncode != 0:
        raise SystemExit("could not revalidate completion marker against Git")
    return result.stdout.decode("utf-8").strip()

if git("rev-parse", "HEAD") != payload["head"]:
    raise SystemExit("completion marker HEAD is no longer checked out")
if git("rev-parse", "HEAD^{tree}") != payload["tree"]:
    raise SystemExit("completion marker tree is no longer checked out")
if git("symbolic-ref", "--quiet", "--short", "HEAD") != configured_branch:
    raise SystemExit("completion marker integration branch is no longer checked out")
if git("status", "--porcelain=v1", "--untracked-files=all"):
    raise SystemExit("completion marker checkout is no longer clean")
print(payload["head"])
PY
}

if [[ -e "$COMPLETION_MARKER" || -L "$COMPLETION_MARKER" ]]; then
  verified_head=$(verify_existing_completion_marker) ||
    die "existing exact-completion marker failed write-once evidence validation"
  append_event "$CONTROL_LOG" completion_already_verified head "$verified_head"
  note "Exact Poincare completion was already sealed at $verified_head."
  exit 0
fi

append_event "$CONTROL_LOG" loop_started pid "$$" head "$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)"

stop_requested=0
request_stop() {
  stop_requested=1
  append_event "$CONTROL_LOG" loop_stop_requested pid "$$"
}
trap request_stop HUP INT TERM
trap 'append_event "$CONTROL_LOG" loop_exited pid "$$"' EXIT

cycle_number=0
consecutive_codex_failures=0
while (( stop_requested == 0 )); do
  if deployment_stop_requested; then
    append_event "$CONTROL_LOG" loop_stopped_at_safe_boundary reason "operator_request"
    exit 0
  fi
  cycle_number=$((cycle_number + 1))
  cycle_stamp=$(date -u '+%Y%m%dT%H%M%SZ')
  cycle_id="${cycle_stamp}-$$-${cycle_number}"
  cycle_dir="$CONTROL_DIR/cycles/$cycle_id"
  mkdir -- "$cycle_dir"
  cycle_started_epoch=$(date +%s)
  cycle_deadline_epoch=$((cycle_started_epoch + POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS))

  head_before=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)
  tree_before=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse 'HEAD^{tree}')
  branch_before=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" symbolic-ref --quiet --short HEAD 2>/dev/null || printf 'detached')
  set +e
  control_hash_before=$(control_surface_hash)
  control_hash_before_status=$?
  set -e
  if (( control_hash_before_status != 0 )); then
    append_event "$CONTROL_LOG" loop_paused \
      cycle_id "$cycle_id" reason "control_surface_unreadable_at_cycle_start"
    die "the Harness trust boundary is missing, non-regular, or unreadable"
  fi
  dirty_before=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" status --porcelain=v1 --untracked-files=all | wc -l | tr -d ' ')
  append_event "$CONTROL_LOG" cycle_started \
    cycle_id "$cycle_id" head "$head_before" tree "$tree_before" \
    branch "$branch_before" dirty_paths "$dirty_before" \
    deadline_epoch "$cycle_deadline_epoch"

  exact_probe_argv=(
    /usr/bin/timeout --kill-after=30 "$POINCARE_EXACT_PROBE_TIMEOUT_SECONDS"
    "$SCRIPT_DIR/exact-completion-probe.sh" "$POINCARE_CONFIG_FILE"
  )
  set +e
  "${exact_probe_argv[@]}" \
    > "$cycle_dir/exact-declaration-probe.log" 2>&1 7>&-
  exact_status=$?
  set -e
  exact_metadata=$(seal_evidence_file "$cycle_dir/exact-declaration-probe.log")
  exact_sha256=$(printf '%s' "$exact_metadata" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  exact_size=$(printf '%s' "$exact_metadata" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["size_bytes"])')

  head_after_probe=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)
  tree_after_probe=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse 'HEAD^{tree}')
  branch_after_probe=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" symbolic-ref --quiet --short HEAD 2>/dev/null || printf 'detached')
  dirty_after_probe=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" status --porcelain=v1 --untracked-files=all | wc -l | tr -d ' ')

  completion_candidate_clean=0
  if (( exact_status == 0 && dirty_before == 0 && dirty_after_probe == 0 )) && \
      [[ "$branch_before" == "$POINCARE_INTEGRATION_BRANCH" ]] && \
      [[ "$branch_after_probe" == "$branch_before" ]] && \
      [[ "$head_after_probe" == "$head_before" ]] && \
      [[ "$tree_after_probe" == "$tree_before" ]]; then
    completion_candidate_clean=1
  fi

  if (( exact_status == 0 && completion_candidate_clean == 1 )); then
    append_event "$CONTROL_LOG" exact_declaration_probe_passed \
      cycle_id "$cycle_id" head "$head_before" tree "$tree_before" \
      branch "$branch_before" log_sha256 "$exact_sha256" log_size_bytes "$exact_size"
    completion_argv=(
      /usr/bin/timeout --kill-after=60 "$POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS"
      /usr/bin/env
      "PATH=$POINCARE_PI_TOOLCHAIN_ROOT/bin:/usr/bin:/bin"
      LEAN_NUM_THREADS=1
      /bin/sh scripts/completion_audit.sh
    )
    set +e
    (
      cd "$POINCARE_REPO_ROOT"
      "${completion_argv[@]}"
    ) > "$cycle_dir/completion-audit.log" 2>&1 7>&-
    completion_status=$?
    set -e
    completion_metadata=$(seal_evidence_file "$cycle_dir/completion-audit.log")
    completion_sha256=$(printf '%s' "$completion_metadata" | "$HARNESS_PI_PYTHON" -S -P -B -c \
      'import json,sys; print(json.load(sys.stdin)["sha256"])')
    completion_size=$(printf '%s' "$completion_metadata" | "$HARNESS_PI_PYTHON" -S -P -B -c \
      'import json,sys; print(json.load(sys.stdin)["size_bytes"])')

    completed_head=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)
    completed_tree=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse 'HEAD^{tree}')
    completed_branch=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" symbolic-ref --quiet --short HEAD 2>/dev/null || printf 'detached')
    completion_dirty=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" status --porcelain=v1 --untracked-files=all | wc -l | tr -d ' ')
    set +e
    completed_control_hash=$(control_surface_hash)
    completed_control_status=$?
    set -e
    if (( completion_status == 0 )) && \
        (( completed_control_status == 0 )) && \
        [[ "$completed_head" == "$head_before" ]] && \
        [[ "$completed_tree" == "$tree_before" ]] && \
        [[ "$completed_branch" == "$branch_before" ]] && \
        [[ "$completed_branch" == "$POINCARE_INTEGRATION_BRANCH" ]] && \
        [[ "$completed_control_hash" == "$control_hash_before" ]] && \
        (( completion_dirty == 0 )); then
      evidence_file="$COMPLETION_DIR/$cycle_id.json"
      evidence_relative="control/completions/$cycle_id.json"
      exact_log_relative="control/cycles/$cycle_id/exact-declaration-probe.log"
      completion_log_relative="control/cycles/$cycle_id/completion-audit.log"
      "$HARNESS_PI_PYTHON" -S -P -B - \
        "$evidence_file" "$COMPLETION_MARKER" "$(utc_now)" "$cycle_id" \
        "$evidence_relative" "$completed_head" "$completed_tree" "$completed_branch" \
        "$POINCARE_CONFIG_FINGERPRINT" "$completed_control_hash" \
        "$POINCARE_REPO_ROOT" "$exact_status" "$exact_log_relative" \
        "$exact_sha256" "$exact_size" "$completion_status" \
        "$completion_log_relative" "$completion_sha256" "$completion_size" \
        "$POINCARE_EXACT_PROBE_TIMEOUT_SECONDS" \
        "$SCRIPT_DIR/exact-completion-probe.sh" "$POINCARE_CONFIG_FILE" \
        "$POINCARE_PI_TOOLCHAIN_ROOT" \
        "$POINCARE_COMPLETION_GATE_TIMEOUT_SECONDS" <<'PY'
import json
import os
import sys

(
    path,
    marker,
    timestamp,
    cycle_id,
    evidence_relative,
    head,
    tree,
    branch,
    fingerprint,
    control_hash,
    repo_root,
    exact_exit,
    exact_log,
    exact_sha256,
    exact_size,
    audit_exit,
    audit_log,
    audit_sha256,
    audit_size,
    exact_timeout,
    exact_script,
    config_file,
    toolchain_root,
    audit_timeout,
) = sys.argv[1:]
payload = {
    "schema_version": "poincare.exact-completion-evidence.v1",
    "status": "verified",
    "evidence_id": cycle_id,
    "evidence_file": evidence_relative,
    "timestamp": timestamp,
    "head": head,
    "tree": tree,
    "branch": branch,
    "working_tree_clean": True,
    "config_fingerprint": fingerprint,
    "control_surface_sha256": control_hash,
    "exact_probe": {
        "argv": [
            "/usr/bin/timeout",
            "--kill-after=30",
            exact_timeout,
            exact_script,
            config_file,
        ],
        "cwd": repo_root,
        "exit_code": int(exact_exit),
        "log": exact_log,
        "sha256": exact_sha256,
        "size_bytes": int(exact_size),
    },
    "completion_audit": {
        "argv": [
            "/usr/bin/timeout",
            "--kill-after=60",
            audit_timeout,
            "/usr/bin/env",
            f"PATH={toolchain_root}/bin:/usr/bin:/bin",
            "LEAN_NUM_THREADS=1",
            "/bin/sh",
            "scripts/completion_audit.sh",
        ],
        "cwd": repo_root,
        "exit_code": int(audit_exit),
        "log": audit_log,
        "sha256": audit_sha256,
        "size_bytes": int(audit_size),
    },
}
data = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")
descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o400)
try:
    os.write(descriptor, data)
    os.fsync(descriptor)
finally:
    os.close(descriptor)
try:
    os.link(path, marker)
except Exception:
    raise
for directory_path in {os.path.dirname(path), os.path.dirname(marker)}:
    directory = os.open(directory_path, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
PY
      append_event "$CONTROL_LOG" completion_verified \
        cycle_id "$cycle_id" head "$completed_head" tree "$completed_tree" \
        branch "$completed_branch" evidence "$evidence_relative" \
        exact_probe_sha256 "$exact_sha256" completion_audit_sha256 "$completion_sha256"
      note "Exact Poincare completion and the full completion audit passed at $completed_head."
      exit 0
    fi

    append_event "$CONTROL_LOG" completion_gate_failed \
      cycle_id "$cycle_id" exit_code "$completion_status" \
      head_before "$head_before" head_after "$completed_head" \
      branch_before "$branch_before" branch_after "$completed_branch" \
      dirty_paths "$completion_dirty" exact_probe_sha256 "$exact_sha256" \
      completion_audit_sha256 "$completion_sha256"
  elif (( exact_status == 0 )); then
    append_event "$CONTROL_LOG" completion_candidate_not_durable \
      cycle_id "$cycle_id" head "$head_before" tree "$tree_before" \
      branch "$branch_before" reason "integration_checkout_not_clean_stable_configured_branch" \
      exact_probe_sha256 "$exact_sha256"
  else
    probe_result=$(head -n 1 "$cycle_dir/exact-declaration-probe.log" 2>/dev/null || true)
    append_event "$CONTROL_LOG" exact_declaration_not_verified \
      cycle_id "$cycle_id" probe_result "${probe_result:-unknown}" \
      exit_code "$exact_status" log_sha256 "$exact_sha256" log_size_bytes "$exact_size"
  fi

  prompt_epoch=$(date +%s)
  cycle_elapsed_seconds=$((prompt_epoch - cycle_started_epoch))
  cycle_remaining_seconds=$((cycle_deadline_epoch - prompt_epoch))
  if (( cycle_remaining_seconds < 1 )); then
    cycle_remaining_seconds=1
    append_event "$CONTROL_LOG" cycle_budget_exhausted_before_codex \
      cycle_id "$cycle_id" elapsed_seconds "$cycle_elapsed_seconds"
  fi
  cycle_deadline_utc=$(utc_from_epoch "$cycle_deadline_epoch")
  set +e
  pipeline_counts=$(job_pipeline_counts)
  pipeline_counts_status=$?
  set -e
  (( pipeline_counts_status == 0 )) || pipeline_counts='{"status":"unavailable"}'

  {
    cat "$POINCARE_PROMPT_FILE"
    printf '\n## Runtime cycle facts\n\n'
    printf -- '- Cycle ID: `%s`\n' "$cycle_id"
    printf -- '- Integration checkout: `%s`\n' "$POINCARE_REPO_ROOT"
    printf -- '- HEAD at cycle start: `%s`\n' "$head_before"
    printf -- '- Integration branch at cycle start: `%s` (configured: `%s`)\n' \
      "$branch_before" "$POINCARE_INTEGRATION_BRANCH"
    printf -- '- Dirty paths at cycle start: `%s`\n' "$dirty_before"
    printf -- '- Configured hard cycle budget: `%s` seconds\n' \
      "$POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS"
    printf -- '- Elapsed before Codex launch: `%s` seconds\n' "$cycle_elapsed_seconds"
    printf -- '- Remaining hard cycle budget at Codex launch: `%s` seconds\n' \
      "$cycle_remaining_seconds"
    printf -- '- Hard cycle deadline: `%s` (epoch `%s`)\n' \
      "$cycle_deadline_utc" "$cycle_deadline_epoch"
    printf -- '- Mandatory independent-review reserve: `%s` seconds\n' \
      "$POINCARE_CODEX_REVIEW_RESERVE_SECONDS"
    printf -- '- Do not start a Job unless its remaining wall-clock budget plus the review reserve fits inside the remaining hard cycle budget.\n'
    printf -- '- Ignored runtime state: `%s`\n' "$POINCARE_STATE_DIR"
    printf -- '- Isolated Job worktree root: `%s`\n' "$POINCARE_WORKTREE_ROOT"
    printf -- '- Sealed Pi install manifest: `%s` (`%s`)\n' \
      "$POINCARE_PI_INSTALL_MANIFEST" "$POINCARE_PI_INSTALL_MANIFEST_SHA256"
    printf -- '- Sealed Pi dependency graph: `%s` (`%s`)\n' \
      "$POINCARE_PI_DEPENDENCY_GRAPH" "$POINCARE_PI_DEPENDENCY_GRAPH_SHA256"
    printf -- '- Immutable per-base Lake cache root: `%s`\n' "$POINCARE_PI_LAKE_CACHE_ROOT"
    printf -- '- Lean toolchain root: `%s`\n' "$POINCARE_PI_TOOLCHAIN_ROOT"
    printf -- '- Leanstral served ID: `%s`\n' "$POINCARE_LEANSTRAL_SERVED_MODEL"
    printf -- '- Leanstral artifact: `%s`\n' "$POINCARE_LEANSTRAL_ARTIFACT"
    printf -- '- Leanstral revision: `%s`\n' "$POINCARE_LEANSTRAL_REVISION"
    printf -- '- Maximum simultaneous Leanstral Jobs: `%s`\n' "$POINCARE_MAX_LEANSTRAL_JOBS"
    printf -- '- Current Job pipeline counts: `%s`\n' "$pipeline_counts"
    printf -- '- Required supervised Job launcher: `%s`\n' \
      "$SCRIPT_DIR/run-job-supervised.sh"
    printf -- '- Every Pi Job must run through that launcher so its PID, Linux start time, PGID, lease identity, and terminal status remain recoverable.\n'
    printf -- '- Enqueue only fully prepared Jobs. The worker plane owns automatic claim and supervisor launch; Codex owns every review, Task transition, integration, and commit.\n'
    printf '\nThe private endpoint URL is available in the process environment; do not print it.\n'
  } > "$cycle_dir/prompt.md"

  codex_command=(
    "$POINCARE_CODEX_BIN"
    -a never
    -c "model_reasoning_effort=$POINCARE_CODEX_REASONING_EFFORT"
  )
  if [[ -n "$POINCARE_CODEX_MODEL" ]]; then
    codex_command+=( -m "$POINCARE_CODEX_MODEL" )
  fi
  codex_command+=(
    exec
    -C "$POINCARE_REPO_ROOT"
    --add-dir "$POINCARE_WORKTREE_ROOT"
    --add-dir "$POINCARE_PI_LAKE_CACHE_ROOT"
    # Codex is the trusted host orchestrator. A Linux workspace-write user
    # namespace maps root-owned attested tools to the overflow UID and prevents
    # cache verification, supervisor admission, review, and commit authority.
    # Leanstral remains isolated behind Pi's exact six scoped tools.
    --sandbox danger-full-access
    --json
    --output-schema "$POINCARE_CYCLE_RESULT_SCHEMA"
    --color never
    --output-last-message "$cycle_dir/final-message.md"
    -
  )

  set +e
  /usr/bin/timeout --kill-after=60 "$cycle_remaining_seconds" \
    "${codex_command[@]}" < "$cycle_dir/prompt.md" \
    > "$cycle_dir/codex-events.jsonl" \
    2> "$cycle_dir/codex-stderr.log" 7>&-
  codex_status=$?
  set -e

  head_after=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)
  dirty_after=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" status --porcelain | wc -l | tr -d ' ')
  set +e
  control_hash_after=$(control_surface_hash)
  control_hash_after_status=$?
  set -e
  append_event "$CONTROL_LOG" cycle_finished \
    cycle_id "$cycle_id" exit_code "$codex_status" head_before "$head_before" \
    head_after "$head_after" dirty_paths "$dirty_after"

  if (( control_hash_after_status != 0 )); then
    append_event "$CONTROL_LOG" loop_paused \
      cycle_id "$cycle_id" reason "control_surface_unreadable_after_cycle"
    die "Codex made the Harness trust boundary missing, non-regular, or unreadable"
  fi

  if [[ "$control_hash_after" != "$control_hash_before" ]]; then
    append_event "$CONTROL_LOG" loop_paused \
      cycle_id "$cycle_id" reason "control_surface_modified"
    die "Codex modified the launcher, prompt, or AGENTS contract; paused for independent review"
  fi

  (( stop_requested == 0 )) || break

  if (( codex_status != 0 )); then
    consecutive_codex_failures=$((consecutive_codex_failures + 1))
    backoff_exponent=$((consecutive_codex_failures - 1))
    (( backoff_exponent > 6 )) && backoff_exponent=6
    retry_cooldown=$((POINCARE_CYCLE_COOLDOWN_SECONDS * (1 << backoff_exponent)))
    (( retry_cooldown > 3600 )) && retry_cooldown=3600
    append_event "$CONTROL_LOG" codex_process_failed \
      cycle_id "$cycle_id" exit_code "$codex_status" \
      consecutive_failures "$consecutive_codex_failures" retry_seconds "$retry_cooldown"
    if (( consecutive_codex_failures == 3 )); then
      append_event "$CONTROL_LOG" operator_alert \
        cycle_id "$cycle_id" reason "repeated_codex_process_failure"
    fi
  else
    consecutive_codex_failures=0
    retry_cooldown=$POINCARE_CYCLE_COOLDOWN_SECONDS
    set +e
    resume_decision=$("$HARNESS_PI_PYTHON" -S -P -B - "$cycle_dir/final-message.md" <<'PY'
import json
import sys

try:
    with open(sys.argv[1], encoding="utf-8") as handle:
        payload = json.load(handle)
    decision = payload["resume_decision"]
except (OSError, KeyError, json.JSONDecodeError, TypeError):
    raise SystemExit(2)
if decision not in {"continue", "pause", "completion_candidate"}:
    raise SystemExit(3)
print(decision)
PY
    )
    decision_status=$?
    set -e
    if (( decision_status != 0 )); then
      append_event "$CONTROL_LOG" loop_paused \
        cycle_id "$cycle_id" reason "invalid_cycle_result"
      die "Codex returned no valid machine-readable resume decision; paused for review"
    fi
    append_event "$CONTROL_LOG" cycle_resume_decision \
      cycle_id "$cycle_id" decision "$resume_decision"
    if [[ "$resume_decision" == pause ]]; then
      append_event "$CONTROL_LOG" loop_paused \
        cycle_id "$cycle_id" reason "orchestrator_requested_pause"
      exit 75
    fi
  fi

  if deployment_stop_requested; then
    append_event "$CONTROL_LOG" loop_stopped_at_safe_boundary reason "operator_request"
    exit 0
  fi

  append_event "$CONTROL_LOG" cycle_cooldown \
    cycle_id "$cycle_id" seconds "$retry_cooldown"
  cooldown_elapsed=0
  while (( cooldown_elapsed < retry_cooldown )); do
    if deployment_stop_requested; then
      append_event "$CONTROL_LOG" loop_stopped_at_safe_boundary reason "operator_request"
      exit 0
    fi
    sleep 5 7>&-
    cooldown_elapsed=$((cooldown_elapsed + 5))
  done
done
