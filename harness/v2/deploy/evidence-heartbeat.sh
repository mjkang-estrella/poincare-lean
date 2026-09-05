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
ensure_runtime_layout

readonly OBSERVE_DIR="$POINCARE_DEPLOY_STATE_DIR/observe"
readonly HEARTBEAT_LOG="$OBSERVE_DIR/heartbeats.jsonl"

heartbeat_stamp=$(date -u '+%Y%m%dT%H%M%SZ')
snapshot_dir="$OBSERVE_DIR/snapshots/${heartbeat_stamp}-$$"
mkdir -- "$snapshot_dir"

head_before=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)
tree_before=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse 'HEAD^{tree}')
dirty_before=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" status --porcelain | wc -l | tr -d ' ')

set +e
/usr/bin/timeout --kill-after=30 "$POINCARE_EXACT_PROBE_TIMEOUT_SECONDS" \
  "$SCRIPT_DIR/exact-completion-probe.sh" "$POINCARE_CONFIG_FILE" \
  > "$snapshot_dir/exact-declaration-probe.log" 2>&1
probe_exit=$?
set -e
probe_metadata=$(seal_evidence_file "$snapshot_dir/exact-declaration-probe.log")
probe_sha256=$(printf '%s' "$probe_metadata" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["sha256"])')
probe_size=$(printf '%s' "$probe_metadata" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["size_bytes"])')
probe_result=$(head -n 1 "$snapshot_dir/exact-declaration-probe.log" 2>/dev/null || true)
probe_result=${probe_result#EXACT_DECLARATION_PROBE=}
probe_result=${probe_result:-probe_error}

if endpoint_models_healthy && endpoint_chat_smoke; then
  endpoint_state=healthy
else
  endpoint_state=unhealthy
fi

head_commit=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)
tree_after=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse 'HEAD^{tree}')
branch=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" symbolic-ref --quiet --short HEAD 2>/dev/null || printf 'detached')
dirty_count=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" status --porcelain | wc -l | tr -d ' ')
worktree_count=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" worktree list --porcelain | awk '$1 == "worktree" {count++} END {print count + 0}')
snapshot_stable=false
if [[ "$head_commit" == "$head_before" && "$tree_after" == "$tree_before" && "$dirty_count" == "$dirty_before" ]]; then
  snapshot_stable=true
else
  probe_result=repository_changed_during_probe
fi

session_state() {
  local session=$1
  if session_is_live_owned "$session"; then
    printf 'owned-running'
  elif session_is_bootstrap_owned "$session"; then
    printf 'owned-bootstrap-recoverable'
  elif session_is_owned "$session"; then
    printf 'owned-stopped'
  elif session_exists "$session"; then
    printf 'foreign'
  else
    printf 'absent'
  fi
}

set +e
supervisor_report=$(job_supervisor_report)
supervisor_status=$?
set -e
supervisor_live=unknown
supervisor_anomalies=unknown
if [[ -n "$supervisor_report" ]]; then
  IFS=$'\t' read -r supervisor_live supervisor_anomalies < <(
    printf '%s' "$supervisor_report" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys
report = json.load(sys.stdin)
print("{}\t{}".format(report["live_supervisors"], len(report["anomalies"])))
'
  )
fi

set +e
utilization_snapshot=$(job_utilization_snapshot)
utilization_status=$?
set -e
queued_jobs=unknown
executing_jobs=unknown
reviewing_jobs=unknown
execution_backlog=unknown
backlog_underfilled=unknown
if (( utilization_status == 0 )); then
  IFS=$'\t' read -r queued_jobs executing_jobs reviewing_jobs execution_backlog backlog_underfilled < <(
    printf '%s' "$utilization_snapshot" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys
snapshot = json.load(sys.stdin)
print("{}\t{}\t{}\t{}\t{}".format(
    snapshot["queued"], snapshot["executing"], snapshot["reviewing"],
    snapshot["execution_backlog"], snapshot["underfilled"]
))
'
  )
fi

append_event "$HEARTBEAT_LOG" evidence_heartbeat \
  head_before "$head_before" head_after "$head_commit" tree "$tree_after" \
  branch "$branch" dirty_paths "$dirty_count" snapshot_stable "$snapshot_stable" \
  worktrees "$worktree_count" exact_declaration_probe "$probe_result" \
  exact_probe_exit "$probe_exit" exact_probe_sha256 "$probe_sha256" \
  exact_probe_size_bytes "$probe_size" leanstral_endpoint "$endpoint_state" \
  job_supervisor_audit_exit "$supervisor_status" \
  live_job_supervisors "$supervisor_live" supervisor_anomalies "$supervisor_anomalies" \
  utilization_audit_exit "$utilization_status" \
  queued_jobs "$queued_jobs" executing_jobs "$executing_jobs" \
  reviewing_jobs "$reviewing_jobs" execution_backlog "$execution_backlog" \
  execution_backlog_target "$POINCARE_LEANSTRAL_BACKLOG_TARGET" \
  backlog_underfilled "$backlog_underfilled" \
  control_session "$(session_state "$POINCARE_CONTROL_SESSION")" \
  workers_session "$(session_state "$POINCARE_WORKERS_SESSION")" \
  observe_session "$(session_state "$POINCARE_OBSERVE_SESSION")" \
  snapshot "deploy/observe/snapshots/${heartbeat_stamp}-$$"

tail -n 1 "$HEARTBEAT_LOG"
