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

readonly WORKER_DIR="$POINCARE_DEPLOY_STATE_DIR/workers"
readonly WORKER_LOG="$WORKER_DIR/events.jsonl"

exec 7<> "$WORKER_DIR/worker-plane.lock"
"$HARNESS_PI_FLOCK" --nonblock 7 ||
  die "another authenticated worker plane holds the lock"

append_event "$WORKER_LOG" worker_plane_ready \
  pid "$$" maximum_jobs "$POINCARE_MAX_LEANSTRAL_JOBS"

dispatcher_pids=()
reap_dispatchers() {
  local pid status
  local live=()
  for pid in "${dispatcher_pids[@]}"; do
    if kill -0 "$pid" 2>/dev/null; then
      live+=("$pid")
      continue
    fi
    set +e
    wait "$pid"
    status=$?
    set -e
    append_event "$WORKER_LOG" worker_dispatcher_reaped \
      pid "$pid" exit_code "$status"
  done
  dispatcher_pids=("${live[@]}")
}

stopping=0
request_stop() {
  stopping=1
  append_event "$WORKER_LOG" worker_plane_stop_requested pid "$$"
}
trap request_stop HUP INT TERM
trap 'append_event "$WORKER_LOG" worker_plane_exited pid "$$"' EXIT

note "Harness v2 Pi worker plane is ready. It dispatches only Codex-prepared queued Jobs and atomically enforces the $POINCARE_MAX_LEANSTRAL_JOBS execution ceiling."
note "Every Job gets a fresh bounded Pi session; durable JSON/RPC evidence lives under harness/v2/state."

while (( stopping == 0 )); do
  reap_dispatchers
  if deployment_stop_requested; then
    set +e
    jobs_active=$(active_job_count)
    jobs_status=$?
    supervisor_report=$(job_supervisor_report)
    supervisor_status=$?
    set -e
    supervisor_live=unknown
    if (( supervisor_status == 0 )); then
      supervisor_live=$(printf '%s' "$supervisor_report" | "$HARNESS_PI_PYTHON" -S -P -B -c \
        'import json,sys; print(json.load(sys.stdin)["live_supervisors"])')
    fi
    session_windows=$(tmux display-message -p -t "${TMUX_PANE:-}" '#{session_windows}' 2>/dev/null || printf 'unknown')
    if (( jobs_status == 0 && supervisor_status == 0 )) && \
        [[ "$jobs_active" == 0 && "$supervisor_live" == 0 && "$session_windows" == 1 ]]; then
      append_event "$WORKER_LOG" worker_plane_drained pid "$$"
      exit 0
    fi
  else
    set +e
    queued=$(queued_job_count)
    queued_status=$?
    supervisor_report=$(job_supervisor_report)
    supervisor_status=$?
    set -e
    if (( queued_status == 0 && supervisor_status == 0 && queued > 0 )); then
      supervisor_live=$(printf '%s' "$supervisor_report" | \
        "$HARNESS_PI_PYTHON" -S -P -B -c \
        'import json,sys; print(json.load(sys.stdin)["live_supervisors"])')
      occupied=${#dispatcher_pids[@]}
      (( supervisor_live > occupied )) && occupied=$supervisor_live
      available=$((POINCARE_MAX_LEANSTRAL_JOBS - occupied))
      (( available > queued )) && available=$queued
      for (( launch_index=0; launch_index<available; launch_index++ )); do
        "$SCRIPT_DIR/run-job-supervised.sh" --dispatch-next \
          "$POINCARE_CONFIG_FILE" >> "$WORKER_DIR/dispatch.log" 2>&1 &
        dispatcher_pid=$!
        dispatcher_pids+=("$dispatcher_pid")
        append_event "$WORKER_LOG" worker_dispatcher_started \
          pid "$dispatcher_pid" queued_seen "$queued"
      done
    elif (( queued_status != 0 || supervisor_status != 0 )); then
      append_event "$WORKER_LOG" worker_dispatch_audit_failed \
        queued_status "$queued_status" supervisor_status "$supervisor_status"
    fi
  fi
  sleep 5 7>&-
done
