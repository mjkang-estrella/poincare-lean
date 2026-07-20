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
  die "another authenticated worker sentinel holds the lock"

append_event "$WORKER_LOG" worker_plane_ready \
  pid "$$" maximum_jobs "$POINCARE_MAX_LEANSTRAL_JOBS"

stopping=0
request_stop() {
  stopping=1
  append_event "$WORKER_LOG" worker_plane_stop_requested pid "$$"
}
trap request_stop HUP INT TERM
trap 'append_event "$WORKER_LOG" worker_plane_exited pid "$$"' EXIT

note "Harness v2 Pi worker sentinel is ready. The supervised launcher atomically enforces the $POINCARE_MAX_LEANSTRAL_JOBS Job ceiling; the sole trusted Codex loop remains responsible for Job selection."
note "Every Job gets a fresh bounded Pi session; durable JSON/RPC evidence lives under harness/v2/state."

while (( stopping == 0 )); do
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
  fi
  sleep 5 7>&-
done
