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

readonly OBSERVE_DIR="$POINCARE_DEPLOY_STATE_DIR/observe"
readonly OBSERVE_LOG="$OBSERVE_DIR/events.jsonl"

exec 7<> "$OBSERVE_DIR/heartbeat-loop.lock"
"$HARNESS_PI_FLOCK" --nonblock 7 ||
  die "another authenticated evidence heartbeat loop holds the lock"

append_event "$OBSERVE_LOG" heartbeat_loop_started \
  pid "$$" interval_seconds "$POINCARE_HEARTBEAT_SECONDS"

stopping=0
request_stop() {
  stopping=1
  append_event "$OBSERVE_LOG" heartbeat_loop_stop_requested pid "$$"
}
trap request_stop HUP INT TERM
trap 'append_event "$OBSERVE_LOG" heartbeat_loop_exited pid "$$"' EXIT

while (( stopping == 0 )); do
  heartbeat_started_ns=$(monotonic_ns)
  heartbeat_deadline_ns=$((heartbeat_started_ns + POINCARE_HEARTBEAT_SECONDS * 1000000000))
  append_event "$OBSERVE_LOG" heartbeat_attempt_started \
    monotonic_start_ns "$heartbeat_started_ns" \
    next_start_deadline_monotonic_ns "$heartbeat_deadline_ns" \
    interval_seconds "$POINCARE_HEARTBEAT_SECONDS"
  set +e
  "$SCRIPT_DIR/evidence-heartbeat.sh" "$POINCARE_CONFIG_FILE" 7>&-
  heartbeat_status=$?
  set -e
  heartbeat_finished_ns=$(monotonic_ns)
  timing=$(heartbeat_timing_metrics \
    "$heartbeat_started_ns" "$heartbeat_finished_ns" \
    "$((POINCARE_HEARTBEAT_SECONDS * 1000000000))")
  IFS=$'\t' read -r heartbeat_duration_ns heartbeat_overrun_ns < <(
    printf '%s' "$timing" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys
value = json.load(sys.stdin)
print("{}\t{}".format(value["duration_ns"], value["overrun_ns"]))
'
  )
  append_event "$OBSERVE_LOG" heartbeat_attempt_finished \
    exit_code "$heartbeat_status" monotonic_start_ns "$heartbeat_started_ns" \
    monotonic_finish_ns "$heartbeat_finished_ns" duration_ns "$heartbeat_duration_ns" \
    next_start_deadline_monotonic_ns "$heartbeat_deadline_ns" \
    cadence_overrun_ns "$heartbeat_overrun_ns"
  if (( heartbeat_overrun_ns > 0 )); then
    append_event "$OBSERVE_LOG" heartbeat_cadence_overrun \
      monotonic_start_ns "$heartbeat_started_ns" \
      monotonic_finish_ns "$heartbeat_finished_ns" \
      deadline_monotonic_ns "$heartbeat_deadline_ns" \
      overrun_ns "$heartbeat_overrun_ns"
  fi
  (( stopping == 0 )) || break
  while (( stopping == 0 )); do
    if deployment_stop_requested && \
        ! session_is_live_owned "$POINCARE_CONTROL_SESSION" && \
        ! session_is_live_owned "$POINCARE_WORKERS_SESSION"; then
      append_event "$OBSERVE_LOG" heartbeat_loop_drained pid "$$"
      exit 0
    fi
    now_ns=$(monotonic_ns)
    (( now_ns < heartbeat_deadline_ns )) || break
    sleep_seconds=$("$HARNESS_PI_PYTHON" -S -P -B - "$now_ns" "$heartbeat_deadline_ns" <<'PY'
import sys

remaining = max(0, int(sys.argv[2]) - int(sys.argv[1])) / 1_000_000_000
print(f"{min(5.0, remaining):.6f}")
PY
    )
    sleep "$sleep_seconds" 7>&-
  done
done
