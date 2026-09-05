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

foreign=0
for session in \
  "$POINCARE_CONTROL_SESSION" \
  "$POINCARE_WORKERS_SESSION" \
  "$POINCARE_OBSERVE_SESSION"
do
  if session_is_live_owned "$session"; then
    session_id=$(session_id_exact "$session")
    tmux display-message -p -t "$session_id" \
      '#{session_name}: owned, windows=#{session_windows}, attached=#{session_attached}, created=#{session_created_string}'
  elif session_is_bootstrap_owned "$session"; then
    printf '%s: owned authenticated bootstrap (launch can recover; stop can terminate)\n' "$session"
  elif session_is_owned "$session"; then
    printf '%s: owned but base pane is not running (launch will recover it)\n' "$session"
  elif session_exists "$session"; then
    printf '%s: FOREIGN (name collision; launcher will not touch it)\n' "$session"
    foreign=1
  else
    printf '%s: stopped\n' "$session"
  fi
done

printf 'repo: branch=%s head=%s dirty_paths=%s\n' \
  "$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" symbolic-ref --quiet --short HEAD 2>/dev/null || printf detached)" \
  "$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)" \
  "$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" status --porcelain | wc -l | tr -d ' ')"

set +e
jobs_active=$(active_job_count)
jobs_status=$?
set -e
if (( jobs_status == 0 )); then
  printf 'runtime: active_jobs=%s configured_ceiling=%s\n' \
    "$jobs_active" "$POINCARE_MAX_LEANSTRAL_JOBS"
  set +e
  utilization_snapshot=$(job_utilization_snapshot)
  utilization_status=$?
  set -e
  if (( utilization_status == 0 )); then
    printf '%s' "$utilization_snapshot" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys

counts = json.load(sys.stdin)
print(
    "pipeline: queued={} executing={} reviewing={} target={} underfilled={}".format(
        counts["queued"], counts["executing"], counts["reviewing"],
        counts["target"], counts["underfilled"]
    )
)
'
  fi
else
  printf 'runtime: active_jobs=unknown (SQLite read failed)\n'
fi

set +e
supervisor_report=$(job_supervisor_report)
supervisor_status=$?
set -e
if [[ -n "$supervisor_report" ]]; then
  printf '%s' "$supervisor_report" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys

report = json.load(sys.stdin)
print(
    "job supervisors: records={} live={} anomalies={}".format(
        len(report["records"]),
        report["live_supervisors"],
        len(report["anomalies"]),
    )
)
for item in report["anomalies"]:
    print("  supervisor anomaly: " + json.dumps(item, sort_keys=True, separators=(",", ":")))
'
else
  printf 'job supervisors: audit unavailable\n'
fi
if (( supervisor_status != 0 )); then
  foreign=1
fi

if deployment_stop_requested; then
  printf 'desired state: stopped (graceful drain requested)\n'
else
  printf 'desired state: running or not initialized\n'
fi

heartbeat_log="$POINCARE_DEPLOY_STATE_DIR/observe/heartbeats.jsonl"
if [[ -s "$heartbeat_log" ]]; then
  printf 'latest heartbeat: '
  tail -n 1 "$heartbeat_log"
else
  printf 'latest heartbeat: none recorded\n'
fi

control_log="$POINCARE_DEPLOY_STATE_DIR/control/events.jsonl"
if [[ -s "$control_log" ]]; then
  printf 'latest control event: '
  tail -n 1 "$control_log"
else
  printf 'latest control event: none recorded\n'
fi

(( foreign == 0 )) || exit 2
