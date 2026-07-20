#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  cat <<EOF
Usage: ${0##*/} [--interrupt-owned-jobs] [environment-file]

By default, stop records a graceful drain request and kills no process.
The override interrupts only stable-ID, marker-authenticated Harness sessions.
EOF
}

interrupt_owned_jobs=0
config_file=$SCRIPT_DIR/.env
config_seen=0
while (( $# > 0 )); do
  case "$1" in
    --interrupt-owned-jobs)
      interrupt_owned_jobs=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    -* )
      usage >&2
      exit 64
      ;;
    *)
      (( config_seen == 0 )) || {
        usage >&2
        exit 64
      }
      config_file=$1
      config_seen=1
      ;;
  esac
  shift
done

load_config "$config_file"
unset POINCARE_LIFECYCLE_LOCKED POINCARE_CONTROL_LOCKED \
  POINCARE_WORKERS_LOCKED POINCARE_OBSERVE_LOCKED \
  POINCARE_JOB_SUPERVISOR_SESSION
ensure_runtime_layout
[[ -x "$HARNESS_PI_FLOCK" ]] || die "flock is required at $HARNESS_PI_FLOCK"

exec 7<> "$POINCARE_DEPLOY_STATE_DIR/lifecycle.lock"
"$HARNESS_PI_FLOCK" --nonblock 7 ||
  die "another authenticated Harness lifecycle operation holds the lock"

sessions=(
  "$POINCARE_CONTROL_SESSION" \
  "$POINCARE_WORKERS_SESSION" \
  "$POINCARE_OBSERVE_SESSION"
)
session_ids=()
for session in "${sessions[@]}"; do
  if session_id=$(session_id_exact "$session"); then
    session_id_is_owned_or_bootstrap "$session_id" "$session" ||
      die "tmux session '$session' does not match this config, role, and base pane; refusing to touch it"
    session_ids+=("$session_id")
  else
    session_ids+=("")
  fi
done

# This SQLite transition shares BEGIN IMMEDIATE serialization with every Job
# claim. Once it commits, no later claim or preparing->running transition can
# pass, while the lifecycle lock prevents a supervisor from being admitted.
set_deployment_desired_state stopped \
  "deploy-stop:$POINCARE_CONFIG_FINGERPRINT"
append_event "$POINCARE_DEPLOY_STATE_DIR/events.jsonl" launcher_stop_requested \
  interrupt_owned_jobs "$interrupt_owned_jobs"

if (( interrupt_owned_jobs == 0 )); then
  note "Recorded a graceful stop request. Control will stop between cycles; workers drain only after SQLite reports no active Jobs; observe exits last."
  note "No process was killed. Re-run status.sh to watch the drain."
  exit 0
fi

set +e
supervisor_report=$(job_supervisor_report)
supervisor_status=$?
set -e
printf '%s' "$supervisor_report" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys

report = json.load(sys.stdin)
allowed = {
    "active_job_lease_expired",
    "active_job_without_supervisor",
    "active_job_supervisor_not_live",
    "supervisor_missing_exit",
    "orphaned_supervisor_process_group",
    "exited_supervisor_still_live",
}
unexpected = [item for item in report["anomalies"] if item.get("code") not in allowed]
if unexpected:
    for item in unexpected:
        print(f"ERROR: Job supervisor anomaly blocks interruption: {item}", file=sys.stderr)
    raise SystemExit(2)
' || die "active Jobs are not all bound to authenticated live supervisors; durable stop remains in force and no process was touched"
(( supervisor_status == 0 || supervisor_status == 2 )) ||
  die "could not audit Job supervisors; durable stop remains in force and no process was touched"

supervised_jobs=()
while IFS= read -r supervised_job_row; do
  supervised_jobs+=("$supervised_job_row")
done < <(
  printf '%s' "$supervisor_report" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys

report = json.load(sys.stdin)
for record in report["records"]:
    # An immutable exit record is evidence, not proof that every descendant in
    # the authenticated process group is dead. Include terminal Jobs and
    # exit-recorded supervisors whenever the recorded PGID still has members.
    if not (record["live"] or record["group_members"]):
        continue
    fields = [
        record["job_id"],
        str(record["supervisor_pid"]),
        str(record["supervisor_start_ticks"]),
        str(record["process_group_id"]),
        str(record["session_id"]),
        record["boot_id"],
    ]
    if any("\t" in str(value) or "\n" in str(value) for value in fields):
        raise SystemExit("unsafe supervisor field")
    print("\t".join(fields))
'
)

for row in "${supervised_jobs[@]}"; do
  IFS=$'\t' read -r job_id supervisor_pid supervisor_start_ticks \
    supervisor_pgid supervisor_sid supervisor_boot_id \
    <<< "$row"
  set +e
  signal_recorded_supervisor_group \
    "$supervisor_pid" "$supervisor_start_ticks" "$supervisor_pgid" \
    "$supervisor_sid" "$supervisor_boot_id" TERM
  signal_status=$?
  set -e
  if (( signal_status == 0 )); then
    append_event "$POINCARE_DEPLOY_STATE_DIR/workers/events.jsonl" job_supervisor_signalled \
      job_id "$job_id" pid "$supervisor_pid" pgid "$supervisor_pgid" signal TERM
  fi

  deadline=$((SECONDS + 15))
  supervisor_live=1
  while (( SECONDS < deadline )); do
    set +e
    current_report=$(job_supervisor_report)
    set -e
    supervisor_live=$(printf '%s' "$current_report" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys
job_id = sys.argv[1]
report = json.load(sys.stdin)
print(
    1
    if any(
        item["job_id"] == job_id and (item["live"] or item["group_members"])
        for item in report["records"]
    )
    else 0
)
' "$job_id")
    [[ "$supervisor_live" == 1 ]] || break
    sleep 1
  done
  if [[ "$supervisor_live" == 1 ]]; then
    signal_recorded_supervisor_group \
      "$supervisor_pid" "$supervisor_start_ticks" "$supervisor_pgid" \
      "$supervisor_sid" "$supervisor_boot_id" KILL ||
      die "Job $job_id was fenced, but its authenticated supervisor identity changed before forced termination"
    append_event "$POINCARE_DEPLOY_STATE_DIR/workers/events.jsonl" job_supervisor_signalled \
      job_id "$job_id" pid "$supervisor_pid" pgid "$supervisor_pgid" signal KILL
    sleep 1
  fi
  set +e
  final_report=$(job_supervisor_report)
  set -e
  still_live=$(printf '%s' "$final_report" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys
job_id = sys.argv[1]
report = json.load(sys.stdin)
print(1 if any(item["job_id"] == job_id and (item["live"] or item["group_members"]) for item in report["records"]) else 0)
' "$job_id")
  [[ "$still_live" == 0 ]] ||
    die "Job $job_id was fenced, but its recorded process group still has live members"
  write_supervisor_exit_once "$job_id" interrupted_by_deploy_stop null deploy-stop
done

# Only after every authenticated process group has been reaped may runtime
# state become terminal and release its file scopes. The runtime command takes
# the same per-Job execution lock nonblocking, so an unrecorded in-flight
# broker fails closed here instead of racing terminalization.
stop_actor="deploy-stop:$POINCARE_CONFIG_FINGERPRINT"
jobs_to_interrupt=()
while IFS= read -r active_row; do
  jobs_to_interrupt+=("$active_row")
done < <(active_job_rows)
for row in "${jobs_to_interrupt[@]}"; do
  IFS=$'\t' read -r job_id prior_state _lease_owner _lease_token <<< "$row"
  set +e
  runtime_cli job interrupt-stopped "$job_id" \
    --actor "$stop_actor" \
    --exit-reason "operator requested authenticated deploy stop interruption" \
    >/dev/null
  interrupt_status=$?
  set -e
  if (( interrupt_status != 0 )); then
    current_state=$(job_runtime_state "$job_id") ||
      die "could not re-read Job $job_id after stop interruption failed"
    case "$current_state" in
      passed|rejected|blocked|interrupted) ;;
      *) die "could not terminalize reaped Job $job_id; it remains $current_state" ;;
    esac
  fi
  append_event "$POINCARE_DEPLOY_STATE_DIR/workers/events.jsonl" job_fenced_for_stop \
    job_id "$job_id" prior_state "$prior_state"
done

set +e
post_interrupt_report=$(job_supervisor_report)
post_interrupt_status=$?
set -e
(( post_interrupt_status == 0 )) || {
  printf 'ERROR: post-interruption supervisor audit: %s\n' "$post_interrupt_report" >&2
  die "Job interruption evidence is inconsistent; tmux sessions remain untouched"
}
[[ "$(active_job_count)" == 0 ]] ||
  die "a new active Job appeared during stop; tmux sessions remain untouched"

for index in "${!sessions[@]}"; do
  session=${sessions[$index]}
  session_id=${session_ids[$index]}
  if [[ -z "$session_id" ]]; then
    note "$session was already stopped"
    continue
  fi
  if session_id_is_owned_or_bootstrap "$session_id" "$session"; then
    tmux kill-session -t "$session_id"
    note "interrupted marker-authenticated session $session; append-only evidence was preserved and active Jobs were recorded interrupted"
  else
    note "$session changed or exited after validation; it was not touched"
  fi
done
