#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

if (( $# > 1 )); then
  printf 'Usage: %s [environment-file]\n' "${0##*/}" >&2
  exit 64
fi

config_file=${1:-$SCRIPT_DIR/.env}
load_config "$config_file"
unset POINCARE_LIFECYCLE_LOCKED POINCARE_CONTROL_LOCKED \
  POINCARE_WORKERS_LOCKED POINCARE_OBSERVE_LOCKED \
  POINCARE_JOB_SUPERVISOR_SESSION
ensure_runtime_layout
[[ -x "$HARNESS_PI_FLOCK" ]] || die "flock is required at $HARNESS_PI_FLOCK"

exec 7<> "$POINCARE_DEPLOY_STATE_DIR/lifecycle.lock"
"$HARNESS_PI_FLOCK" --nonblock 7 ||
  die "another authenticated Harness lifecycle operation holds the lock"

"$SCRIPT_DIR/preflight.sh" "$POINCARE_CONFIG_FILE" 7>&-
load_config "$POINCARE_CONFIG_FILE"
ensure_runtime_layout

for session in \
  "$POINCARE_CONTROL_SESSION" \
  "$POINCARE_WORKERS_SESSION" \
  "$POINCARE_OBSERVE_SESSION"
do
  assert_session_available_or_owned "$session"
done

dispatch_before_launch=$(deployment_dispatch_state) ||
  die "could not read durable dispatch state before launch"
if [[ "$dispatch_before_launch" == stopped ]]; then
  [[ "$(active_job_count)" == 0 ]] ||
    die "refusing stopped-to-running transition while an old-generation Job remains active"
fi
dispatch_advanced=0
launch_complete=0
rollback_failed_launch() {
  local status=$?
  trap - EXIT
  if (( launch_complete == 0 && dispatch_advanced == 1 )); then
    set +e
    set_deployment_desired_state stopped \
      "deploy-launch-rollback:$POINCARE_CONFIG_FINGERPRINT"
    append_event "$POINCARE_DEPLOY_STATE_DIR/events.jsonl" launcher_failed_closed \
      exit_code "$status"
  fi
  exit "$status"
}
trap rollback_failed_launch EXIT
[[ "$dispatch_before_launch" == stopped ]] && dispatch_advanced=1
set_deployment_desired_state running \
  "deploy-launch:$POINCARE_CONFIG_FINGERPRINT"

(start_or_recover_session "$POINCARE_WORKERS_SESSION" sentinel "$SCRIPT_DIR/worker-plane.sh") 7>&-
(start_or_recover_session "$POINCARE_OBSERVE_SESSION" heartbeat "$SCRIPT_DIR/heartbeat-loop.sh") 7>&-
(start_or_recover_session "$POINCARE_CONTROL_SESSION" orchestrator "$SCRIPT_DIR/codex-cycle.sh") 7>&-

for session in \
  "$POINCARE_CONTROL_SESSION" \
  "$POINCARE_WORKERS_SESSION" \
  "$POINCARE_OBSERVE_SESSION"
do
  session_is_live_owned "$session" || die "Harness session failed live identity validation: $session"
done

append_event "$POINCARE_DEPLOY_STATE_DIR/events.jsonl" launcher_started \
  head "$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse HEAD)"

launch_complete=1
trap - EXIT
note "Harness v2 is running. Use $SCRIPT_DIR/status.sh $POINCARE_CONFIG_FILE for evidence-backed status."
