#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  cat <<EOF
Usage: ${0##*/} --job-id ID --lease-owner OWNER --lease-token TOKEN
       [--lean-timeout-seconds SECONDS] [environment-file]

Runs exactly one Harness Pi Job beneath a recorded Linux process-group/session
supervisor. A Job ID can acquire only one write-once supervisor record.
EOF
}

job_id=
lease_owner=
lease_token=
lean_timeout_seconds=900
config_file=$SCRIPT_DIR/.env
config_seen=0
while (( $# > 0 )); do
  case "$1" in
    --job-id)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      job_id=$2
      shift
      ;;
    --lease-owner)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      lease_owner=$2
      shift
      ;;
    --lease-token)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      lease_token=$2
      shift
      ;;
    --lean-timeout-seconds)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      lean_timeout_seconds=$2
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    -*)
      usage >&2
      exit 64
      ;;
    *)
      (( config_seen == 0 )) || { usage >&2; exit 64; }
      config_file=$1
      config_seen=1
      ;;
  esac
  shift
done

[[ "$job_id" =~ ^[a-z0-9][a-z0-9._-]{2,119}$ ]] || die "invalid --job-id"
[[ -n "$lease_owner" && "$lease_owner" != *$'\n'* && "$lease_owner" != *$'\t'* ]] ||
  die "invalid --lease-owner"
[[ "$lease_token" =~ ^[1-9][0-9]*$ ]] || die "--lease-token must be a positive integer"
require_uint_range --lean-timeout-seconds "$lean_timeout_seconds" 1 86400

load_config "$config_file"
ensure_runtime_layout
[[ -x /usr/bin/setsid ]] || die "setsid is required at /usr/bin/setsid"
[[ -x "$HARNESS_PI_FLOCK" ]] || die "flock is required at $HARNESS_PI_FLOCK"
deployment_stop_requested && die "deployment stop is requested; refusing to start a Job supervisor"

reexec_args=(
  --job-id "$job_id"
  --lease-owner "$lease_owner"
  --lease-token "$lease_token"
  --lean-timeout-seconds "$lean_timeout_seconds"
  "$POINCARE_CONFIG_FILE"
)
if [[ "${POINCARE_JOB_SUPERVISOR_SESSION:-0}" != 1 ]]; then
  exec /usr/bin/setsid --fork --wait \
    /usr/bin/env POINCARE_JOB_SUPERVISOR_SESSION=1 "$0" "${reexec_args[@]}"
fi

read -r supervisor_pid supervisor_pgid supervisor_sid supervisor_start_ticks boot_id < <(
  "$HARNESS_PI_PYTHON" -S -P -B - "$$" <<'PY'
import os
import sys
from pathlib import Path

pid = int(sys.argv[1])
raw = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
fields = raw[raw.rfind(")") + 2 :].split()
if len(fields) < 20:
    raise SystemExit("cannot read supervisor process identity")
print(
    pid,
    int(fields[2]),
    int(fields[3]),
    int(fields[19]),
    Path("/proc/sys/kernel/random/boot_id").read_text(encoding="ascii").strip(),
)
PY
)
[[ "$supervisor_pid" == "$supervisor_pgid" && "$supervisor_pid" == "$supervisor_sid" ]] ||
  die "Job supervisor must be its Linux process-group and session leader"
unset POINCARE_JOB_SUPERVISOR_SESSION POINCARE_LIFECYCLE_LOCKED \
  POINCARE_CONTROL_LOCKED POINCARE_WORKERS_LOCKED POINCARE_OBSERVE_LOCKED

# Serialize the final stop-state check and write-once launch record with
# launch.sh/stop.sh. The descriptor is explicitly unlocked and closed as soon
# as the supervised Python child exists, so a stop can then fence it normally.
exec 8> "$POINCARE_DEPLOY_STATE_DIR/lifecycle.lock"
"$HARNESS_PI_FLOCK" 8
deployment_stop_requested && die "deployment stop was requested before Job supervisor admission"

execution_lock=$(job_execution_lock_path "$job_id") ||
  die "could not validate the Job execution lock"
exec {job_execution_fd}<> "$execution_lock"
"$HARNESS_PI_FLOCK" --nonblock "$job_execution_fd" ||
  die "Job $job_id already has an in-flight execution session"

capacity_slot=
capacity_slot_fd=
occupied_slots=0
free_slot_numbers=()
free_slot_fds=()
# Probe every fixed slot, including slots above a newly lowered ceiling. Holding
# all free locks during this census makes the count atomic with admission under
# the lifecycle lock; only the selected reservation survives child launch.
for (( candidate_slot=1; candidate_slot<=4; candidate_slot++ )); do
  candidate_path="$POINCARE_DEPLOY_STATE_DIR/workers/slots/slot-$candidate_slot.lock"
  exec {candidate_slot_fd}<> "$candidate_path"
  if "$HARNESS_PI_FLOCK" --nonblock "$candidate_slot_fd"; then
    free_slot_numbers+=("$candidate_slot")
    free_slot_fds+=("$candidate_slot_fd")
  else
    occupied_slots=$((occupied_slots + 1))
    exec {candidate_slot_fd}>&-
  fi
done
if (( occupied_slots >= POINCARE_MAX_LEANSTRAL_JOBS || ${#free_slot_fds[@]} == 0 )); then
  for unused_fd in "${free_slot_fds[@]}"; do
    exec {unused_fd}>&-
  done
  die "the configured Leanstral Job ceiling is already fully reserved"
fi
capacity_slot=${free_slot_numbers[0]}
capacity_slot_fd=${free_slot_fds[0]}
for (( free_index=1; free_index<${#free_slot_fds[@]}; free_index++ )); do
  unused_fd=${free_slot_fds[$free_index]}
  exec {unused_fd}>&-
done

artifact_dir=$("$HARNESS_PI_PYTHON" -S -P -B - \
  "$POINCARE_STATE_DIR/harness.sqlite3" "$job_id" "$lease_owner" "$lease_token" <<'PY'
import sqlite3
import sys
import time

database, job_id, owner, raw_token = sys.argv[1:]
connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True, timeout=5)
connection.row_factory = sqlite3.Row
row = connection.execute(
    "SELECT state, lease_owner, lease_generation, lease_expires_at, artifact_dir "
    "FROM jobs WHERE job_id = ?",
    (job_id,),
).fetchone()
connection.close()
if row is None:
    raise SystemExit("Job is absent from the runtime store")
if row["state"] != "running":
    raise SystemExit("Job supervisor requires the exact running state")
if row["lease_owner"] != owner or int(row["lease_generation"] or 0) != int(raw_token):
    raise SystemExit("Job supervisor lease owner/token differs from SQLite")
if row["lease_expires_at"] is None or float(row["lease_expires_at"]) <= time.time():
    raise SystemExit("Job supervisor requires an unexpired lease")
print(row["artifact_dir"])
PY
) || die "could not bind supervisor to the active fenced Job"

expected_artifact_dir="$POINCARE_STATE_DIR/jobs/$job_id"
[[ "$(canonical_path "$artifact_dir")" == "$expected_artifact_dir" ]] ||
  die "Job artifact directory is not the canonical Harness location"
[[ -d "$artifact_dir" && ! -L "$artifact_dir" ]] ||
  die "Job artifact directory is missing or redirected"

launch_recorded=0
child_pid=
requested_signal=
finalize_supervisor() {
  local status=$?
  trap - EXIT
  if (( launch_recorded == 0 )); then
    exit "$status"
  fi
  if [[ -n "$requested_signal" ]]; then
    outcome="interrupted_by_$requested_signal"
  else
    outcome=process_exit
  fi
  set +e
  write_supervisor_exit_once "$job_id" "$outcome" "$status" supervisor
  append_event "$POINCARE_DEPLOY_STATE_DIR/workers/events.jsonl" job_supervisor_exited \
    job_id "$job_id" pid "$supervisor_pid" pgid "$supervisor_pgid" \
    exit_code "$status" outcome "$outcome"
  exit "$status"
}
request_supervisor_stop() {
  requested_signal=$1
  if [[ -n "$child_pid" ]] && kill -0 "$child_pid" 2>/dev/null; then
    kill -TERM "$child_pid" 2>/dev/null || true
  elif [[ -z "$child_pid" ]]; then
    exit 143
  fi
}
trap finalize_supervisor EXIT
trap 'request_supervisor_stop HUP' HUP
trap 'request_supervisor_stop INT' INT
trap 'request_supervisor_stop TERM' TERM

record_dir="$POINCARE_DEPLOY_STATE_DIR/workers/supervisors/$job_id"
[[ ! -e "$record_dir" && ! -L "$record_dir" ]] ||
  die "a supervisor record already exists for Job $job_id; create a fresh immutable Job"
staging_root="$POINCARE_DEPLOY_STATE_DIR/workers/staging"
staging_dir="$staging_root/$job_id.$supervisor_pid.$supervisor_start_ticks"
mkdir -- "$staging_dir" || die "could not create private supervisor record staging"
chmod 700 "$staging_dir"

job_argv=(
  "$HARNESS_PI_PYTHON" -S -P -B -m harness.v2.pi run-job
  --job-id "$job_id"
  --lease-owner "$lease_owner"
  --lease-token "$lease_token"
  --state-dir "$POINCARE_STATE_DIR"
  --control-root "$POINCARE_REPO_ROOT"
  --pi-install-manifest "$POINCARE_PI_INSTALL_MANIFEST"
  --pi-dependency-graph "$POINCARE_PI_DEPENDENCY_GRAPH"
  --lean-timeout-seconds "$lean_timeout_seconds"
)

argv_json=$(printf '%s\0' "${job_argv[@]}" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import json
import sys
print(json.dumps([part.decode("utf-8") for part in sys.stdin.buffer.read().split(b"\0")[:-1]]))
')
"$HARNESS_PI_PYTHON" -S -P -B - \
  "$staging_dir/launch.json" "$record_dir" \
  "$job_id" "$lease_owner" "$lease_token" \
  "$supervisor_pid" "$supervisor_start_ticks" "$supervisor_pgid" \
  "$supervisor_sid" "$boot_id" "$POINCARE_CONFIG_FINGERPRINT" \
  "$(utc_now)" "$argv_json" "$POINCARE_REPO_ROOT" "$capacity_slot" <<'PY'
import json
import os
import sys

(
    path,
    final_directory,
    job_id,
    lease_owner,
    lease_token,
    supervisor_pid,
    start_ticks,
    pgid,
    session_id,
    boot_id,
    fingerprint,
    timestamp,
    argv_json,
    cwd,
    capacity_slot,
) = sys.argv[1:]
payload = {
    "schema_version": "poincare.job-supervisor.v2",
    "job_id": job_id,
    "lease_owner": lease_owner,
    "lease_token": int(lease_token),
    "supervisor_pid": int(supervisor_pid),
    "supervisor_start_ticks": int(start_ticks),
    "process_group_id": int(pgid),
    "session_id": int(session_id),
    "boot_id": boot_id,
    "config_fingerprint": fingerprint,
    "started_at": timestamp,
    "argv": json.loads(argv_json),
    "cwd": cwd,
    "capacity_slot": int(capacity_slot),
}
data = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()
descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o400)
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
staging_directory = os.path.dirname(path)
os.rename(staging_directory, final_directory)
for parent in {os.path.dirname(staging_directory), os.path.dirname(final_directory)}:
    descriptor = os.open(parent, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
PY

launch_recorded=1

append_event "$POINCARE_DEPLOY_STATE_DIR/workers/events.jsonl" job_supervisor_started \
  job_id "$job_id" pid "$supervisor_pid" start_ticks "$supervisor_start_ticks" \
  pgid "$supervisor_pgid" lease_owner "$lease_owner" lease_token "$lease_token" \
  capacity_slot "$capacity_slot"

set +e
/usr/bin/env -i \
  HOME="$HOME" LANG="${LANG:-C.UTF-8}" PATH="$PATH" \
  PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 \
  PYTHONDONTWRITEBYTECODE=1 \
  LEANSTRAL_BASE_URL="$LEANSTRAL_BASE_URL" LEANSTRAL_MODEL="$LEANSTRAL_MODEL" \
  LEANSTRAL_MODEL_REVISION="$LEANSTRAL_MODEL_REVISION" \
  HARNESS_PI_BWRAP="$HARNESS_PI_BWRAP" \
  HARNESS_PI_PYTHON="$HARNESS_PI_PYTHON" \
  HARNESS_PI_SYSTEMD_RUN="$HARNESS_PI_SYSTEMD_RUN" \
  HARNESS_PI_GIT="$HARNESS_PI_GIT" \
  HARNESS_PI_GIT_SHA256="$HARNESS_PI_GIT_SHA256" \
  HARNESS_PI_LAKE_CACHE_ROOT="$HARNESS_PI_LAKE_CACHE_ROOT" \
  HARNESS_PI_TOOLCHAIN_ROOTS="$HARNESS_PI_TOOLCHAIN_ROOTS" \
  "${job_argv[@]}" 8>&- &
child_pid=$!
"$HARNESS_PI_FLOCK" -u 8
exec 8>&-
wait "$child_pid"
job_status=$?
if kill -0 "$child_pid" 2>/dev/null; then
  wait "$child_pid"
  job_status=$?
fi
set -e
exit "$job_status"
