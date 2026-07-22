#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  printf 'Usage: %s [environment-file]\n' "${0##*/}"
}

if (( $# > 1 )); then
  usage >&2
  exit 64
fi

load_config "${1:-$SCRIPT_DIR/.env}"
assert_review_control_committed

require_command grep
require_command curl
require_command sleep
require_command readlink
require_command mv
require_command rsync
[[ -x "$POINCARE_CODEX_BIN" ]] || die "Codex is not executable: $POINCARE_CODEX_BIN"
[[ -x /usr/bin/bwrap ]] || die "Bubblewrap is required at /usr/bin/bwrap"
[[ -x /usr/bin/systemd-run ]] || die "systemd-run is required at /usr/bin/systemd-run"
[[ -x /usr/bin/setsid ]] || die "setsid is required at /usr/bin/setsid"
[[ -x /usr/bin/timeout ]] || die "timeout is required at /usr/bin/timeout"
[[ "$HARNESS_PI_PYTHON" == /usr/bin/python3 && -x "$HARNESS_PI_PYTHON" ]] ||
  die "deployment authority requires Python at /usr/bin/python3"
[[ "$HARNESS_PI_FLOCK" == /usr/bin/flock && -x "$HARNESS_PI_FLOCK" ]] ||
  die "deployment authority requires flock at /usr/bin/flock"
for authority in git tmux; do
  if [[ "$authority" == git ]]; then
    authority_path=$HARNESS_PI_GIT
    authority_sha256=$HARNESS_PI_GIT_SHA256
  else
    authority_path=$HARNESS_PI_TMUX
    authority_sha256=$HARNESS_PI_TMUX_SHA256
  fi
  set +e
  authority_payload=$(secure_executable_payload "$authority_path")
  authority_status=$?
  set -e
  (( authority_status == 0 )) ||
    die "configured $authority executable failed preflight re-attestation"
  current_sha256=$(printf '%s' "$authority_payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
    'import json,sys; print(json.load(sys.stdin)["sha256"])')
  [[ "$current_sha256" == "$authority_sha256" ]] ||
    die "configured $authority executable changed during preflight"
done

[[ -d "$POINCARE_REPO_ROOT/.git" ]] ||
  die "POINCARE_REPO_ROOT is not the primary git worktree: $POINCARE_REPO_ROOT"
[[ "$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" rev-parse --show-toplevel)" == "$POINCARE_REPO_ROOT" ]] ||
  die "configured repository root does not match git's top level"

for required_file in \
  AGENTS.md README.md HANDOFF.md docs/PROJECT_MAP.md \
  harness/v2/SPEC.md harness/v2/RUNBOOK.md harness/v2/schemas/task.schema.json \
  harness/v2/schemas/job.schema.json scripts/completion_audit.sh \
  harness/v2/runtime/__main__.py harness/v2/worker/__main__.py \
  harness/v2/pi/__main__.py harness/v2/pi/install.py harness/v2/pi/rpc.py \
  harness/v2/pi/package.json \
  harness/v2/pi/tests/test_pi.py \
  harness/v2/deploy/run-job-supervised.sh \
  harness/v2/deploy/cache-sandbox-smoke.sh \
  harness/v2/deploy/record-lean-cache-provenance.sh \
  harness/v2/deploy/publish-lean-cache.sh \
  harness/v2/deploy/verify-lean-cache.sh \
  scripts/interface_audit.sh scripts/semantic_surface_audit.sh \
  scripts/theorem_contract_audit.sh scripts/root_import_audit.sh \
  scripts/axiom_audit.sh harness/v2/prompts/orchestrator.md \
  harness/v2/prompts/cycle-result.schema.json
do
  [[ -f "$POINCARE_REPO_ROOT/$required_file" ]] ||
    die "required repository file is missing: $required_file"
done

set +e
control_manifest=$(control_surface_manifest)
control_manifest_status=$?
set -e
(( control_manifest_status == 0 )) ||
  die "the complete Harness trust boundary must be tracked, clean, regular, and byte-equal to HEAD"
control_head=$(printf '%s' "$control_manifest" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["git_commit"])')
control_hash=$(printf '%s' "$control_manifest" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["aggregate_sha256"])')
set +e
pi_attestation=$(
  cd "$POINCARE_REPO_ROOT" &&
    PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1 \
      "$HARNESS_PI_PYTHON" -S -P -B - <<'PY'
import json
from pathlib import Path

from harness.v2.pi.integrity import attest_trusted_code

print(json.dumps(attest_trusted_code(Path.cwd(), check_loaded_origins=False), sort_keys=True))
PY
)
pi_attestation_status=$?
set -e
(( pi_attestation_status == 0 )) ||
  die "the integration checkout does not satisfy Pi's clean committed-code attestation"
"$HARNESS_PI_PYTHON" -S -P -B - "$control_manifest" "$pi_attestation" <<'PY' ||
import json
import sys

control = json.loads(sys.argv[1])
pi = json.loads(sys.argv[2])
if control["git_commit"] != pi["git_commit"]:
    raise SystemExit("deploy and Pi attestations name different commits")
control_files = {entry["path"]: entry for entry in control["files"]}
for entry in pi["files"]:
    matching = control_files.get(entry["path"])
    if matching is None or matching["sha256"] != entry["sha256"] or matching["size_bytes"] != entry["size_bytes"]:
        raise SystemExit(f"deploy and Pi attestations disagree for {entry['path']}")
PY
  die "the full deploy trust boundary is inconsistent with Pi's executable-code attestation"
note "Committed control trust boundary verified at $control_head ($control_hash)."

current_branch=$("$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" symbolic-ref --quiet --short HEAD) ||
  die "the integration checkout is detached; refusing to launch"
[[ "$current_branch" == "$POINCARE_INTEGRATION_BRANCH" ]] ||
  die "expected integration branch '$POINCARE_INTEGRATION_BRANCH', found '$current_branch'"

"$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" config user.name >/dev/null ||
  die "git user.name is not configured"
"$HARNESS_PI_GIT" -C "$POINCARE_REPO_ROOT" config user.email >/dev/null ||
  die "git user.email is not configured"

"$POINCARE_CODEX_BIN" --version
"$POINCARE_CODEX_BIN" login status >/dev/null || die "Codex is not authenticated"
expected_pi_version=$(
  cd "$POINCARE_REPO_ROOT"
  PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B - <<'PY'
import json
from pathlib import Path

from harness.v2.pi import PI_VERSION

package = json.loads(Path("harness/v2/pi/package.json").read_text(encoding="utf-8"))
lock = json.loads(Path("harness/v2/pi/package-lock.json").read_text(encoding="utf-8"))
expected = {
    "@earendil-works/pi-coding-agent": PI_VERSION,
    "typebox": "1.1.38",
}
if package.get("dependencies") != expected:
    raise SystemExit("Pi package dependencies are not the exact audited set")
if lock.get("packages", {}).get("", {}).get("dependencies") != expected:
    raise SystemExit("Pi lock root and package dependency pins disagree")
package_version = package["dependencies"]["@earendil-works/pi-coding-agent"]
if package_version != PI_VERSION:
    raise SystemExit("Pi package pin and executor pin disagree")
print(PI_VERSION)
PY
) || die "could not read the repository's pinned Pi version"
set +e
pi_install_report=$(
  cd "$POINCARE_REPO_ROOT" &&
    PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1 \
      "$HARNESS_PI_PYTHON" -S -P -B - \
        "$POINCARE_PI_INSTALL_MANIFEST" "$POINCARE_PI_DEPENDENCY_GRAPH" <<'PY'
import json
import sys

from harness.v2.pi.install import verify_sealed_install_files

manifest = verify_sealed_install_files(
    sys.argv[1], sys.argv[2], expected_node_executable="/usr/bin/node"
)
if manifest["node"]["path"] != "/usr/bin/node":
    raise SystemExit("production Pi must use the exact attested /usr/bin/node")
print(
    json.dumps(
        {
            "package": manifest["package"],
            "tree_sha256": manifest["tree"]["sha256"],
            "node": {
                "minimum_version": manifest["node"]["minimum_version"],
                "path": manifest["node"]["path"],
                "sha256": manifest["node"]["sha256"],
                "version": manifest["node"]["version"],
            },
            "cli_sha256": manifest["cli_js"]["sha256"],
        },
        sort_keys=True,
        separators=(",", ":"),
    )
)
PY
)
pi_install_status=$?
set -e
(( pi_install_status == 0 )) ||
  die "the sealed Pi manifest/dependency graph does not match the complete live installation"
pi_verified_version=$(printf '%s' "$pi_install_report" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["package"]["version"])')
[[ "$pi_verified_version" == "$expected_pi_version" ]] ||
  die "sealed Pi version mismatch: expected $expected_pi_version, found $pi_verified_version"
pi_tree_sha256=$(printf '%s' "$pi_install_report" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["tree_sha256"])')
pi_verified_node_version=$(printf '%s' "$pi_install_report" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["node"]["version"])')
note "Complete sealed Pi $pi_verified_version installation verified with exact /usr/bin/node $pi_verified_node_version ($pi_tree_sha256)."

mv --version 2>/dev/null | grep 'GNU coreutils' >/dev/null ||
  die "the atomic immutable-cache publisher requires GNU mv"
[[ -d "$POINCARE_PI_LAKE_CACHE_ROOT" && ! -L "$POINCARE_PI_LAKE_CACHE_ROOT" ]] ||
  die "immutable Lake cache root must be an existing real directory"
[[ -O "$POINCARE_PI_LAKE_CACHE_ROOT" && -w "$POINCARE_PI_LAKE_CACHE_ROOT" ]] ||
  die "immutable Lake cache root must be owned and writable by the current user"
[[ -d "$POINCARE_PI_TOOLCHAIN_ROOT" && ! -L "$POINCARE_PI_TOOLCHAIN_ROOT" ]] ||
  die "Lean toolchain root must be an existing real directory"
for executable in lean lake; do
  [[ -x "$POINCARE_PI_TOOLCHAIN_ROOT/bin/$executable" ]] ||
    die "configured Lean toolchain lacks executable bin/$executable"
done
"$HARNESS_PI_PYTHON" -S -P -B - "$POINCARE_PI_TOOLCHAIN_ROOT" <<'PY' ||
import os
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve(strict=True)
for name in ("lean", "lake"):
    executable = (root / "bin" / name).resolve(strict=True)
    try:
        executable.relative_to(root)
    except ValueError as exc:
        raise SystemExit(f"toolchain {name} resolves outside the configured root") from exc
    with executable.open("rb") as stream:
        if stream.read(4) != b"\x7fELF":
            raise SystemExit(f"toolchain {name} is not a native ELF executable")
PY
  die "configured Lean toolchain identity check failed"

bwrap_layout=(--ro-bind /usr /usr)
for host_entry in bin lib lib64 sbin; do
  if [[ -L "/$host_entry" ]]; then
    bwrap_layout+=(--symlink "$(readlink "/$host_entry")" "/$host_entry")
  elif [[ -d "/$host_entry" ]]; then
    bwrap_layout+=(--ro-bind "/$host_entry" "/$host_entry")
  fi
done

host_user_namespace=$(readlink /proc/self/ns/user) || die "cannot identify the host user namespace"
host_pid_namespace=$(readlink /proc/self/ns/pid) || die "cannot identify the host PID namespace"
host_mount_namespace=$(readlink /proc/self/ns/mnt) || die "cannot identify the host mount namespace"
host_network_namespace=$(readlink /proc/self/ns/net) || die "cannot identify the host network namespace"

readonly BWRAP_SMOKE=$(cat <<'PY'
import os
from pathlib import Path
import sys

for namespace, outside in zip(("user", "pid", "mnt", "net"), sys.argv[1:], strict=True):
    inside = os.readlink(f"/proc/self/ns/{namespace}")
    if inside == outside:
        raise SystemExit(f"{namespace} namespace is not isolated")

numeric_pids = [entry for entry in Path("/proc").iterdir() if entry.name.isdigit()]
if len(numeric_pids) > 8:
    raise SystemExit("PID namespace is not isolated")
uid_map = Path("/proc/self/uid_map").read_text(encoding="utf-8")
if "4294967295" in uid_map:
    raise SystemExit("user namespace is not isolated")
mounts = Path("/proc/mounts").read_text(encoding="utf-8")
mount_rows = list(map(str.split, mounts.splitlines()))
if not any(parts[1] == "/tmp" and parts[2] == "tmpfs" for parts in mount_rows):
    raise SystemExit("/tmp is not a private tmpfs")
if not any(parts[1] == "/usr" and "ro" in parts[3].split(",") for parts in mount_rows):
    raise SystemExit("/usr is not mounted read-only")
if Path("/etc/passwd").exists() or Path("/home").exists() or Path("/srv").exists():
    raise SystemExit("host filesystem escaped the minimal read-only view")
probe = Path("/tmp/poincare-bwrap-smoke")
probe.write_text("ok", encoding="utf-8")
if probe.read_text(encoding="utf-8") != "ok":
    raise SystemExit("private /tmp is not writable")
routes = Path("/proc/net/route").read_text(encoding="utf-8").splitlines()
if len(routes) > 1:
    raise SystemExit("private network namespace unexpectedly has an IPv4 route")
PY
)

/usr/bin/bwrap \
  --die-with-parent --new-session --unshare-all --unshare-user --disable-userns \
  --assert-userns-disabled --cap-drop ALL \
  "${bwrap_layout[@]}" --proc /proc --dev /dev \
  --size "$((256 * 1024 * 1024))" --tmpfs /tmp --remount-ro / --chdir /tmp \
  --clearenv --setenv PATH /usr/bin:/bin \
  /usr/bin/python3 -I -c "$BWRAP_SMOKE" \
    "$host_user_namespace" "$host_pid_namespace" \
    "$host_mount_namespace" "$host_network_namespace" >/dev/null 2>&1 ||
  die "Bubblewrap deny-by-default namespace smoke failed"
note "Bubblewrap user/PID/mount/network isolation verified."

/usr/bin/systemd-run --user --scope --quiet --collect \
  --property=MemoryMax=$((256 * 1024 * 1024)) \
  --property=MemorySwapMax=0 --property=TasksMax=16 \
  --property=CPUQuota=100% -- /bin/true >/dev/null 2>&1 ||
  die "the user systemd scope required for bounded Lean checks is unavailable"
note "User systemd cgroup scopes for bounded Lean checks verified."

/usr/bin/setsid --help 2>&1 | grep -- '--fork' >/dev/null && \
  /usr/bin/setsid --help 2>&1 | grep -- '--wait' >/dev/null ||
  die "util-linux setsid with --fork and --wait is required for Job supervision"
(
  cd "$POINCARE_REPO_ROOT"
  PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B -m harness.v2.pi --help
  PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B -m harness.v2.pi run-job --help
) >/dev/null || die "the bounded Pi Job executor entrypoint is unavailable"

(
  cd "$POINCARE_REPO_ROOT"
  "$POINCARE_PI_TOOLCHAIN_ROOT/bin/lake" env \
    "$POINCARE_PI_TOOLCHAIN_ROOT/bin/lean" --version
) || die "the repository's pinned Lean toolchain is unavailable"

"$SCRIPT_DIR/verify-lean-cache.sh" "$POINCARE_CONFIG_FILE" >/dev/null ||
  die "the current HEAD has no valid immutable Lake cache snapshot"
note "Current per-base immutable Lake cache manifest and content verified."
"$SCRIPT_DIR/cache-sandbox-smoke.sh" "$POINCARE_CONFIG_FILE" >/dev/null ||
  die "the immutable cache failed its real Bubblewrap Lean smoke"
note "Current immutable cache elaborated a real Poincare file through the exact worker sandbox."

available_kib=$(df -Pk "$POINCARE_REPO_ROOT" | awk 'NR == 2 {print $4}')
[[ "$available_kib" =~ ^[0-9]+$ ]] || die "could not determine free repository disk space"
required_kib=$(( POINCARE_MIN_FREE_GIB * 1024 * 1024 ))
(( available_kib >= required_kib )) ||
  die "repository volume has less than ${POINCARE_MIN_FREE_GIB} GiB free"

mkdir -p -- "$POINCARE_WORKTREE_ROOT"
[[ -O "$POINCARE_WORKTREE_ROOT" ]] ||
  die "worktree root is not owned by the current user: $POINCARE_WORKTREE_ROOT"
[[ -w "$POINCARE_WORKTREE_ROOT" ]] ||
  die "worktree root is not writable: $POINCARE_WORKTREE_ROOT"
worktree_available_kib=$(df -Pk "$POINCARE_WORKTREE_ROOT" | awk 'NR == 2 {print $4}')
[[ "$worktree_available_kib" =~ ^[0-9]+$ ]] ||
  die "could not determine free worktree disk space"
(( worktree_available_kib >= required_kib )) ||
  die "worktree volume has less than ${POINCARE_MIN_FREE_GIB} GiB free"

ensure_runtime_layout
note "Initializing or migrating the restart-safe Harness v2 store."
(
  runtime_cli \
    --worktree-root "$POINCARE_WORKTREE_ROOT" \
    --integration-root "$POINCARE_REPO_ROOT" \
    init
) >/dev/null || die "Harness v2 runtime initialization failed"

set +e
supervisor_report=$(job_supervisor_report)
supervisor_status=$?
set -e
if (( supervisor_status != 0 )); then
  printf 'Job supervisor preflight report: %s\n' "$supervisor_report" >&2
  die "recorded Job supervisor PID/start-time/PGID state is inconsistent or orphaned"
fi
supervisor_live=$(printf '%s' "$supervisor_report" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["live_supervisors"])')
note "Job supervisor state verified: $supervisor_live authenticated live supervisor(s)."
dispatch_state=$(deployment_dispatch_state) ||
  die "durable dispatch state is unreadable after runtime initialization"
if [[ "$dispatch_state" == stopped ]]; then
  jobs_active=$(active_job_count) ||
    die "could not count active Jobs before restarting a stopped deployment"
  if [[ "$jobs_active" != 0 || "$supervisor_live" != 0 ]]; then
    die "a stopped deployment cannot relaunch until all active Jobs and supervisors are reaped; use authenticated interrupt stop"
  fi
  note "Stopped deployment is fully drained and may advance to a new dispatch generation."
fi

(
  cd "$POINCARE_REPO_ROOT"
  PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1 \
    "$HARNESS_PI_PYTHON" -S -P -B -m harness.v2.worker health
) >/dev/null || die "the bounded worker endpoint identity check failed"

for session in \
  "$POINCARE_CONTROL_SESSION" \
  "$POINCARE_WORKERS_SESSION" \
  "$POINCARE_OBSERVE_SESSION"
do
  assert_session_available_or_owned "$session"
done

note "Checking the pinned Leanstral served model ID (endpoint URL is not printed)."
endpoint_models_healthy || die "Leanstral /models did not expose the configured served model ID"
note "Running one bounded Leanstral chat smoke."
endpoint_chat_smoke || die "Leanstral chat smoke failed"

note "Preflight passed from one clean attested commit: Codex, Lean, git, tmux, disk, repository contracts, and Leanstral are ready."
