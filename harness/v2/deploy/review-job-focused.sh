#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

usage() {
  printf 'Usage: %s JOB_ID --reviewer CODEX_REVIEWER [--timeout-seconds N] [environment-file]\n' "${0##*/}"
}

(( $# >= 3 )) || { usage >&2; exit 64; }
job_id=$1
shift
reviewer=
timeout_seconds=900
while (( $# > 0 )); do
  case "$1" in
    --reviewer)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      reviewer=$2
      shift 2
      ;;
    --timeout-seconds)
      (( $# >= 2 )) || { usage >&2; exit 64; }
      timeout_seconds=$2
      shift 2
      ;;
    *)
      break
      ;;
  esac
done
[[ -n "$reviewer" ]] || { usage >&2; exit 64; }
(( $# <= 1 )) || { usage >&2; exit 64; }

load_config "${1:-$SCRIPT_DIR/.env}"
assert_review_control_committed

cd "$POINCARE_DEPLOY_CODE_ROOT"
PYTHONPATH="$POINCARE_DEPLOY_CODE_ROOT" PYTHONNOUSERSITE=1 \
  PYTHONDONTWRITEBYTECODE=1 \
  "$HARNESS_PI_PYTHON" -S -P -B -m harness.v2.deploy.focused_review \
    "$job_id" --reviewer "$reviewer" --timeout-seconds "$timeout_seconds"
