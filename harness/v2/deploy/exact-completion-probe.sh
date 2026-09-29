#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

# This is only the exact declaration/type/axiom prerequisite. It deliberately
# does not claim project completion; codex-cycle.sh additionally requires the
# full completion audit and one clean, stable integration HEAD.

fresh=1
if [[ "${1:-}" == --reuse-negative ]]; then
  fresh=0
  shift
elif [[ "${1:-}" == --fresh ]]; then
  shift
fi

if (( $# > 1 )) || [[ "${1:-}" == --* ]]; then
  printf 'Usage: %s [--fresh|--reuse-negative] [environment-file]\n' "${0##*/}" >&2
  exit 64
fi

load_config "${1:-$SCRIPT_DIR/.env}"
# The pinned executable and its libraries, rather than ambient Lake/Lean
# overrides, define both the probe and its reusable input identity.
unset LAKE_OVERRIDE_LEAN LAKE_OVERRIDE_LAKE LEAN_SYSROOT LEAN

# Ordinary and final probes run fresh. Negative reuse is explicitly opt-in:
# hashing mutable import artifacts can cost more than loading them with Lean.
probe_argv=(
  "$HARNESS_PI_PYTHON" -S -P -B "$SCRIPT_DIR/negative_probe_cache.py"
  --root "$POINCARE_REPO_ROOT"
  --toolchain-root "$POINCARE_PI_TOOLCHAIN_ROOT"
  --config "$POINCARE_CONFIG_FILE"
  --config-fingerprint "$POINCARE_CONFIG_FINGERPRINT"
)
if (( fresh )); then
  probe_argv+=(--fresh)
fi
exec "${probe_argv[@]}"
