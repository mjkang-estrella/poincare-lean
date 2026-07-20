#!/usr/bin/env bash

set -euo pipefail

readonly SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# shellcheck source=common.sh
source "$SCRIPT_DIR/common.sh"

# This is only the exact declaration/type/axiom prerequisite. It deliberately
# does not claim project completion; codex-cycle.sh additionally requires the
# full completion audit and one clean, stable integration HEAD.

if (( $# > 1 )); then
  printf 'Usage: %s [environment-file]\n' "${0##*/}" >&2
  exit 64
fi

load_config "${1:-$SCRIPT_DIR/.env}"

probe_source=$(cat <<'LEAN'
import Poincare

#check (Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement)
#print axioms Poincare.poincare_conjecture
LEAN
)

set +e
probe_output=$(
  cd "$POINCARE_REPO_ROOT" &&
    printf '%s\n' "$probe_source" |
      LEAN_NUM_THREADS=1 "$POINCARE_PI_TOOLCHAIN_ROOT/bin/lake" env \
        "$POINCARE_PI_TOOLCHAIN_ROOT/bin/lean" --stdin 2>&1
)
probe_status=$?
set -e

if (( probe_status != 0 )); then
  if [[ "$probe_output" == *"Unknown identifier"* || "$probe_output" == *"Unknown constant"* ]]; then
    printf 'EXACT_DECLARATION_PROBE=absent\n'
    exit 3
  fi
  printf 'EXACT_DECLARATION_PROBE=invalid\n'
  printf '%s\n' "$probe_output" >&2
  exit 4
fi

if ! printf '%s\n' "$probe_output" | "$HARNESS_PI_PYTHON" -S -P -B -c '
import re
import sys

text = sys.stdin.read()
if "does not depend on any axioms" in text:
    raise SystemExit(0)
match = re.search(r"depends on axioms:\s*\[(.*?)\]", text, re.S)
if match is None:
    raise SystemExit(2)
axioms = {part.strip() for part in match.group(1).replace("\n", " ").split(",") if part.strip()}
allowed = {"propext", "Classical.choice", "Quot.sound"}
raise SystemExit(0 if axioms <= allowed else 1)
'; then
  printf 'EXACT_DECLARATION_PROBE=nonstandard_axioms\n'
  printf '%s\n' "$probe_output" >&2
  exit 5
fi

printf 'EXACT_DECLARATION_PROBE=verified\n'
printf '%s\n' "$probe_output" >&2
