#!/bin/bash
# Acceptance gate for worker output (the only judge). Usage: gate.sh <worktree> <module> [decl ...]; exit 0 = accepted.
set -uo pipefail
WT="$1"; MODULE="$2"; shift 2
cd "$WT" || exit 2
FILE="$(echo "$MODULE" | tr . /).lean"
echo "=== GATE: forbidden tokens in $FILE ==="
if grep -nE '\b(sorry|admit)\b|^\s*axiom\b|native_decide|\bopaque\b|\bpostulate\b' "$FILE"; then echo "REJECT: forbidden token"; exit 3; fi
echo "=== GATE: git diff --check ==="; git diff --check HEAD -- . || { echo "REJECT: whitespace"; exit 3; }
echo "=== GATE: lake build $MODULE ==="
OUT=$(lake build "$MODULE" 2>&1); RC=$?; echo "$OUT" | tail -25
if [ $RC -ne 0 ] || echo "$OUT" | grep -qE '^error:|error: '; then echo "REJECT: build failed"; exit 4; fi
if echo "$OUT" | grep -q "$FILE.*warning: declaration uses 'sorry'"; then echo "REJECT: sorry warning"; exit 4; fi
if [ $# -gt 0 ]; then
  echo "=== GATE: #print axioms ==="
  AX=$(mktemp /tmp/gate_axioms_XXXX.lean)
  { echo "import $MODULE"; for t in "$@"; do echo "#print axioms $t"; done; } > "$AX"
  AXOUT=$(LEAN_NUM_THREADS=1 lake env lean "$AX" 2>&1); echo "$AXOUT"; rm -f "$AX"
  if echo "$AXOUT" | grep -qE 'sorryAx|error'; then echo "REJECT: axiom audit"; exit 5; fi
  if echo "$AXOUT" | grep -oE 'depends on axioms: \[[^]]*\]' | sed -E 's/.*\[|\]//g' | tr ',' '\n' | tr -d " '" | grep -v '^$' | grep -vxE "propext|Classical\.choice|Quot\.sound" | grep -q .; then echo "REJECT: non-core axiom"; exit 5; fi
fi
echo "=== GATE: PASS ==="
