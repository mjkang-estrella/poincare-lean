#!/bin/bash
# Acceptance gate for worker output (the only judge).
# Usage: gate.sh <worktree> <module> [decl ...]
# Exit 0 = accepted. Checks: forbidden tokens in the module file, whitespace,
# `lake build <module>`, and a module-wide axiom scan (every declaration of the
# module must use only propext, Classical.choice, Quot.sound); extra decl names,
# if given, are additionally probed with #print axioms.
set -uo pipefail
WT="$1"; MODULE="$2"; shift 2
cd "$WT" || exit 2
FILE="$(echo "$MODULE" | tr . /).lean"
echo "=== GATE: forbidden tokens in $FILE ==="
if grep -nE '\b(sorry|admit)\b|^\s*axiom\b|native_decide|\bopaque\b|\bpostulate\b' "$FILE"; then echo "REJECT: forbidden token"; exit 3; fi
echo "=== GATE: git diff --check ==="; git diff --check HEAD -- . || { echo "REJECT: whitespace"; exit 3; }
echo "=== GATE: lake build $MODULE ==="
OUT=$(lake build "$MODULE" 2>&1); RC=$?; echo "$OUT" | tail -5
if [ $RC -ne 0 ] || echo "$OUT" | grep -qE '^error:|error: '; then echo "REJECT: build failed"; exit 4; fi
if echo "$OUT" | grep -q "$FILE.*warning: declaration uses 'sorry'"; then echo "REJECT: sorry warning"; exit 4; fi
echo "=== GATE: module-wide axiom scan ==="
SCAN=$(mktemp /tmp/gate_scan_XXXX.lean)
cat > "$SCAN" <<LEAN
import $MODULE
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? \`$MODULE | throwError "module not found"
  let mut bad : Array String := #[]
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      for a in axs do
        if a != \`\`propext && a != \`\`Classical.choice && a != \`\`Quot.sound then
          bad := bad.push s!"{n} uses {a}"
  logInfo m!"GATE_SCAN declarations={count} nonstandard={bad}"
LEAN
SCANOUT=$(LEAN_NUM_THREADS=1 lake env lean "$SCAN" 2>&1); echo "$SCANOUT" | grep -E "GATE_SCAN|error" ; rm -f "$SCAN"
if ! echo "$SCANOUT" | grep -q "GATE_SCAN declarations=[0-9]* nonstandard=\[\]"; then echo "REJECT: nonstandard axiom or scan failure"; exit 5; fi
if [ $# -gt 0 ]; then
  echo "=== GATE: #print axioms (named) ==="
  AX=$(mktemp /tmp/gate_axioms_XXXX.lean)
  { echo "import $MODULE"; for t in "$@"; do echo "#print axioms $t"; done; } > "$AX"
  AXOUT=$(LEAN_NUM_THREADS=1 lake env lean "$AX" 2>&1); echo "$AXOUT"; rm -f "$AX"
  if echo "$AXOUT" | grep -qE 'sorryAx|error'; then echo "REJECT: axiom probe"; exit 5; fi
fi
echo "=== GATE: PASS ==="
