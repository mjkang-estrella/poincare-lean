#!/bin/bash
# Acceptance gate for worker output (the only judge).
# Usage: gate.sh <worktree> <module> [decl ...]
# Exit 0 = accepted. Checks: forbidden tokens in the module file, whitespace,
# `lake build <module>`, and a module-wide axiom scan (every declaration of the
# module, including internal declarations, must use only propext,
# Classical.choice, Quot.sound); extra decl names are checked in the same Lean
# invocation and printed with #print axioms.
set -uo pipefail
if [ $# -lt 2 ]; then echo "Usage: gate.sh <worktree> <module> [decl ...]" >&2; exit 2; fi
WT="$1"; MODULE="$2"; shift 2
cd "$WT" || exit 2
FILE="$(echo "$MODULE" | tr . /).lean"
echo "=== GATE: forbidden tokens in $FILE ==="
grep -nE '\b(sorry|admit)\b|^\s*axiom\b|native_decide|\bopaque\b|\bpostulate\b' "$FILE"; TOKEN_RC=$?
if [ "$TOKEN_RC" -ne 1 ]; then echo "REJECT: forbidden token or unreadable module"; exit 3; fi
echo "=== GATE: git diff --check ==="; git diff --check HEAD -- . || { echo "REJECT: whitespace"; exit 3; }
echo "=== GATE: lake build $MODULE ==="
OUT=$(lake build "$MODULE" 2>&1); RC=$?; echo "$OUT" | tail -5
if [ $RC -ne 0 ] || echo "$OUT" | grep -qE '^error:|error: '; then echo "REJECT: build failed"; exit 4; fi
if echo "$OUT" | grep -q "$FILE.*warning: declaration uses 'sorry'"; then echo "REJECT: sorry warning"; exit 4; fi
echo "=== GATE: module-wide and named axiom scan ==="
SCAN=$(mktemp /tmp/gate_scan_XXXX.lean)
trap 'rm -f "$SCAN"' EXIT
cat > "$SCAN" <<LEAN
import $MODULE
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let some idx := env.getModuleIdx? \`$MODULE | throwError "module not found"
  let mut bad : Array String := #[]
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      for a in axs do
        if a != \`\`propext && a != \`\`Classical.choice && a != \`\`Quot.sound then
          bad := bad.push s!"{n} uses {a}"
  logInfo m!"GATE_SCAN declarations={count} nonstandard={bad}"
  unless bad.isEmpty do
    throwError "nonstandard module axioms: {bad}"
LEAN
for t in "$@"; do
  cat >> "$SCAN" <<LEAN
open Lean Elab Command in
run_cmd do
  let n := \`$t
  let _ ← getConstInfo n
  let axs ← liftCoreM (collectAxioms n)
  for a in axs do
    unless a == \`\`propext || a == \`\`Classical.choice || a == \`\`Quot.sound do
      throwError "nonstandard named axiom {a} in {n}"
  logInfo m!"GATE_NAMED_OK {n}"
#print axioms $t
LEAN
done
SCANOUT=$(LEAN_NUM_THREADS=1 lake env lean "$SCAN" 2>&1); SCAN_RC=$?
printf '%s\n' "$SCANOUT"
if [ "$SCAN_RC" -ne 0 ] || ! printf '%s\n' "$SCANOUT" | grep -q '^GATE_SCAN declarations=[0-9]* nonstandard=\[\]$'; then
  echo "REJECT: nonstandard axiom or scan failure"; exit 5
fi
NAMED_COUNT=$(printf '%s\n' "$SCANOUT" | grep -c '^GATE_NAMED_OK ' || true)
if [ "$NAMED_COUNT" -ne "$#" ]; then echo "REJECT: incomplete named axiom scan"; exit 5; fi
echo "=== GATE: PASS ==="
