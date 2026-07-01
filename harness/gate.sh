#!/bin/bash
# Acceptance gate for worker output. The ONLY judge of task completion.
# Usage: gate.sh <worktree_dir> <module_name> [target_decl ...]
# Exit 0 = accepted. Any nonzero = rejected.
set -uo pipefail
WT="$1"; MODULE="$2"; shift 2
TARGETS=("$@")
cd "$WT" || exit 2

echo "=== GATE: diff hygiene ==="
DIFF=$(git diff HEAD)
if echo "$DIFF" | grep -E '^\+.*\bsorry\b' | grep -v '^\+++'; then
  echo "REJECT: added sorry"; exit 3
fi
if echo "$DIFF" | grep -E '^\+.*\baxiom\b' | grep -v '^\+++'; then
  echo "REJECT: added axiom"; exit 3
fi

echo "=== GATE: build $MODULE ==="
if ! lake build "$MODULE" 2>&1 | tail -20; then
  echo "REJECT: build failed"; exit 4
fi

if [ ${#TARGETS[@]} -gt 0 ]; then
  echo "=== GATE: axiom audit on targets ==="
  AX_FILE=$(mktemp /tmp/gate_axioms_XXXX.lean)
  {
    echo "import $MODULE"
    for t in "${TARGETS[@]}"; do echo "#print axioms $t"; done
  } > "$AX_FILE"
  AX_OUT=$(lake env lean "$AX_FILE" 2>&1)
  echo "$AX_OUT"
  rm -f "$AX_FILE"
  if echo "$AX_OUT" | grep -qE 'sorryAx|error'; then
    echo "REJECT: axiom audit failed"; exit 5
  fi
  # every listed axiom must be a Mathlib-core one
  if echo "$AX_OUT" | grep -oE "'[^']+'" | grep -vE "propext|Classical.choice|Quot.sound" | grep -q .; then
    echo "REJECT: non-core axiom in closure"; exit 5
  fi
fi

echo "=== GATE: PASS ==="
exit 0
