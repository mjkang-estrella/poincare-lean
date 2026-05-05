#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

echo "== Mathlib proof-wanted dependency guard =="

poincare_file=".lake/packages/mathlib/Mathlib/Geometry/Manifold/PoincareConjecture.lean"
proof_wanted_state=0

if rg -q '^proof_wanted .*nonempty_(homeomorph|diffeomorph)_sphere_three' "$poincare_file"; then
  proof_wanted_state=1
fi

forbidden_names='((SimplyConnectedSpace\.)?(nonempty_homeomorph_sphere_three|nonempty_diffeomorph_sphere_three)|(ContinuousMap\.HomotopyEquiv\.)?nonempty_homeomorph_sphere|exists_homeomorph_isEmpty_diffeomorph_sphere_seven|exists_open_nonempty_homeomorph_isEmpty_diffeomorph_euclideanSpace_four)'
forbidden_regex="(^|[^[:alnum:]_])${forbidden_names}([^[:alnum:]_]|$)"

if rg -n "$forbidden_regex" Poincare Poincare.lean; then
  if [ "$proof_wanted_state" -eq 1 ]; then
    echo "FAIL: local Lean source references mathlib Poincare names that are still proof_wanted upstream"
  else
    echo "FAIL: local Lean source references canonical mathlib Poincare shortcut names"
  fi
  exit 1
fi

if [ "$proof_wanted_state" -eq 1 ]; then
  echo "PASS: local Lean source does not reference mathlib Poincare proof-wanted shortcut names"
else
  echo "PASS: local Lean source does not reference canonical mathlib Poincare shortcut names"
fi
