#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

echo "== Mathlib gap audit =="

status=0
poincare_file=".lake/packages/mathlib/Mathlib/Geometry/Manifold/PoincareConjecture.lean"
manifold_dir=".lake/packages/mathlib/Mathlib/Geometry/Manifold"
poincare_proof_wanted=0
name_check_dir=
name_check=

cleanup() {
  if [ -n "$name_check_dir" ]; then
    rm -rf "$name_check_dir"
  fi
}

trap cleanup EXIT

if rg -q '^proof_wanted .*nonempty_(homeomorph|diffeomorph)_sphere_three' "$poincare_file"; then
  echo "GAP: mathlib 3D Poincare statements are still proof_wanted"
  rg -n '^proof_wanted .*nonempty_(homeomorph|diffeomorph)_sphere_three' "$poincare_file"
  poincare_proof_wanted=1
else
  echo "READY: mathlib 3D Poincare statements are no longer proof_wanted"
fi

name_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-mathlib-name-check.$$-XXXXXX")
name_check="$name_check_dir/check.lean"
cat > "$name_check" <<'EOF'
import Mathlib.Geometry.Manifold.PoincareConjecture

open scoped Manifold ContDiff

#check SimplyConnectedSpace.nonempty_homeomorph_sphere_three
#check SimplyConnectedSpace.nonempty_diffeomorph_sphere_three
EOF

if lake env lean "$name_check" >/dev/null 2>&1; then
  echo "READY: mathlib 3D Poincare names are exposed to Lean"
else
  if [ "$poincare_proof_wanted" -eq 1 ]; then
    echo "INFO: mathlib proof_wanted 3D Poincare names are not exposed as Lean constants"
  else
    echo "GAP: mathlib 3D Poincare source no longer has proof_wanted, but canonical names do not typecheck"
    lake env lean "$name_check" || true
    status=1
  fi
fi

rm -rf "$name_check_dir"
name_check_dir=
name_check=

if sh scripts/mathlib_proof_wanted_dependency_guard.sh; then
  :
else
  status=1
fi

if rg -q '\bContMDiffRiemannianMetric\b' "$manifold_dir"; then
  echo "READY: mathlib has smooth Riemannian metric infrastructure"
else
  echo "GAP: smooth Riemannian metric infrastructure not found"
  status=1
fi

if rg -q '\b(RicciTensor|RicciCurvature|RicciFlow|RicciSoliton)\b' "$manifold_dir"; then
  echo "READY: mathlib appears to contain Ricci-specific manifold declarations"
  rg -n '\b(RicciTensor|RicciCurvature|RicciFlow|RicciSoliton)\b' "$manifold_dir"
else
  echo "GAP: Ricci-specific manifold declarations not found"
fi

if rg -q '^\s*(def|theorem|lemma|class|structure|inductive)\s+.*\b(RicciFlowWithSurgery|Perelman|FiniteExtinction)\b' "$manifold_dir"; then
  echo "READY: mathlib appears to contain Ricci-flow-with-surgery declarations"
  rg -n '^\s*(def|theorem|lemma|class|structure|inductive)\s+.*\b(RicciFlowWithSurgery|Perelman|FiniteExtinction)\b' "$manifold_dir"
else
  echo "GAP: Ricci-flow-with-surgery / Perelman finite-extinction declarations not found"
fi

exit "$status"
