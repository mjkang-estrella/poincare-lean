#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

echo "== Lean build =="
lake build

echo "== Placeholder audit =="
placeholder_hits=$(rg -n '\b(opaque|axiom|constant|postulate|sorry|admit)\b' Poincare Poincare.lean || true)
proof_wanted_hits=$(rg -n '^\s*proof_wanted\b' Poincare Poincare.lean || true)

if [ -n "$placeholder_hits" ]; then
  echo "Disallowed proof placeholders found:"
  printf '%s\n' "$placeholder_hits"
  exit 1
fi

if [ -n "$proof_wanted_hits" ]; then
  echo "Local proof_wanted declarations found:"
  printf '%s\n' "$proof_wanted_hits"
  exit 1
fi

dependency_claim_pattern='^\s*(noncomputable\s+)?(theorem|lemma|def|abbrev)\s+.*:\s*(Poincare\.)?(PoincareProofDependencies|RemainingDependencyPackage)(\.\{[^}]*\})?\s*(:=|where|by)?$|^\s*example\s*:\s*(Poincare\.)?(PoincareProofDependencies|RemainingDependencyPackage)(\.\{[^}]*\})?\s*(:=|where|by)?$'
dependency_claim_hits=$(rg -n "$dependency_claim_pattern" Poincare || true)
direct_target_claim_pattern='^\s*(noncomputable\s+)?(theorem|lemma|def|abbrev)\s+.*:\s*(Poincare\.)?(Smooth)?PoincareConjectureStatement(\.\{[^}]*\})?\s*(:=|where|by)?$|^\s*example\s*:\s*(Poincare\.)?(Smooth)?PoincareConjectureStatement(\.\{[^}]*\})?\s*(:=|where|by)?$'
alternate_target_claim_hits=$(rg -n "$direct_target_claim_pattern" Poincare Poincare.lean | rg -v '\b(poincare_conjecture|smoothPoincareConjectureStatement_eq)\b' || true)

if [ -n "$dependency_claim_hits" ]; then
  echo "Local declaration claims the aggregate dependency package:"
  printf '%s\n' "$dependency_claim_hits"
  exit 1
fi

if [ -n "$alternate_target_claim_hits" ]; then
  echo "Local noncanonical declaration claims a Poincare target statement:"
  printf '%s\n' "$alternate_target_claim_hits"
  exit 1
fi

completion_check_dir=
completion_check=

cleanup() {
  if [ -n "$completion_check_dir" ]; then
    rm -rf "$completion_check_dir"
  fi
}

trap cleanup EXIT

if rg -q '^\s*(noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(Poincare\.)?poincare_conjecture\b' Poincare Poincare.lean; then
  completion_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-formalization-check.$$-XXXXXX")
  completion_check="$completion_check_dir/check.lean"
  cat > "$completion_check" <<'EOF'
import Poincare

#check (Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement)
EOF

  if ! lake env lean "$completion_check" >/dev/null 2>&1; then
    echo "A local poincare_conjecture declaration exists, but Lean cannot confirm the canonical target type."
    lake env lean "$completion_check" || true
    exit 1
  fi

  rm -rf "$completion_check_dir"
  completion_check_dir=
  completion_check=
else
  echo "Reserved theorem boundary: poincare_conjecture is absent; scaffold audit success is not theorem completion."
fi

echo "No disallowed proof placeholders or false proof claims detected."

sh scripts/interface_audit.sh
sh scripts/mathlib_gap_audit.sh
sh scripts/shape_contract_audit.sh
sh scripts/theorem_contract_audit.sh
sh scripts/semantic_surface_audit.sh
sh scripts/root_import_audit.sh
sh scripts/axiom_audit.sh
