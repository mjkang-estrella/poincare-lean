#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

echo "== Theorem contract audit =="

decls_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-contracts.XXXXXX")
names_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-names.XXXXXX")
missing_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-missing.XXXXXX")
baseline_entries_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-baseline.XXXXXX")
checked_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-checked.XXXXXX")
diff_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-diff.XXXXXX")
baseline_file="scripts/theorem_contract_audit_known_missing.txt"
name_pattern='^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+[A-Za-z0-9_.'\'']+'

cleanup() {
  rm -f "$decls_file" "$names_file" "$missing_file" \
    "$baseline_entries_file" "$checked_file" "$diff_file"
}

trap cleanup EXIT

rg --no-filename -o "$name_pattern" Poincare Poincare.lean |
  sed -E 's/^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+//' |
  sort -u > "$names_file"

rg -n -o "$name_pattern" Poincare Poincare.lean |
  sort -t: -k1,1 -k2,2n > "$decls_file"

awk -F: -v checked_file="$checked_file" '
  NR == FNR {
    names[$0] = 1
    next
  }

  {
    decl_path = $1
    rest = $0
    sub(/^[^:]+:[^:]+:/, "", rest)
    sub(/^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+/, "", rest)
    name = rest

    if (name ~ /_eq$/ || name == "poincare_conjecture") {
      next
    }

    checked += 1
    eq_name = name "_eq"
    if (!(eq_name in names)) {
      printf "%s:%s:%s\n", decl_path, name, eq_name
    }
  }

  END {
    print checked > checked_file
  }
' "$names_file" "$decls_file" > "$missing_file"

if [ "${1:-}" = "--write-baseline" ]; then
  {
    echo "# Known theorem/lemma declarations without sibling _eq contracts."
    echo "# Format: path:name:expected_eq_name"
    echo "# Regenerate only after reviewing that the changed boundary is intentional."
    cat "$missing_file"
  } > "$baseline_file"
  echo "Wrote $baseline_file"
  exit 0
fi

if [ ! -f "$baseline_file" ]; then
  echo "FAIL: theorem contract baseline is missing: $baseline_file"
  echo "Run sh scripts/theorem_contract_audit.sh --write-baseline after reviewing current missing contracts."
  exit 1
fi

sed '/^[[:space:]]*#/d;/^[[:space:]]*$/d' "$baseline_file" > "$baseline_entries_file"

if diff -u "$baseline_entries_file" "$missing_file" > "$diff_file"; then
  checked=$(cat "$checked_file")
  missing=$(wc -l < "$missing_file" | tr -d ' ')
  present=$((checked - missing))
  echo "PASS: theorem equality-contract boundary matches baseline"
  echo "PASS: $present theorem/lemma declarations have sibling _eq contracts"
  echo "PASS: $missing theorem/lemma declarations are recorded as known missing contracts"
else
  echo "FAIL: theorem equality-contract boundary changed"
  cat "$diff_file"
  exit 1
fi
