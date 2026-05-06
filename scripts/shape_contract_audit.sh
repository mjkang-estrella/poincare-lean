#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

echo "== Shape contract audit =="

status=0
decls_file=$(mktemp "${TMPDIR:-/tmp}/poincare-shape-contracts.XXXXXX")

cleanup() {
  rm -f "$decls_file"
}

trap cleanup EXIT

rg -n '^(noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+[A-Za-z0-9_]+' \
  Poincare/*.lean | sort -t: -k1,1 -k2,2n > "$decls_file"

while IFS=: read -r path line rest; do
  name=$(
    printf '%s\n' "$rest" |
      sed -E 's/^(noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+([A-Za-z0-9_]+).*/\3/'
  )
  first=$(printf '%s' "$name" | cut -c1 | tr 'A-Z' 'a-z')
  rest_name=$(printf '%s' "$name" | cut -c2-)
  eq_name="${first}${rest_name}_eq"

  if rg -q "^(@\\[simp\\] )?(theorem|lemma)[[:space:]]+${eq_name}\\b" "$path"; then
    echo "PASS: $name has $eq_name in $path"
  else
    echo "FAIL: $name at $path:$line is missing $eq_name"
    status=1
  fi
done < "$decls_file"

exit "$status"
