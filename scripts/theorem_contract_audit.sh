#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

echo "== Theorem contract audit =="

status=0
checked=0
decls_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-contracts.XXXXXX")
names_file=$(mktemp "${TMPDIR:-/tmp}/poincare-theorem-names.XXXXXX")

cleanup() {
  rm -f "$decls_file" "$names_file"
}

trap cleanup EXIT

rg --no-filename -o '^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+[A-Za-z0-9_.'\'']+' \
  Poincare/*.lean |
  sed -E 's/^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+//' |
  sort -u > "$names_file"

rg -n -o '^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+[A-Za-z0-9_.'\'']+' \
  Poincare/*.lean |
  sort -t: -k1,1 -k2,2n > "$decls_file"

while IFS=: read -r path line rest; do
  name=$(
    printf '%s\n' "$rest" |
      sed -E 's/^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+//'
  )

  case "$name" in
    *_eq|poincare_conjecture)
      continue
      ;;
  esac

  checked=$((checked + 1))
  if grep -Fxq "${name}_eq" "$names_file"; then
    :
  else
    echo "FAIL: $name at $path:$line is missing ${name}_eq"
    status=1
  fi
done < "$decls_file"

if [ "$status" -eq 0 ]; then
  echo "PASS: theorem equality contracts present for $checked theorem/lemma declarations"
fi

exit "$status"
