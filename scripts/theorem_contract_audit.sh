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

: > "$decls_file"
for path in Poincare/*.lean; do
  awk -v path="$path" '
    BEGIN {
      in_block = 0
      apos = sprintf("%c", 39)
      pattern = "^(@\\[[^]]+\\][[:space:]]+)?(theorem|lemma)[[:space:]]+[A-Za-z0-9_." apos "]+"
    }
    {
      line = $0
      if (in_block) {
        if (line ~ /-\//) {
          in_block = 0
        }
        next
      }
      if (line ~ /^[[:space:]]*\/-/) {
        if (line !~ /-\//) {
          in_block = 1
        }
        next
      }
      sub(/[[:space:]]*--.*/, "", line)
      if (line ~ pattern) {
        match(line, pattern)
        print path ":" NR ":" substr(line, RSTART, RLENGTH)
      }
    }
  ' "$path" >> "$decls_file"
done

sort -t: -k1,1 -k2,2n "$decls_file" -o "$decls_file"

cut -d: -f3- "$decls_file" |
  sed -E 's/^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+//' |
  sort -u > "$names_file"

awk -F: '
  FNR == NR {
    names[$0] = 1
    next
  }
  {
    path = $1
    line = $2
    rest = $3
    for (i = 4; i <= NF; i++) {
      rest = rest ":" $i
    }
    name = rest
    sub(/^(@\[[^]]+\][[:space:]]+)?(theorem|lemma)[[:space:]]+/, "", name)

    if (name ~ /_eq$/ || name == "poincare_conjecture") {
      next
    }

    checked += 1
    if (!((name "_eq") in names)) {
      print "FAIL: " name " at " path ":" line " is missing " name "_eq"
      status = 1
    }
  }
  END {
    if (status == 0) {
      print "PASS: theorem equality contracts present for " checked " theorem/lemma declarations"
    }
    exit status
  }
' "$names_file" "$decls_file"
