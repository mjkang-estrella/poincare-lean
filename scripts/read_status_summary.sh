#!/usr/bin/env sh
set -eu
root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
exec python3 "$root_dir/scripts/verification_receipts.py" --root "$root_dir" read "$@"
