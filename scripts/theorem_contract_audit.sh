#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

# Equality lemmas remain valid API, but companion names are not type contracts.
exec python3 scripts/frozen_contract_audit.py "$@"
