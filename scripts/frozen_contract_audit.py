#!/usr/bin/env python3
"""Execute reviewed, frozen type and axiom contracts for curated interfaces.

A successful run certifies only the listed declarations and pinned definition
sources. Mathematical agreement is an independent review decision, whose exact
report is checked here. There is no theorem-count or companion-name requirement.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from harness.v2.runtime.validation import (  # noqa: E402
    RecordValidationError,
    statement_contract_probe_source,
    statement_contract_snapshot,
    validate_statement_contract,
    validate_statement_readback,
)


def read_source(root: Path, relative: str) -> bytes:
    path = root / relative
    if root not in path.parents:
        raise ValueError(f"source escapes repository: {relative}")
    for candidate in (path, *path.parents):
        if candidate == root:
            break
        if candidate.is_symlink():
            raise ValueError(f"symbolic-link statement evidence is forbidden: {relative}")
    if not path.is_file():
        raise ValueError(f"missing statement evidence: {relative}")
    if path.stat().st_size > 8 * 1024 * 1024:
        raise ValueError(f"statement evidence exceeds 8 MiB: {relative}")
    return path.read_bytes()


def verify_context(root: Path, contract: dict) -> None:
    validate_statement_contract(contract)
    for entry in contract["definition_files"]:
        digest = hashlib.sha256(read_source(root, entry["path"])).hexdigest()
        if digest != entry["sha256"]:
            raise ValueError(f"frozen statement definition changed: {entry['path']}")
    review = contract["review"]
    validate_statement_readback(contract, read_source(root, review["report_path"]))


def load_manifest(path: Path) -> dict:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict) or set(manifest) != {"schema_version", "statement_contract"}:
        raise ValueError("contract manifest fields must be schema_version and statement_contract")
    if manifest["schema_version"] != "1.0":
        raise ValueError("contract manifest schema_version must equal '1.0'")
    return manifest["statement_contract"]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--manifest", type=Path, action="append")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--snapshot", action="store_true", help="print draft statement/definition hash only")
    mode.add_argument("--render", action="store_true", help="print verified executable Lean probe only")
    mode.add_argument("--check-context-only", action="store_true", help="verify source and review hashes, without Lean")
    args = parser.parse_args(argv)
    root = args.repo.resolve(strict=True)
    paths = args.manifest or sorted((root / "harness/v2/contracts").glob("*.contract.json"))
    if not paths:
        print("FAIL: no curated frozen statement contracts", file=sys.stderr)
        return 1
    checked = 0
    try:
        for path in paths:
            path = path if path.is_absolute() else root / path
            contract = load_manifest(path)
            if args.snapshot:
                print(statement_contract_snapshot(contract))
                continue
            verify_context(root, contract)
            if args.check_context_only:
                print(f"PASS: reviewed source snapshot {path.name} (Lean not run)")
                continue
            source = statement_contract_probe_source(contract)
            if args.render:
                print(source, end="")
                continue
            environment = dict(os.environ, LEAN_NUM_THREADS="1")
            modules = [name for name in contract["imports"] if name not in {"Lean", "Init"}]
            if modules:
                build = subprocess.run(["lake", "build", *modules], cwd=root, env=environment, check=False)
                if build.returncode:
                    return build.returncode
                verify_context(root, contract)
            probe = subprocess.run(
                ["lake", "env", "lean", "--stdin"], input=source, text=True,
                cwd=root, env=environment, check=False,
            )
            if probe.returncode:
                return probe.returncode
            verify_context(root, contract)
            checked += len(contract["declarations"])
        if not (args.snapshot or args.render or args.check_context_only):
            print(f"PASS: {checked} curated frozen type and axiom contracts; global theorem coverage is not claimed")
        return 0
    except (OSError, ValueError, RecordValidationError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
