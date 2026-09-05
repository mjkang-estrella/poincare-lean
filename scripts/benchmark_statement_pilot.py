#!/usr/bin/env python3
"""Measure focused statement/proof checks without modifying Lean sources.

Build the selected modules first. This measures warm-cache elaboration, not a
before/after speedup or a clean build. Raw outputs are retained in the report.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import statistics
import subprocess
import time


def measure(root: Path, path: str) -> dict:
    command = ["lake", "env", "lean", path]
    start = time.perf_counter()
    result = subprocess.run(
        command, cwd=root, env={**os.environ, "LEAN_NUM_THREADS": "1"},
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=300, check=False,
    )
    return {
        "command": command, "seconds": time.perf_counter() - start,
        "exit_code": result.returncode, "stdout": result.stdout,
        "stderr": result.stderr,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--statements", required=True)
    parser.add_argument("--proofs", required=True)
    parser.add_argument("--repeat", type=int, default=2)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error("--repeat must be positive")
    root = Path(__file__).resolve().parents[1]
    for path in (args.statements, args.proofs):
        resolved = (root / path).resolve()
        if not resolved.is_relative_to(root) or resolved.suffix != ".lean" or not resolved.is_file():
            parser.error("each module must be an existing repository Lean source")
    report = {
        "schema_version": 1,
        "measurement": "warm-cache focused elaboration; no speedup claim",
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "working_tree": subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True),
        "lean_num_threads": 1,
        "runs": {"statements": [], "proofs": []},
    }
    # Alternate the checks so all statement samples do not precede all proofs.
    for _ in range(args.repeat):
        for label, path in (("statements", args.statements), ("proofs", args.proofs)):
            report["runs"][label].append(measure(root, path))
    report["median_seconds"] = {
        label: statistics.median(run["seconds"] for run in runs)
        for label, runs in report["runs"].items()
    }
    report["passed"] = all(
        run["exit_code"] == 0 for runs in report["runs"].values() for run in runs
    )
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end="")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
