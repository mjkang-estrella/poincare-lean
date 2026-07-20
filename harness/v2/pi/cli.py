"""Command-line boundary for the Harness v2 Pi Job engine and tool broker."""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any, Sequence

from harness.v2.runtime.store import HarnessError, default_state_dir
from harness.v2.worker.artifacts import ArtifactError, ArtifactStore, canonical_json_bytes

from . import TOOL_NAMES
from .broker import BrokerError, execute_tool, read_tool_input
from .engine import PiEngineError, run_job
from .security import SecurityError, arm_parent_death_guard
from .snapshot import SnapshotError, build_snapshot, load_task_file


def _positive_integer(raw: str) -> int:
    try:
        value = int(raw)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("must be an integer") from exc
    if value < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def _print_json(value: Any, *, stream: Any | None = None) -> None:
    if stream is None:
        stream = sys.stdout
    print(
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2),
        file=stream,
        flush=True,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python3 -m harness.v2.pi",
        description="Run one bounded fresh Pi session for a claimed Harness v2 Job",
    )
    commands = parser.add_subparsers(dest="command", required=True)

    snapshot = commands.add_parser(
        "snapshot", help="materialize the deterministic Pi prompt/context snapshot"
    )
    snapshot.add_argument("--task-json", required=True)
    snapshot.add_argument("--worktree", required=True)
    snapshot.add_argument("--output-dir", required=True)
    snapshot.set_defaults(action="snapshot")

    run = commands.add_parser(
        "run-job", help="execute one fresh Pi session without changing Harness state"
    )
    run.add_argument("--job-id", required=True)
    run.add_argument("--lease-owner", required=True)
    run.add_argument("--lease-token", required=True, type=_positive_integer)
    run.add_argument("--state-dir", default=str(default_state_dir()))
    run.add_argument("--control-root", default=str(Path.cwd()))
    run.add_argument("--pi-install-manifest", required=True)
    run.add_argument("--pi-dependency-graph", required=True)
    run.add_argument("--lean-timeout-seconds", type=_positive_integer, default=900)
    run.set_defaults(action="run_job")

    # This subcommand is called only by the explicit Pi extension. Its request
    # body is bounded JSON on stdin; it deliberately has no generic argv/shell
    # escape hatch.
    tool = commands.add_parser("tool", help=argparse.SUPPRESS)
    tool.add_argument("--capability", required=True)
    tool.add_argument("--capability-sha256", required=True)
    tool.add_argument("--tool", required=True, choices=TOOL_NAMES)
    tool.add_argument("--call-id", required=True)
    tool.set_defaults(action="tool")
    return parser


def _snapshot(arguments: argparse.Namespace) -> dict[str, Any]:
    task = load_task_file(arguments.task_json)
    snapshot = build_snapshot(task, arguments.worktree)
    output = ArtifactStore(arguments.output_dir)
    prompt = output.write_once("prompt.md", snapshot.prompt.encode("utf-8"))
    manifest = output.write_once(
        "context-manifest.json", canonical_json_bytes(snapshot.manifest)
    )
    return {
        "schema_version": "poincare.pi-snapshot-result.v1",
        "task_id": task["id"],
        "task_revision": task["revision"],
        "prompt_sha256": snapshot.prompt_sha256,
        "context_sha256": snapshot.context_sha256,
        "prompt_artifact": prompt.relative_path,
        "context_manifest_artifact": manifest.relative_path,
        "context_files": len(snapshot.entries),
    }


def dispatch(arguments: argparse.Namespace) -> dict[str, Any]:
    if arguments.action == "snapshot":
        return _snapshot(arguments)
    if arguments.action == "run_job":
        result = run_job(
            job_id=arguments.job_id,
            lease_owner=arguments.lease_owner,
            lease_token=arguments.lease_token,
            state_dir=arguments.state_dir,
            control_root=arguments.control_root,
            pi_install_manifest=arguments.pi_install_manifest,
            pi_dependency_graph=arguments.pi_dependency_graph,
            lean_timeout_seconds=arguments.lean_timeout_seconds,
        )
        return asdict(result)
    if arguments.action == "tool":
        result = execute_tool(
            capability_path=Path(arguments.capability),
            capability_sha256=arguments.capability_sha256,
            tool_name=arguments.tool,
            call_id=arguments.call_id,
            value=read_tool_input(),
        )
        # Broker stdout is a compact, one-object protocol consumed by the Pi
        # extension, not a human-oriented CLI rendering.
        print(
            json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")),
            flush=True,
        )
        return {}
    raise PiEngineError(f"unknown Pi CLI action: {arguments.action}")


def _arm_broker_parent_guard(arguments: argparse.Namespace) -> None:
    if getattr(arguments, "action", None) != "tool":
        return
    if os.environ.get("HARNESS_PI_BROKER_PROCESS") != "1":
        raise SecurityError("Pi tool broker requires the supervised broker marker")
    raw_parent = os.environ.get("HARNESS_PI_PARENT_PID", "")
    if not raw_parent.isascii() or not raw_parent.isdecimal():
        raise SecurityError("Pi tool broker requires an exact parent PID")
    expected_parent = int(raw_parent)
    if str(expected_parent) != raw_parent or expected_parent <= 1:
        raise SecurityError("Pi tool broker parent PID is invalid")
    arm_parent_death_guard(expected_parent)


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    arguments = parser.parse_args(argv)
    try:
        _arm_broker_parent_guard(arguments)
        result = dispatch(arguments)
    except (ArtifactError, BrokerError, HarnessError, PiEngineError, SecurityError, SnapshotError) as exc:
        if getattr(arguments, "action", None) == "tool":
            print(
                json.dumps(
                    {"ok": False, "error": str(exc)},
                    ensure_ascii=False,
                    sort_keys=True,
                    separators=(",", ":"),
                ),
                flush=True,
            )
        else:
            print(f"error: {exc}", file=sys.stderr, flush=True)
        return 2
    if arguments.action != "tool":
        _print_json(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
