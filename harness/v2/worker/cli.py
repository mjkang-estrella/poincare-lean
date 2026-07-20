"""Command-line interface for the bounded Leanstral worker."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import Sequence

from .artifacts import ArtifactError
from .binding import BindingError
from .client import (
    LeanstralConfig,
    LeanstralError,
    _parse_positive_float,
    check_health,
    run_once,
    snapshot_job,
)
from .snapshot import SnapshotError


def _positive_integer(raw: str) -> int:
    try:
        value = int(raw)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("must be an integer") from exc
    if value < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def _add_binding_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--job-id", required=True)
    parser.add_argument("--state-dir", type=Path, required=True)
    parser.add_argument("--lease-owner", required=True)
    parser.add_argument("--lease-token", type=_positive_integer, required=True)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python -m harness.v2.worker",
        description="Pinned Leanstral health/snapshot and fallback one-shot client",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("health", help="verify the exact endpoint model ID without artifacts")

    snapshot = subparsers.add_parser(
        "snapshot", help="build a deterministic prompt/context snapshot without inference"
    )
    _add_binding_arguments(snapshot)

    run = subparsers.add_parser(
        "run", help="explicit fallback: snapshot a Task and make one completion request"
    )
    _add_binding_arguments(run)
    run.add_argument("--timeout-seconds", type=str)
    return parser


def _run_config(args: argparse.Namespace) -> LeanstralConfig:
    config = LeanstralConfig.from_env()
    if args.timeout_seconds is not None:
        config = replace(
            config,
            timeout_seconds=_parse_positive_float(args.timeout_seconds, "--timeout-seconds"),
        )
    return config


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "health":
            config = LeanstralConfig.from_env()
            result = check_health(config)
            output = {
                "ok": True,
                "model": result.model,
                "served_model_ids": list(result.served_model_ids),
                "status_code": result.status_code,
            }
        elif args.command == "snapshot":
            config = LeanstralConfig.from_env()
            binding, result = snapshot_job(
                config=config,
                job_id=args.job_id,
                state_dir=args.state_dir,
                lease_owner=args.lease_owner,
                lease_token=args.lease_token,
            )
            output = {
                "ok": True,
                "job_id": binding.job["id"],
                "task_id": result.task["id"],
                "task_revision": result.task["revision"],
                "prompt_sha256": result.prompt_sha256,
                "context_sha256": result.context_sha256,
                "context_files": [entry.path for entry in result.context_entries],
                "artifact_dir": str(binding.artifact_dir),
            }
        else:
            config = _run_config(args)
            result = run_once(
                config=config,
                job_id=args.job_id,
                state_dir=args.state_dir,
                lease_owner=args.lease_owner,
                lease_token=args.lease_token,
            )
            output = {
                "ok": True,
                "job_id": result.job_id,
                "request_id": result.request_id,
                "model": result.health.model,
                "prompt_sha256": result.snapshot.prompt_sha256,
                "context_sha256": result.snapshot.context_sha256,
                "response_artifact": result.response_artifact,
                "response_sha256": result.response_sha256,
                "assistant_artifact": result.assistant_artifact,
                "assistant_sha256": result.assistant_sha256,
                "evidence_artifact": result.evidence_artifact,
                "evidence_sha256": result.evidence_sha256,
                "finish_reason": result.finish_reason,
                "artifact_dir": str(Path(args.state_dir).resolve() / "jobs" / result.job_id),
            }
        print(json.dumps(output, ensure_ascii=False, sort_keys=True))
        return 0
    except (ArtifactError, BindingError, LeanstralError, SnapshotError, OSError) as exc:
        print(json.dumps({"ok": False, "error": str(exc)}, sort_keys=True), file=sys.stderr)
        return 2
