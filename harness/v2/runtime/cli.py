"""Command-line interface for the first executable Harness v2 core."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

from .store import HarnessError, HarnessStore, default_state_dir


MAX_RECORD_BYTES = 10 * 1024 * 1024


def _read_json(path_text: str) -> dict[str, Any]:
    path = Path(path_text)
    if not path.is_file():
        raise HarnessError(f"JSON record is not a regular file: {path}")
    if path.stat().st_size > MAX_RECORD_BYTES:
        raise HarnessError(f"JSON record exceeds {MAX_RECORD_BYTES} bytes: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise HarnessError(f"could not read JSON record {path}: {error}") from error
    if not isinstance(value, dict):
        raise HarnessError(f"JSON record must contain one object: {path}")
    return value


def _print(value: Any) -> None:
    print(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2))


def _add_task_transition_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("task_id")
    parser.add_argument(
        "to_state", choices=["ready", "accepted", "blocked", "superseded"]
    )
    parser.add_argument("--revision", type=int)
    parser.add_argument("--accepted-commit")
    parser.add_argument("--gate-job")
    parser.add_argument("--reason")
    parser.add_argument("--evidence-job")
    parser.add_argument("--superseding-task")
    parser.set_defaults(action="task_transition")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python3 -m harness.v2.runtime",
        description="Restart-safe Harness v2 Task, Job, and lease control plane",
    )
    parser.add_argument(
        "--state-dir",
        default=str(default_state_dir()),
        help="runtime state directory (default: harness/v2/state)",
    )
    parser.add_argument(
        "--worktree-root",
        help="trusted external root for Job worktrees; persist with init",
    )
    parser.add_argument(
        "--integration-root",
        help="integration/control checkout that Job worktrees must remain outside",
    )
    commands = parser.add_subparsers(dest="command", required=True)

    init = commands.add_parser("init", help="idempotently create or migrate runtime state")
    init.set_defaults(action="init")

    dispatch_control = commands.add_parser(
        "dispatch", help="manage the durable deployment dispatch fence"
    )
    dispatch_commands = dispatch_control.add_subparsers(
        dest="dispatch_command", required=True
    )
    dispatch_show = dispatch_commands.add_parser("show", help="show dispatch state")
    dispatch_show.set_defaults(action="dispatch_show")
    dispatch_set = dispatch_commands.add_parser(
        "set", help="atomically enable or stop new Job claims"
    )
    dispatch_set.add_argument("state", choices=["running", "stopped"])
    dispatch_set.add_argument("--actor", required=True)
    dispatch_set.set_defaults(action="dispatch_set")

    task = commands.add_parser("task", help="manage durable Task contracts")
    task_commands = task.add_subparsers(dest="task_command", required=True)
    task_import = task_commands.add_parser("import", help="validate and import a proposed Task")
    task_import.add_argument("path")
    task_import.set_defaults(action="task_import")
    task_list = task_commands.add_parser("list", help="list Tasks")
    task_list.add_argument("--state")
    task_list.add_argument("--all-revisions", action="store_true")
    task_list.set_defaults(action="task_list")
    task_show = task_commands.add_parser("show", help="show one Task")
    task_show.add_argument("task_id")
    task_show.add_argument("--revision", type=int)
    task_show.set_defaults(action="task_show")
    _add_task_transition_arguments(
        task_commands.add_parser("transition", help="perform a checked Task state transition")
    )
    _add_task_transition_arguments(
        task_commands.add_parser("state", help="alias for task transition")
    )

    job = commands.add_parser("job", help="manage individual execution attempts")
    job_commands = job.add_subparsers(dest="job_command", required=True)
    job_enqueue = job_commands.add_parser("enqueue", help="validate and enqueue a Job record")
    job_enqueue.add_argument("path")
    job_enqueue.set_defaults(action="job_enqueue")
    job_list = job_commands.add_parser("list", help="list Jobs")
    job_list.add_argument("--state")
    job_list.add_argument("--task")
    job_list.set_defaults(action="job_list")
    job_show = job_commands.add_parser("show", help="show one Job and its lease scopes")
    job_show.add_argument("job_id")
    job_show.set_defaults(action="job_show")
    job_claim = job_commands.add_parser(
        "claim", help="atomically claim a queued or expired recoverable Job"
    )
    job_claim.add_argument("--owner", required=True)
    job_claim.add_argument("--lease-seconds", type=int, default=900)
    job_claim.add_argument("--job-id")
    job_claim.set_defaults(action="job_claim")
    job_heartbeat = job_commands.add_parser(
        "heartbeat", help="renew an owned lease and optionally advance execution state"
    )
    job_heartbeat.add_argument("job_id")
    job_heartbeat.add_argument("--owner", required=True)
    job_heartbeat.add_argument("--lease-token", required=True, type=int)
    job_heartbeat.add_argument("--lease-seconds", type=int, default=900)
    job_heartbeat.add_argument("--state", choices=["preparing", "running", "reviewing"])
    job_heartbeat.set_defaults(action="job_heartbeat")
    job_finish = job_commands.add_parser(
        "finish", help="finish an owned Job without accepting its Task"
    )
    job_finish.add_argument("job_id")
    job_finish.add_argument("--owner", required=True)
    job_finish.add_argument("--lease-token", required=True, type=int)
    job_finish.add_argument(
        "--state", required=True, choices=["blocked", "interrupted"]
    )
    job_finish.add_argument("--exit-reason", required=True)
    job_finish.set_defaults(action="job_finish")
    job_stop_interrupt = job_commands.add_parser(
        "interrupt-stopped",
        help="terminalize a reaped Job while durable dispatch is stopped",
    )
    job_stop_interrupt.add_argument("job_id")
    job_stop_interrupt.add_argument("--actor", required=True)
    job_stop_interrupt.add_argument("--exit-reason", required=True)
    job_stop_interrupt.set_defaults(action="job_interrupt_stopped")
    job_review = job_commands.add_parser(
        "review", help="record an independent Codex review of a reviewing Job"
    )
    job_review.add_argument("job_id")
    job_review.add_argument("--reviewer", required=True)
    job_review.add_argument(
        "--state", required=True, choices=["passed", "rejected"]
    )
    job_review.add_argument("--exit-reason", required=True)
    job_review.add_argument(
        "--gate-status", choices=["not_run", "passed", "failed"], default="not_run"
    )
    job_review.add_argument(
        "--gate-result",
        help="path relative to the Job artifact directory; required for a completed gate",
    )
    job_review.add_argument("--accepted-commit")
    job_review.set_defaults(action="job_review")
    return parser


def dispatch(arguments: argparse.Namespace) -> Any:
    store = HarnessStore(
        arguments.state_dir,
        worktree_root=arguments.worktree_root,
        integration_root=arguments.integration_root,
    )
    if arguments.action == "init":
        return store.initialize()
    if arguments.action == "dispatch_show":
        return store.get_dispatch_state()
    if arguments.action == "dispatch_set":
        return store.set_dispatch_state(arguments.state, actor=arguments.actor)
    if arguments.action == "task_import":
        return store.import_task(_read_json(arguments.path))
    if arguments.action == "task_list":
        return store.list_tasks(
            state=arguments.state, all_revisions=arguments.all_revisions
        )
    if arguments.action == "task_show":
        return store.get_task(arguments.task_id, arguments.revision)
    if arguments.action == "task_transition":
        return store.transition_task(
            arguments.task_id,
            arguments.to_state,
            revision=arguments.revision,
            accepted_commit=arguments.accepted_commit,
            gate_job_id=arguments.gate_job,
            blocked_reason=arguments.reason,
            evidence_job_id=arguments.evidence_job,
            superseding_task_id=arguments.superseding_task,
        )
    if arguments.action == "job_enqueue":
        return store.enqueue_job(_read_json(arguments.path))
    if arguments.action == "job_list":
        return store.list_jobs(state=arguments.state, task_id=arguments.task)
    if arguments.action == "job_show":
        return store.get_job(arguments.job_id)
    if arguments.action == "job_claim":
        return store.claim_job(
            owner=arguments.owner,
            lease_seconds=arguments.lease_seconds,
            job_id=arguments.job_id,
        )
    if arguments.action == "job_heartbeat":
        return store.heartbeat_job(
            arguments.job_id,
            owner=arguments.owner,
            lease_token=arguments.lease_token,
            lease_seconds=arguments.lease_seconds,
            to_state=arguments.state,
        )
    if arguments.action == "job_finish":
        return store.finish_job(
            arguments.job_id,
            owner=arguments.owner,
            lease_token=arguments.lease_token,
            state=arguments.state,
            exit_reason=arguments.exit_reason,
        )
    if arguments.action == "job_interrupt_stopped":
        return store.interrupt_job_after_stop(
            arguments.job_id,
            actor=arguments.actor,
            exit_reason=arguments.exit_reason,
        )
    if arguments.action == "job_review":
        return store.review_job(
            arguments.job_id,
            reviewer=arguments.reviewer,
            state=arguments.state,
            exit_reason=arguments.exit_reason,
            gate_status=arguments.gate_status,
            gate_result=arguments.gate_result,
            accepted_commit=arguments.accepted_commit,
        )
    raise HarnessError(f"unknown CLI action: {arguments.action}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    arguments = parser.parse_args(argv)
    try:
        result = dispatch(arguments)
    except HarnessError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    _print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
