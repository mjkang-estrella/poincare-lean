from __future__ import annotations

import copy
import errno
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import patch

from harness.v2.pi import engine
from harness.v2.pi.engine import (
    PiEngineError,
    _EventState,
    _consume_event,
    _run_pi_process,
    _validate_terminal,
)


SESSION_ID = "00000000-0000-4000-8000-000000000042"
MODEL = "leanstral-test-model"
PROMPT = "# Exact bounded Job\nProve the named scalar derivative lemma."


def _usage(output: int) -> dict[str, object]:
    return {
        "input": 10,
        "output": output,
        "cacheRead": 0,
        "cacheWrite": 0,
        "totalTokens": 10 + output,
        "cost": {
            "input": 0,
            "output": 0,
            "cacheRead": 0,
            "cacheWrite": 0,
            "total": 0,
        },
    }


def _user(prompt: str) -> dict[str, object]:
    return {
        "role": "user",
        "content": [{"type": "text", "text": prompt}],
        "timestamp": 1,
    }


def _assistant(
    output: int,
    *,
    text: str = "verified result",
    stop_reason: str = "stop",
    tool_call: tuple[str, str] | None = None,
) -> dict[str, object]:
    content: list[dict[str, object]] = []
    if text:
        content.append({"type": "text", "text": text})
    if tool_call is not None:
        call_id, name = tool_call
        content.append(
            {
                "type": "toolCall",
                "id": call_id,
                "name": name,
                "arguments": {"view": "status"},
            }
        )
    return {
        "role": "assistant",
        "content": content,
        "api": "openai-completions",
        "provider": "harness-leanstral",
        "model": MODEL,
        "usage": _usage(output),
        "stopReason": stop_reason,
        "timestamp": 2 + output,
    }


def _header() -> dict[str, object]:
    return {
        "type": "session",
        "version": 3,
        "id": SESSION_ID,
        "timestamp": "2026-07-19T00:00:00.000Z",
        "cwd": "/runtime",
    }


def _no_tool_events(prompt: str = PROMPT) -> list[dict[str, object]]:
    user = _user(prompt)
    start = _assistant(0, text="")
    update = _assistant(1, text="verified")
    final = _assistant(3)
    return [
        _header(),
        {"type": "agent_start"},
        {"type": "turn_start"},
        {"type": "message_start", "message": user},
        {"type": "message_end", "message": user},
        {"type": "message_start", "message": start},
        {
            "type": "message_update",
            "message": update,
            "assistantMessageEvent": {"type": "text_delta", "delta": "verified"},
        },
        {"type": "message_end", "message": final},
        {"type": "turn_end", "message": final, "toolResults": []},
        {
            "type": "agent_end",
            "messages": [user, final],
            "willRetry": False,
        },
        {"type": "agent_settled"},
    ]


def _tool_events(prompt: str = PROMPT) -> list[dict[str, object]]:
    user = _user(prompt)
    first_start = _assistant(0, text="")
    first = _assistant(
        2,
        text="",
        stop_reason="toolUse",
        tool_call=("call-1", "git_diff"),
    )
    result = {
        "role": "toolResult",
        "toolCallId": "call-1",
        "toolName": "git_diff",
        "content": [{"type": "text", "text": "clean"}],
        "details": {},
        "isError": False,
        "timestamp": 5,
    }
    second_start = _assistant(0, text="")
    final = _assistant(4, text="final after tool")
    return [
        _header(),
        {"type": "agent_start"},
        {"type": "turn_start"},
        {"type": "message_start", "message": user},
        {"type": "message_end", "message": user},
        {"type": "message_start", "message": first_start},
        {"type": "message_end", "message": first},
        {
            "type": "tool_execution_start",
            "toolCallId": "call-1",
            "toolName": "git_diff",
            "args": {"view": "status"},
        },
        {
            "type": "tool_execution_end",
            "toolCallId": "call-1",
            "toolName": "git_diff",
            "result": {"content": result["content"], "details": {}},
            "isError": False,
        },
        {"type": "message_start", "message": result},
        {"type": "message_end", "message": result},
        {"type": "turn_end", "message": first, "toolResults": [result]},
        {"type": "turn_start"},
        {"type": "message_start", "message": second_start},
        {"type": "message_end", "message": final},
        {"type": "turn_end", "message": final, "toolResults": []},
        {
            "type": "agent_end",
            "messages": [user, first, result, final],
            "willRetry": False,
        },
        {"type": "agent_settled"},
    ]


def _state(prompt: str = PROMPT) -> _EventState:
    encoded = prompt.encode("utf-8")
    return _EventState(
        expected_session_id=SESSION_ID,
        expected_prompt_sha256=hashlib.sha256(encoded).hexdigest(),
        expected_prompt_size_bytes=len(encoded),
        expected_provider="harness-leanstral",
        expected_model=MODEL,
    )


def _feed(
    events: list[dict[str, object]], prompt: str = PROMPT
) -> _EventState:
    state = _state(prompt)
    with tempfile.TemporaryDirectory(prefix="pi-event-stream-", dir="/tmp") as raw:
        root = Path(raw)
        with ExitStack() as stack:
            messages = stack.enter_context((root / "messages.jsonl").open("ab"))
            tools = stack.enter_context((root / "tools.jsonl").open("ab"))
            for event in events:
                _consume_event(
                    json.dumps(
                        event,
                        ensure_ascii=False,
                        separators=(",", ":"),
                    ).encode("utf-8")
                    + b"\n",
                    state=state,
                    messages_handle=messages,
                    tools_handle=tools,
                    token_budget=64,
                )
    return state


class EngineEventStreamTest(unittest.TestCase):
    def test_accepts_exact_no_tool_and_tool_round_sequences(self) -> None:
        for events in (_no_tool_events(), _tool_events()):
            with self.subTest(event_count=len(events)):
                state = _feed(events)
                self.assertEqual(state.phase, "settled")
                self.assertTrue(state.saw_initial_user)
                self.assertTrue(state.saw_agent_settled)
                accepted, reason, report = _validate_terminal(state, 0)
                self.assertTrue(accepted, reason)
                self.assertTrue(report)

    def test_accepts_structurally_terminal_report_blocked_without_passing(self) -> None:
        ordinary = _tool_events()
        blocked = json.loads(json.dumps(ordinary[:12]).replace("git_diff", "report_blocked"))
        user = blocked[3]["message"]
        assistant = blocked[6]["message"]
        tool_result = blocked[9]["message"]
        blocked.extend(
            [
                {
                    "type": "agent_end",
                    "messages": [user, assistant, tool_result],
                    "willRetry": False,
                },
                {"type": "agent_settled"},
            ]
        )
        state = _feed(blocked)
        accepted, reason, _ = _validate_terminal(state, 0)
        self.assertFalse(accepted)
        self.assertIn("toolUse", reason)

    def test_rejects_each_order_identity_and_usage_escape(self) -> None:
        cases: dict[str, tuple[list[dict[str, object]], str]] = {}

        wrong_session = _no_tool_events()
        wrong_session[0]["id"] = "wrong-session"
        cases["wrong_session"] = (wrong_session, "session header")

        duplicate_session = _no_tool_events()
        duplicate_session.insert(1, copy.deepcopy(duplicate_session[0]))
        cases["duplicate_session"] = (duplicate_session, "session header")

        altered_prompt = _no_tool_events()
        altered_prompt[4]["message"] = _user(PROMPT + " altered")
        cases["altered_prompt"] = (altered_prompt, "initial user message")

        assistant_before_turn = _no_tool_events()
        assistant_before_turn.pop(2)
        cases["assistant_before_turn"] = (assistant_before_turn, "out of order")

        wrong_model = _no_tool_events()
        wrong_model[5]["message"]["model"] = "unsealed-model"  # type: ignore[index]
        cases["wrong_model"] = (wrong_model, "provider/model")

        missing_usage = _no_tool_events()
        del missing_usage[7]["message"]["usage"]  # type: ignore[index]
        cases["missing_usage"] = (missing_usage, "provider usage")

        zero_final_usage = _no_tool_events()
        zero_final_usage[7]["message"]["usage"] = _usage(0)  # type: ignore[index]
        cases["zero_final_usage"] = (zero_final_usage, "invalid output-token")

        tool_before_declaration = _no_tool_events()
        tool_before_declaration.insert(
            5,
            {
                "type": "tool_execution_start",
                "toolCallId": "call-1",
                "toolName": "git_diff",
                "args": {},
            },
        )
        cases["tool_before_declaration"] = (tool_before_declaration, "tool event")

        early_agent_end = _no_tool_events()
        early_agent_end.pop(8)
        cases["early_agent_end"] = (early_agent_end, "agent_end")

        early_settled = _no_tool_events()
        early_settled.pop(9)
        cases["early_settled"] = (early_settled, "settled")

        unknown = _no_tool_events()
        unknown.insert(2, {"type": "queue_update", "steering": [], "followUp": []})
        cases["unknown"] = (unknown, "unknown event")

        compaction = _no_tool_events()
        compaction.insert(2, {"type": "compaction_start", "reason": "threshold"})
        cases["compaction"] = (compaction, "forbidden compaction")

        after_settled = _no_tool_events() + [{"type": "agent_start"}]
        cases["after_settled"] = (after_settled, "after agent_settled")

        for name, (events, message) in cases.items():
            with self.subTest(name=name):
                with self.assertRaisesRegex(PiEngineError, message):
                    _feed(events)


class _AlwaysLiveStore:
    def get_job(self, _job_id: str) -> dict[str, object]:
        return {
            "job": {
                "state": "running",
                "task_id": "stream-task",
                "task_revision": 1,
                "workspace": {"lease_owner": "stream-owner"},
            },
            "runtime": {
                "lease_active": True,
                "lease_token": 1,
                "scopes": [
                    {
                        "path": "Poincare/Test.lean",
                        "active": True,
                        "owner": "stream-owner",
                        "lease_token": 1,
                    }
                ],
            },
        }

    def get_task(self, _task_id: str) -> dict[str, object]:
        return {"task": {"revision": 1, "status": "active"}}


CHILD = r"""
import hashlib
import json
import os
import sys
import time

session_id, model, mode, expected_path = sys.argv[1:]
expected = open(expected_path, "rb").read()
if mode in {"read", "close-streams"}:
    received = sys.stdin.buffer.read()
elif mode == "early-close":
    sys.stdin.buffer.read(1)
    os.close(0)
    received = expected
elif mode == "stall":
    time.sleep(10)
    raise SystemExit(0)
else:
    raise SystemExit(2)

prompt = received.decode("utf-8")
usage = lambda output: {
    "input": 10,
    "output": output,
    "cacheRead": 0,
    "cacheWrite": 0,
    "totalTokens": 10 + output,
    "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0},
}
user = {"role": "user", "content": [{"type": "text", "text": prompt}], "timestamp": 1}
start = {
    "role": "assistant", "content": [], "api": "openai-completions",
    "provider": "harness-leanstral", "model": model, "usage": usage(0),
    "stopReason": "stop", "timestamp": 2,
}
final = {
    "role": "assistant", "content": [{"type": "text", "text": "done"}],
    "api": "openai-completions", "provider": "harness-leanstral", "model": model,
    "usage": usage(2), "stopReason": "stop", "timestamp": 3,
}
events = [
    {"type": "session", "version": 3, "id": session_id,
     "timestamp": "2026-07-19T00:00:00.000Z", "cwd": "/runtime"},
    {"type": "agent_start"},
    {"type": "turn_start"},
    {"type": "message_start", "message": user},
    {"type": "message_end", "message": user},
    {"type": "message_start", "message": start},
    {"type": "message_end", "message": final},
    {"type": "turn_end", "message": final, "toolResults": []},
    {"type": "agent_end", "messages": [user, final], "willRetry": False},
    {"type": "agent_settled"},
]
for event in events:
    print(json.dumps(event, ensure_ascii=False, separators=(",", ":")), flush=True)
if mode == "close-streams":
    os.close(1)
    os.close(2)
    time.sleep(10)
"""


class EnginePromptTransportTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="pi-transport-", dir="/tmp")
        self.root = Path(self.temporary.name)
        self.child = self.root / "child.py"
        self.child.write_text(CHILD, encoding="utf-8")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _run(
        self,
        prompt: bytes,
        mode: str,
        *,
        artifact_name: str,
    ) -> tuple[int, str, _EventState]:
        expected = self.root / f"{artifact_name}-expected.bin"
        expected.write_bytes(prompt)
        artifact_dir = self.root / artifact_name
        artifact_dir.mkdir()
        capability = {
            "session_id": SESSION_ID,
            "job_id": "stream-job",
            "task_id": "stream-task",
            "task_revision": 1,
            "lease_owner": "stream-owner",
            "lease_token": 1,
            "allowed_paths": ["Poincare/Test.lean"],
            "deadline_epoch": time.time() + 30,
            "prompt_sha256": hashlib.sha256(prompt).hexdigest(),
            "backend": {"model": MODEL},
        }
        return _run_pi_process(
            argv=[
                sys.executable,
                str(self.child),
                SESSION_ID,
                MODEL,
                mode,
                str(expected),
            ],
            env={
                "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                "PYTHONNOUSERSITE": "1",
            },
            worktree=self.root,
            prompt=prompt,
            artifact_dir=artifact_dir,
            store=_AlwaysLiveStore(),  # type: ignore[arg-type]
            capability=capability,
            disk_budget_mb=64,
            token_budget=64,
        )

    def test_retries_transient_errors_and_completes_positive_short_writes(self) -> None:
        prompt = ("TRANSPORT-SENTINEL\n" + "x" * 200_000).encode("utf-8")
        real_write = os.write
        prompt_fd: int | None = None
        injected = 0

        def controlled_write(fd: int, data: object) -> int:
            nonlocal prompt_fd, injected
            raw = bytes(data)  # type: ignore[arg-type]
            if prompt_fd is None and raw.startswith(b"TRANSPORT-SENTINEL"):
                prompt_fd = fd
            if fd != prompt_fd:
                return real_write(fd, raw)
            if injected == 0:
                injected += 1
                raise BlockingIOError(errno.EAGAIN, "try again")
            if injected == 1:
                injected += 1
                raise InterruptedError(errno.EINTR, "interrupted")
            return real_write(fd, raw[: min(len(raw), 4096)])

        with patch.object(engine.os, "write", side_effect=controlled_write):
            returncode, reason, state = self._run(
                prompt, "read", artifact_name="short-write"
            )
        self.assertEqual(returncode, 0)
        self.assertEqual(reason, "process_exit")
        self.assertEqual(state.phase, "settled")
        self.assertGreaterEqual(injected, 2)

    def test_early_stdin_close_cannot_be_masked_by_valid_events(self) -> None:
        prompt = b"E" * (1024 * 1024)
        returncode, reason, state = self._run(
            prompt, "early-close", artifact_name="early-close"
        )
        self.assertIn("canonical prompt", reason)
        self.assertNotEqual(state.phase, "settled")
        accepted, _, _ = _validate_terminal(state, returncode)
        self.assertFalse(accepted)

    def test_closed_event_streams_get_a_bounded_exit_grace(self) -> None:
        started = time.monotonic()
        returncode, reason, state = self._run(
            b"bounded stream-close grace", "close-streams", artifact_name="closed-streams"
        )
        elapsed = time.monotonic() - started
        self.assertNotEqual(returncode, 0)
        self.assertEqual(reason, "Pi closed its event streams without exiting")
        self.assertEqual(state.phase, "settled")
        self.assertGreaterEqual(elapsed, 1)
        self.assertLess(elapsed, 5)

    def test_stalled_reader_hits_bounded_inactivity_deadline(self) -> None:
        prompt = b"S" * (1024 * 1024)
        started = time.monotonic()
        with patch.object(engine, "PROMPT_WRITE_TIMEOUT_SECONDS", 0.25):
            _, reason, state = self._run(
                prompt, "stall", artifact_name="stall"
            )
        elapsed = time.monotonic() - started
        self.assertIn("transport deadline", reason)
        self.assertLess(elapsed, 4.0)
        self.assertFalse(state.saw_agent_settled)


if __name__ == "__main__":
    unittest.main()
