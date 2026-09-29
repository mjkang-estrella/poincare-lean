"""Bounded Lean LSP transport for broker-owned proof iteration.

This module does not select an executable or mount host paths. Production
callers must supply the attested, networkless sparse-sandbox argv from security.
Each operation waits for Lean's versioned ``waitForDiagnostics`` barrier, never
for a quiet interval. Final acceptance remains a separate fresh compiler run.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import selectors
import subprocess
import sys
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Sequence

from .security import (
    ProcessResourceLimits,
    _bounded_process_preexec,
    _leader_exited_without_reaping,
    _terminate_and_reap,
)

MAX_DOCUMENT_BYTES = 2 * 1024 * 1024
MAX_HEADER_BYTES = 8192
MAX_PROTOCOL_MESSAGE_BYTES = 8 * 1024 * 1024
MAX_OPERATION_WIRE_BYTES = 32 * 1024 * 1024
MAX_SESSION_WIRE_BYTES = 128 * 1024 * 1024
MAX_QUEUED_MESSAGES = 2048


class LeanSessionError(RuntimeError):
    def __init__(self, message: str, kind: str = "protocol") -> None:
        super().__init__(message)
        self.kind = kind


class LeanSessionUnavailable(LeanSessionError):
    """The pinned compiler explicitly lacks the synchronization protocol."""


def header_fingerprint(text: str) -> str:
    """Conservatively bind all header syntax, including multiline imports.

    Strip comments/strings only for locating the first body command; hash the
    original prefix. Unknown header syntax hashes the entire document, causing
    extra restarts instead of unsafe reuse. Lean's module header precedes any
    namespace/open/definition command.
    """
    masked = list(text)
    index, depth, string = 0, 0, False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                masked[index:index + 2] = "  "
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                masked[index:index + 2] = "  "
                index += 2
            else:
                if text[index] != "\n":
                    masked[index] = " "
                index += 1
        elif string:
            if text[index] == "\\":
                masked[index:index + 2] = " " * min(2, len(text) - index)
                index += 2
            else:
                if text[index] == '"':
                    string = False
                if text[index] != "\n":
                    masked[index] = " "
                index += 1
        elif text.startswith("/-", index):
            depth = 1
            masked[index:index + 2] = "  "
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            masked[index:end] = " " * (end - index)
            index = end
        elif text[index] == '"':
            string = True
            masked[index] = " "
            index += 1
        else:
            index += 1
    # The first body keyword closes the module header. Header/body changes
    # before this point restart. No import can occur after a body command.
    body = re.search(
        r"(?m)^\s*(?:namespace|section|end|open|export|variable|universe|"
        r"set_option|attribute|theorem|lemma|def|abbrev|opaque|axiom|instance|"
        r"structure|class|inductive|example|#|noncomputable\s+section)\b",
        "".join(masked),
    )
    prefix = text[:body.start()] if body else text
    return hashlib.sha256(prefix.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class LeanSessionResult:
    argv: tuple[str, ...]
    returncode: int
    stdout: bytes
    stderr: bytes
    timed_out: bool
    output_limited: bool
    guard_cancelled: bool
    duration_seconds: float
    document_version: int
    reused_success: bool
    phase_seconds: dict[str, float]
    transport: dict[str, int] = field(default_factory=dict)


class LeanProofSession:
    """One document, one isolated compiler process group, one live capability."""

    def __init__(
        self,
        argv: Sequence[str],
        *,
        cwd: Path,
        env: dict[str, str],
        uri: str,
        guard: Callable[[], bool],
        output_limit_bytes: int,
        resource_limits: ProcessResourceLimits | None,
        supervise_parent: bool = True,
    ) -> None:
        if not argv or not uri.startswith("file://") or output_limit_bytes < 1:
            raise LeanSessionError("invalid Lean session transport configuration")
        if not self._guard_allowed(guard):
            raise LeanSessionError("live Job capability was revoked", "guard")
        self.argv, self.uri = tuple(argv), uri
        self.guard = guard
        self.output_limit = output_limit_bytes
        self._condition = threading.Condition()
        self._termination_lock = threading.Lock()
        self._messages: deque[tuple[dict[str, Any], int]] = deque()
        self._queued_bytes = 0
        self._buffer = bytearray()
        self._stdout, self._stderr = bytearray(), bytearray()
        self._operation_bytes, self._lifetime_bytes = 0, 0
        self._dropped_progress = 0
        self._fatal: LeanSessionError | None = None
        self._stop = threading.Event()
        self._initialized, self._opened = False, False
        self._version, self._request_id = 0, 0
        self._last_success: tuple[str, LeanSessionResult] | None = None
        self._process = subprocess.Popen(
            list(argv), cwd=cwd, env=env, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False,
            start_new_session=True,
            preexec_fn=_bounded_process_preexec(
                expected_parent=os.getpid() if supervise_parent and sys.platform == "linux" else None,
                limits=resource_limits,
            ),
        )
        for stream in (self._process.stdin, self._process.stdout, self._process.stderr):
            assert stream is not None
            os.set_blocking(stream.fileno(), False)
        self._pump = threading.Thread(target=self._read_loop, name="lean-session-guard", daemon=True)
        self._pump.start()

    @staticmethod
    def _guard_allowed(guard: Callable[[], bool]) -> bool:
        try:
            return bool(guard())
        except Exception:
            return False

    @property
    def alive(self) -> bool:
        return not self._stop.is_set() and self._fatal is None

    def _terminate(self) -> None:
        with self._termination_lock:
            if self._process.returncode is None:
                _terminate_and_reap(self._process)

    def _fail(self, error: LeanSessionError) -> None:
        with self._condition:
            if self._fatal is None:
                self._fatal = error
            self._stop.set()
            self._condition.notify_all()

    def _parse_frames(self) -> None:
        while self._buffer:
            split = self._buffer.find(b"\r\n\r\n")
            if split < 0:
                if len(self._buffer) > MAX_HEADER_BYTES:
                    raise LeanSessionError("Lean LSP header exceeds its cap", "output")
                return
            header = bytes(self._buffer[:split])
            if len(header) > MAX_HEADER_BYTES:
                raise LeanSessionError("Lean LSP header exceeds its cap", "output")
            lengths = re.findall(rb"(?im)^Content-Length: ([0-9]+)\r?$", header)
            if len(lengths) != 1 or len(lengths[0]) > 10:
                raise LeanSessionError("Lean LSP Content-Length is invalid")
            length = int(lengths[0])
            if length > MAX_PROTOCOL_MESSAGE_BYTES:
                raise LeanSessionError("Lean LSP message exceeds its cap", "output")
            end = split + 4 + length
            if len(self._buffer) < end:
                return
            data = bytes(self._buffer[split + 4:end])
            del self._buffer[:end]
            try:
                message = json.loads(data.decode("utf-8"))
            except (UnicodeDecodeError, ValueError, RecursionError) as exc:
                raise LeanSessionError("Lean LSP message is invalid JSON") from exc
            if not isinstance(message, dict) or message.get("jsonrpc") != "2.0":
                raise LeanSessionError("Lean LSP message has an invalid envelope")
            if "method" in message and (not isinstance(message["method"], str) or len(message["method"]) > 128):
                raise LeanSessionError("Lean LSP method is invalid")
            if "id" in message and (isinstance(message["id"], bool) or
                    not isinstance(message["id"], (str, int)) or len(str(message["id"])) > 180):
                raise LeanSessionError("Lean LSP response ID is invalid")
            if "params" in message and not isinstance(message["params"], dict):
                raise LeanSessionError("Lean LSP parameters are invalid")
            if "id" not in message:
                # Progress is transport traffic, not compiler diagnostics.
                # Charge every byte against the wire budgets, but do not
                # retain redundant nonsemantic telemetry in the bounded
                # diagnostic queue. Fatal progress remains observable.
                method = message.get("method")
                if method == "$/lean/fileProgress":
                    params = message.get("params", {})
                    document, processing = params.get("textDocument"), params.get("processing")
                    if not isinstance(document, dict) or not isinstance(processing, list) or any(
                            not isinstance(item, dict) or isinstance(item.get("kind", 1), bool) or
                            item.get("kind", 1) not in {1, 2} for item in processing):
                        raise LeanSessionError("Lean file progress is invalid")
                    if all(item.get("kind", 1) == 1 for item in processing):
                        self._dropped_progress += 1
                        continue
                elif method in {
                    "$/lean/importClosure", "$/lean/ileanInfoUpdate",
                    "$/lean/ileanInfoFinal", "$/lean/ileanHeaderSetupInfo", "$/progress",
                }:
                    self._dropped_progress += 1
                    continue
            self._messages.append((message, length))
            self._queued_bytes += length
            if len(self._messages) > MAX_QUEUED_MESSAGES or self._queued_bytes > self.output_limit:
                raise LeanSessionError("Lean LSP unread message queue exceeds its cap", "output")

    def _read_loop(self) -> None:
        selector = selectors.DefaultSelector()
        next_guard = time.monotonic()
        try:
            selector.register(self._process.stdout, selectors.EVENT_READ, "stdout")
            selector.register(self._process.stderr, selectors.EVENT_READ, "stderr")
            while not self._stop.is_set():
                now = time.monotonic()
                if now >= next_guard:
                    next_guard = now + 0.25
                    if not self._guard_allowed(self.guard):
                        raise LeanSessionError("live Job capability was revoked", "guard")
                if _leader_exited_without_reaping(self._process):
                    raise LeanSessionError("Lean server exited unexpectedly", "process")
                for key, _ in selector.select(timeout=0.1):
                    data = os.read(key.fileobj.fileno(), 8192)
                    if not data:
                        selector.unregister(key.fileobj)
                        continue
                    with self._condition:
                        self._lifetime_bytes += len(data)
                        self._operation_bytes += len(data)
                        stream = getattr(self, f"_{key.data}")
                        remaining = max(0, self.output_limit - len(stream))
                        stream.extend(data[:remaining])
                        if self._operation_bytes > MAX_OPERATION_WIRE_BYTES or self._lifetime_bytes > MAX_SESSION_WIRE_BYTES:
                            raise LeanSessionError("Lean session wire traffic exceeds its cap", "output")
                        if key.data == "stderr" and len(data) > remaining:
                            raise LeanSessionError("Lean session stderr exceeds its output cap", "output")
                        if key.data == "stdout":
                            self._buffer.extend(data)
                            self._parse_frames()
                        self._condition.notify_all()
        except LeanSessionError as exc:
            self._fail(exc)
        except Exception as exc:
            self._fail(LeanSessionError(f"Lean session transport failed: {exc}"))
        finally:
            selector.close()
            self._terminate()
            with self._condition:
                self._condition.notify_all()

    def _send(self, message: dict[str, Any], deadline: float) -> None:
        data = json.dumps(message, ensure_ascii=True, allow_nan=False, separators=(",", ":")).encode()
        if len(data) > 6 * MAX_DOCUMENT_BYTES:
            raise LeanSessionError("Lean LSP input exceeds its cap", "output")
        payload = memoryview(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        while payload:
            self._check_deadline(deadline)
            try:
                count = os.write(self._process.stdin.fileno(), payload)
                payload = payload[count:]
            except BlockingIOError:
                with self._condition:
                    self._condition.wait(timeout=0.05)
            except OSError as exc:
                raise LeanSessionError(f"cannot write to Lean server: {exc}", "process") from exc

    def _check_deadline(self, deadline: float) -> None:
        if self._fatal:
            raise self._fatal
        if self._stop.is_set():
            raise LeanSessionError("Lean session is closed", "process")
        if time.monotonic() >= deadline:
            raise LeanSessionError("Lean session operation timed out", "timeout")
        if not self._guard_allowed(self.guard):
            raise LeanSessionError("live Job capability was revoked", "guard")

    def _notify(self, method: str, params: dict[str, Any], deadline: float) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params}, deadline)

    def _request(self, method: str, params: dict[str, Any], deadline: float,
                 on_notification: Callable[[dict[str, Any]], None] = lambda _message: None) -> Any:
        self._request_id += 1
        request_id = self._request_id
        self._send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params}, deadline)
        while True:
            self._check_deadline(deadline)
            with self._condition:
                if not self._messages:
                    self._condition.wait(timeout=min(0.1, max(0, deadline - time.monotonic())))
                    continue
                message, message_bytes = self._messages.popleft()
                self._queued_bytes -= message_bytes
            if "method" in message:
                if "id" in message:
                    # Never honor server requests to write files or perform
                    # operations outside the fixed transport protocol.
                    if message["method"] == "workspace/configuration":
                        items = message.get("params", {}).get("items", [])
                        if not isinstance(items, list) or len(items) > 64:
                            raise LeanSessionError("Lean configuration request exceeds its cap")
                        response = {"result": [{} for _ in items]}
                    elif message["method"] in {"client/registerCapability", "workspace/semanticTokens/refresh", "workspace/inlayHint/refresh"}:
                        response = {"result": None}
                    else:
                        response = {"error": {"code": -32601, "message": "unsupported broker request"}}
                    self._send({"jsonrpc": "2.0", "id": message["id"], **response}, deadline)
                else:
                    on_notification(message)
                continue
            if message.get("id") != request_id:
                raise LeanSessionError("unexpected Lean LSP response ID")
            if "error" in message:
                error = message["error"]
                if method == "textDocument/waitForDiagnostics" and isinstance(error, dict) and error.get("code") == -32601:
                    raise LeanSessionUnavailable("pinned Lean server lacks waitForDiagnostics")
                raise LeanSessionError(f"Lean LSP request failed: {error}")
            if "result" not in message:
                raise LeanSessionError("Lean LSP response lacks a result")
            return message["result"]

    def check(self, text: str, *, input_key: str, timeout_seconds: float) -> LeanSessionResult:
        """Check exact bytes after the caller reattests every non-document input."""
        if len(text.encode("utf-8")) > MAX_DOCUMENT_BYTES or timeout_seconds <= 0:
            raise LeanSessionError("Lean document or check timeout exceeds its cap")
        started, phases = time.monotonic(), {}
        deadline = started + timeout_seconds
        exact_key = hashlib.sha256(input_key.encode("utf-8") + b"\0" + text.encode("utf-8")).hexdigest()
        try:
            self._check_deadline(deadline)
            with self._condition:
                self._stdout.clear()
                self._stderr.clear()
                self._operation_bytes = 0
                self._dropped_progress = 0
            if self._last_success is not None and self._last_success[0] == exact_key:
                previous = self._last_success[1]
                return LeanSessionResult(self.argv, 0, previous.stdout, previous.stderr,
                                         False, False, False, time.monotonic() - started,
                                         self._version, True, {"identical_input_reuse": time.monotonic() - started}, self._transport_details())
            if not self._initialized:
                initialize_started = time.monotonic()
                self._request("initialize", {"processId": None, "rootUri": None,
                    "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}},
                    "initializationOptions": {"hasWidgets": False}}, deadline)
                self._notify("initialized", {}, deadline)
                self._initialized = True
                phases["server_initialize"] = time.monotonic() - initialize_started
            self._version += 1
            version = self._version
            if self._opened:
                self._notify("textDocument/didChange", {"textDocument": {"uri": self.uri, "version": version},
                    "contentChanges": [{"text": text}]}, deadline)
            else:
                self._notify("textDocument/didOpen", {"textDocument": {"uri": self.uri,
                    "languageId": "lean4", "version": version, "text": text},
                    "dependencyBuildMode": "never"}, deadline)
                self._opened = True
            diagnostics: list[dict[str, Any]] | None = None
            diagnostics_bytes = 0
            fatal_progress = False

            def notification(message: dict[str, Any]) -> None:
                nonlocal diagnostics, diagnostics_bytes, fatal_progress
                params = message.get("params", {})
                if not isinstance(params, dict):
                    raise LeanSessionError("Lean notification parameters are invalid")
                if message["method"] == "textDocument/publishDiagnostics" and params.get("uri") == self.uri:
                    if params.get("version") != version:
                        return  # Explicitly discard all outdated diagnostics.
                    items = params.get("diagnostics")
                    if not isinstance(items, list) or any(not isinstance(item, dict) for item in items):
                        raise LeanSessionError("Lean diagnostics are invalid")
                    items_bytes = len(json.dumps(items, ensure_ascii=True, separators=(",", ":")).encode())
                    if params.get("isIncremental") is True:
                        diagnostics_bytes += items_bytes
                        diagnostics = (diagnostics or []) + items
                    else:
                        diagnostics_bytes = items_bytes
                        diagnostics = items
                    if diagnostics_bytes > self.output_limit:
                        raise LeanSessionError("Lean diagnostic payload exceeds its output cap", "output")
                elif message["method"] == "$/lean/fileProgress":
                    document = params.get("textDocument", {})
                    processing = params.get("processing", [])
                    if not isinstance(document, dict) or not isinstance(processing, list) or any(not isinstance(item, dict) for item in processing):
                        raise LeanSessionError("Lean file progress is invalid")
                    if document.get("uri") == self.uri and document.get("version") == version:
                        fatal_progress = any(item.get("kind") == 2 for item in processing)

            check_started = time.monotonic()
            self._request("textDocument/waitForDiagnostics", {"uri": self.uri, "version": version}, deadline, notification)
            phases["import_load_and_elaboration"] = time.monotonic() - check_started
            self._check_deadline(deadline)
            if diagnostics is None:
                raise LeanSessionError("Lean synchronization finished without diagnostics for the exact version")
            errors = fatal_progress or any(item.get("severity", 1) == 1 for item in diagnostics)
            rendered = json.dumps({"uri": self.uri, "version": version, "diagnostics": diagnostics},
                                  ensure_ascii=True, sort_keys=True).encode() + b"\n"
            if len(rendered) + len(self._stderr) > self.output_limit:
                raise LeanSessionError("rendered Lean diagnostics exceed the output cap", "output")
            result = LeanSessionResult(self.argv, 1 if errors else 0, rendered, bytes(self._stderr),
                                      False, False, False, time.monotonic() - started,
                                      version, False, phases, self._transport_details())
            self._last_success = (exact_key, result) if not errors else None
            return result
        except LeanSessionUnavailable:
            self.close()
            raise
        except LeanSessionError as exc:
            self._fail(exc)
            error = (str(exc) + "\n").encode()[:min(8192, self.output_limit)]
            stdout = bytes(self._stdout)[:max(0, self.output_limit - len(error))]
            stderr = bytes(self._stderr)[:max(0, self.output_limit - len(error) - len(stdout))] + error
            result = LeanSessionResult(self.argv, -1, stdout, stderr, exc.kind == "timeout",
                exc.kind == "output", exc.kind == "guard", time.monotonic() - started,
                self._version, False, phases, self._transport_details())
            self.close()
            return result

    def _transport_details(self) -> dict[str, int]:
        with self._condition:
            return {"operation_wire_bytes": self._operation_bytes,
                    "lifetime_wire_bytes": self._lifetime_bytes,
                    "dropped_telemetry_messages": self._dropped_progress,
                    "operation_wire_cap_bytes": MAX_OPERATION_WIRE_BYTES,
                    "lifetime_wire_cap_bytes": MAX_SESSION_WIRE_BYTES,
                    "message_cap_bytes": MAX_PROTOCOL_MESSAGE_BYTES,
                    "diagnostic_evidence_cap_bytes": self.output_limit}

    def close(self) -> None:
        self._stop.set()
        self._terminate()
        if threading.current_thread() is not self._pump:
            self._pump.join(timeout=3)
            if self._pump.is_alive():
                raise LeanSessionError("Lean session output supervisor could not stop")
        for stream in (self._process.stdin, self._process.stdout, self._process.stderr):
            if stream is not None:
                stream.close()
