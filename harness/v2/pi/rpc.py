"""Authenticated, bounded Unix-domain RPC transport for the Pi broker."""

from __future__ import annotations

import hmac
import json
import os
import socket
import stat
import struct
import threading
from pathlib import Path
from typing import Any, Callable


RPC_PROTOCOL = "poincare.pi-rpc.v1"
MAX_REQUEST_BYTES = 768 * 1024
MAX_RESPONSE_BYTES = 2 * 1024 * 1024
_REQUEST_KEYS = {
    "protocol",
    "job_id",
    "session_id",
    "sequence",
    "tool_call_id",
    "tool",
    "token",
    "params",
}
_RESULT_KEYS = {"text"}
_RESULT_OPTIONAL_KEYS = {"details"}


class RpcError(RuntimeError):
    """Raised when the local broker transport is unsafe or malformed."""


def _duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _nonfinite(raw: str) -> None:
    raise ValueError(f"non-finite JSON value: {raw}")


def canonical_json_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8", "strict")
    except (TypeError, ValueError, UnicodeError) as exc:
        raise RpcError("RPC value is not canonical UTF-8 JSON") from exc


def _parse_canonical_object(data: bytes) -> dict[str, Any]:
    try:
        value = json.loads(
            data.decode("utf-8", "strict"),
            object_pairs_hook=_duplicate_pairs,
            parse_constant=_nonfinite,
        )
    except (UnicodeError, ValueError, json.JSONDecodeError) as exc:
        raise RpcError("RPC frame is not strict UTF-8 JSON") from exc
    if not isinstance(value, dict):
        raise RpcError("RPC frame must contain one JSON object")
    if canonical_json_bytes(value) != data:
        raise RpcError("RPC frame is not canonical JSON")
    return value


def _exact_object(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        raise RpcError(f"{label} does not have its exact field set")
    return value


def _bounded_id(value: Any, label: str) -> str:
    if (
        not isinstance(value, str)
        or not value
        or len(value.encode("utf-8", "strict")) > 180
        or any(marker in value for marker in ("\x00", "\n", "\r"))
    ):
        raise RpcError(f"{label} is not a bounded identifier")
    return value


def _read_exact(connection: socket.socket, size: int) -> bytes:
    chunks: list[bytes] = []
    remaining = size
    while remaining:
        chunk = connection.recv(remaining)
        if not chunk:
            raise RpcError("RPC connection closed with a partial frame")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


def _read_frame(connection: socket.socket) -> bytes:
    header = _read_exact(connection, 4)
    (size,) = struct.unpack(">I", header)
    if size < 2 or size > MAX_REQUEST_BYTES:
        raise RpcError("RPC request frame length is outside its bound")
    return _read_exact(connection, size)


def _write_frame(connection: socket.socket, payload: bytes) -> None:
    if len(payload) > MAX_RESPONSE_BYTES:
        raise RpcError("RPC response exceeds its byte cap")
    connection.sendall(struct.pack(">I", len(payload)) + payload)


def _peer_credentials(connection: socket.socket) -> dict[str, int]:
    if not hasattr(socket, "SO_PEERCRED"):
        raise RpcError("SO_PEERCRED is required for the Pi broker")
    try:
        raw = connection.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12)
        pid, uid, gid = struct.unpack("3i", raw)
    except (OSError, struct.error) as exc:
        raise RpcError("cannot authenticate Unix-socket peer credentials") from exc
    return {"pid": pid, "uid": uid, "gid": gid}


class UnixRpcServer:
    """One-Job UDS server with exact token, peer, and frame validation."""

    def __init__(
        self,
        socket_path: Path,
        *,
        job_id: str,
        session_id: str,
        token: str,
        execute: Callable[[dict[str, Any]], dict[str, Any]],
        append_event: Callable[[dict[str, Any]], None],
        protocol: str = RPC_PROTOCOL,
        expected_peer_uid: int | None = None,
        io_timeout_seconds: float = 5.0,
    ) -> None:
        self.socket_path = Path(socket_path).expanduser().absolute()
        self.job_id = _bounded_id(job_id, "job_id")
        self.session_id = _bounded_id(session_id, "session_id")
        self.protocol = _bounded_id(protocol, "RPC protocol")
        if (
            not isinstance(token, str)
            or len(token.encode("utf-8", "strict")) < 32
            or len(token.encode("utf-8", "strict")) > 4096
            or any(marker in token for marker in ("\x00", "\n", "\r"))
        ):
            raise RpcError("RPC token must be a bounded high-entropy string")
        if (
            isinstance(io_timeout_seconds, bool)
            or not isinstance(io_timeout_seconds, (int, float))
            or not 0 < float(io_timeout_seconds) <= 30
        ):
            raise RpcError("RPC I/O timeout is invalid")
        self._token = token
        self._execute = execute
        self._append_event = append_event
        self._expected_uid = os.getuid() if expected_peer_uid is None else expected_peer_uid
        self._timeout = float(io_timeout_seconds)
        self._listener: socket.socket | None = None
        self._accept_thread: threading.Thread | None = None
        self._workers: set[threading.Thread] = set()
        self._workers_lock = threading.Lock()
        self._stop = threading.Event()

    def start(self) -> "UnixRpcServer":
        if self._listener is not None:
            raise RpcError("RPC server is already started")
        parent = self.socket_path.parent
        if parent.is_symlink() or not parent.is_dir():
            raise RpcError("RPC socket parent is not a real directory")
        metadata = parent.stat(follow_symlinks=False)
        if metadata.st_uid != os.getuid() or stat.S_IMODE(metadata.st_mode) != 0o700:
            raise RpcError("RPC socket parent must be private and owned by the engine user")
        if self.socket_path.exists() or self.socket_path.is_symlink():
            raise RpcError("RPC socket path already exists")
        listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            listener.bind(str(self.socket_path))
            os.chmod(self.socket_path, 0o600, follow_symlinks=False)
            opened = os.lstat(self.socket_path)
            if (
                not stat.S_ISSOCK(opened.st_mode)
                or opened.st_uid != os.getuid()
                or stat.S_IMODE(opened.st_mode) != 0o600
            ):
                raise RpcError("RPC socket has unsafe identity or mode")
            listener.listen(8)
            listener.settimeout(0.2)
        except Exception:
            listener.close()
            try:
                self.socket_path.unlink()
            except OSError:
                pass
            raise
        self._listener = listener
        self._accept_thread = threading.Thread(
            target=self._accept_loop,
            name=f"pi-rpc-{self.job_id}",
            daemon=True,
        )
        self._accept_thread.start()
        return self

    def _accept_loop(self) -> None:
        assert self._listener is not None
        while not self._stop.is_set():
            try:
                connection, _address = self._listener.accept()
            except socket.timeout:
                continue
            except OSError:
                if self._stop.is_set():
                    break
                continue
            worker = threading.Thread(
                target=self._serve_and_retire,
                args=(connection,),
                name=f"pi-rpc-call-{self.job_id}",
                daemon=True,
            )
            with self._workers_lock:
                self._workers.add(worker)
            worker.start()

    def _serve_and_retire(self, connection: socket.socket) -> None:
        try:
            self._serve(connection)
        finally:
            connection.close()
            with self._workers_lock:
                self._workers.discard(threading.current_thread())

    def _transport_rejected(self, reason: str, peer: dict[str, int] | None) -> None:
        bounded = str(reason).replace("\x00", " ").replace("\r", " ").replace("\n", " ")[:1024]
        self._append_event(
            {
                "event": "rpc_transport_rejected",
                "protocol": self.protocol,
                "reason": bounded or "unknown transport rejection",
                "peer": peer,
            }
        )

    def _serve(self, connection: socket.socket) -> None:
        connection.settimeout(self._timeout)
        peer: dict[str, int] | None = None
        request: dict[str, Any] | None = None
        try:
            peer = _peer_credentials(connection)
            if peer["uid"] != self._expected_uid:
                raise RpcError("RPC peer UID does not match the engine user")
            request = _exact_object(
                _parse_canonical_object(_read_frame(connection)),
                _REQUEST_KEYS,
                "RPC request",
            )
            for name in ("protocol", "job_id", "session_id", "tool_call_id", "tool"):
                _bounded_id(request[name], name)
            if request["protocol"] != self.protocol:
                raise RpcError("RPC protocol mismatch")
            if request["job_id"] != self.job_id or request["session_id"] != self.session_id:
                raise RpcError("RPC request crosses its Job/session boundary")
            if (
                isinstance(request["sequence"], bool)
                or not isinstance(request["sequence"], int)
                or not 1 <= request["sequence"] <= 2**63 - 1
            ):
                raise RpcError("RPC sequence is invalid")
            if not isinstance(request["token"], str) or not hmac.compare_digest(
                request["token"], self._token
            ):
                raise RpcError("RPC authentication failed")
        except Exception as exc:
            try:
                self._transport_rejected(str(exc), peer)
            except Exception:
                pass
            return

        assert request is not None and peer is not None
        identity = {
            "protocol": self.protocol,
            "job_id": self.job_id,
            "session_id": self.session_id,
            "sequence": request["sequence"],
            "tool_call_id": request["tool_call_id"],
            "tool_name": request["tool"],
            "peer": peer,
        }
        token_free = {
            "protocol": request["protocol"],
            "job_id": request["job_id"],
            "session_id": request["session_id"],
            "sequence": request["sequence"],
            "tool_call_id": request["tool_call_id"],
            "tool": request["tool"],
            "params": request["params"],
        }
        ok = False
        error: str | None = None
        result: dict[str, Any] | None = None
        response_sent = False
        try:
            self._append_event(
                {
                    "event": "rpc_request_received",
                    **identity,
                    "params": request["params"],
                }
            )
            raw_result = self._execute(token_free)
            if not isinstance(raw_result, dict) or set(raw_result) not in (
                _RESULT_KEYS,
                _RESULT_KEYS | _RESULT_OPTIONAL_KEYS,
            ):
                raise RpcError("RPC result does not have its exact field set")
            if not isinstance(raw_result.get("text"), str):
                raise RpcError("RPC result text is not a string")
            result = raw_result
            ok = True
        except Exception as exc:
            error = str(exc).replace("\x00", " ").replace("\r", " ").replace("\n", " ")[:4096]
            error = error or "broker rejected the request"

        response = {
            "protocol": self.protocol,
            "job_id": self.job_id,
            "session_id": self.session_id,
            "sequence": request["sequence"],
            "tool_call_id": request["tool_call_id"],
            "ok": ok,
            "result": result if ok else None,
            "error": None if ok else error,
        }
        try:
            payload = canonical_json_bytes(response)
            if len(payload) > MAX_RESPONSE_BYTES:
                response["ok"] = False
                response["result"] = None
                response["error"] = "broker response exceeds its byte cap"
                ok = False
                error = response["error"]
                payload = canonical_json_bytes(response)
            _write_frame(connection, payload)
            response_sent = True
        except Exception as exc:
            ok = False
            error = str(exc)[:4096] or "RPC response write failed"
        finally:
            try:
                self._append_event(
                    {
                        "event": "rpc_request_terminal",
                        **identity,
                        "ok": ok,
                        "error": None if ok else error,
                        "response_sent": response_sent,
                    }
                )
            except Exception:
                pass

    def close(self) -> None:
        self._stop.set()
        listener = self._listener
        self._listener = None
        if listener is not None:
            listener.close()
        if self._accept_thread is not None:
            self._accept_thread.join(timeout=2)
            self._accept_thread = None
        deadline_workers: list[threading.Thread]
        with self._workers_lock:
            deadline_workers = list(self._workers)
        for worker in deadline_workers:
            worker.join(timeout=self._timeout + 1)
        with self._workers_lock:
            if any(worker.is_alive() for worker in self._workers):
                raise RpcError("RPC worker did not terminate within its bound")
        try:
            self.socket_path.unlink()
        except FileNotFoundError:
            pass
        except OSError as exc:
            raise RpcError(f"cannot remove closed RPC socket: {exc}") from exc

    def __enter__(self) -> "UnixRpcServer":
        return self.start()

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()


__all__ = [
    "MAX_REQUEST_BYTES",
    "MAX_RESPONSE_BYTES",
    "RPC_PROTOCOL",
    "RpcError",
    "UnixRpcServer",
    "canonical_json_bytes",
]
