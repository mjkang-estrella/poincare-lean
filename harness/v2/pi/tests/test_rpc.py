from __future__ import annotations

import json
import os
import socket
import struct
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from harness.v2.pi.rpc import UnixRpcServer, canonical_json_bytes


class UnixRpcServerTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.root.chmod(0o700)
        self.events: list[dict[str, object]] = []
        self.token = "t" * 48

    def request(self, *, token: str | None = None) -> dict[str, object]:
        return {
            "protocol": "poincare.pi-rpc.v1",
            "job_id": "job-1",
            "session_id": "session-1",
            "sequence": 1,
            "tool_call_id": "call-1",
            "tool": "git_diff",
            "token": self.token if token is None else token,
            "params": {},
        }

    def exchange(self, socket_path: Path, payload: bytes) -> dict[str, object] | None:
        connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        connection.settimeout(2)
        connection.connect(str(socket_path))
        connection.sendall(struct.pack(">I", len(payload)) + payload)
        header = connection.recv(4)
        if not header:
            connection.close()
            return None
        size = struct.unpack(">I", header)[0]
        chunks: list[bytes] = []
        remaining = size
        while remaining:
            chunk = connection.recv(remaining)
            self.assertTrue(chunk)
            chunks.append(chunk)
            remaining -= len(chunk)
        connection.close()
        return json.loads(b"".join(chunks).decode("utf-8"))

    @patch(
        "harness.v2.pi.rpc._peer_credentials",
        return_value={"pid": 123, "uid": os.getuid(), "gid": os.getgid()},
    )
    def test_authenticated_request_has_exact_terminal_evidence(self, _peer: object) -> None:
        seen: list[dict[str, object]] = []
        socket_path = self.root / "broker.sock"
        server = UnixRpcServer(
            socket_path,
            job_id="job-1",
            session_id="session-1",
            token=self.token,
            execute=lambda request: seen.append(request) or {"text": "ok"},
            append_event=self.events.append,
        ).start()
        response = self.exchange(socket_path, canonical_json_bytes(self.request()))
        server.close()
        self.assertEqual(response["ok"], True)
        self.assertEqual(response["result"], {"text": "ok"})
        self.assertEqual([event["event"] for event in self.events], [
            "rpc_request_received",
            "rpc_request_terminal",
        ])
        self.assertEqual(self.events[-1]["response_sent"], True)
        self.assertNotIn(self.token, json.dumps(self.events, sort_keys=True))
        self.assertEqual(set(seen[0]), {
            "protocol", "job_id", "session_id", "sequence",
            "tool_call_id", "tool", "params",
        })

    @patch(
        "harness.v2.pi.rpc._peer_credentials",
        return_value={"pid": 123, "uid": os.getuid(), "gid": os.getgid()},
    )
    def test_noncanonical_or_bad_token_never_reaches_executor(self, _peer: object) -> None:
        calls: list[object] = []
        for index, payload in enumerate((
            json.dumps(self.request()).encode("utf-8"),
            canonical_json_bytes(self.request(token="wrong-token-value-that-is-long-enough")),
        )):
            with self.subTest(index=index):
                socket_path = self.root / f"broker-{index}.sock"
                server = UnixRpcServer(
                    socket_path,
                    job_id="job-1",
                    session_id="session-1",
                    token=self.token,
                    execute=lambda request: calls.append(request) or {"text": "bad"},
                    append_event=self.events.append,
                ).start()
                self.assertIsNone(self.exchange(socket_path, payload))
                server.close()
        self.assertEqual(calls, [])
        self.assertEqual(
            [event["event"] for event in self.events],
            ["rpc_transport_rejected", "rpc_transport_rejected"],
        )

    @patch(
        "harness.v2.pi.rpc._peer_credentials",
        return_value={"pid": 123, "uid": os.getuid(), "gid": os.getgid()},
    )
    def test_executor_failure_is_one_bounded_error_response(self, _peer: object) -> None:
        socket_path = self.root / "broker.sock"

        def fail(_request: dict[str, object]) -> dict[str, object]:
            raise RuntimeError("denied\nwith detail")

        server = UnixRpcServer(
            socket_path,
            job_id="job-1",
            session_id="session-1",
            token=self.token,
            execute=fail,
            append_event=self.events.append,
        ).start()
        response = self.exchange(socket_path, canonical_json_bytes(self.request()))
        server.close()
        self.assertEqual(response["ok"], False)
        self.assertIsNone(response["result"])
        self.assertEqual(response["error"], "denied with detail")
        self.assertEqual(self.events[-1]["ok"], False)
        self.assertEqual(self.events[-1]["response_sent"], True)


if __name__ == "__main__":
    unittest.main()
