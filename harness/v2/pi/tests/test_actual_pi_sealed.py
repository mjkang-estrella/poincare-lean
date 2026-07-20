from __future__ import annotations

import hashlib
import json
import os
import secrets
import socketserver
import subprocess
import sys
import tempfile
import threading
import unittest
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

from harness.v2.pi import PROVIDER_NAME, TOOL_NAMES
from harness.v2.pi.engine import (
    PI_PRIVATE_SETTINGS_BYTES,
    SYSTEM_PROMPT,
    _verify_sealed_pi_install,
)
from harness.v2.pi.rpc import UnixRpcServer
from harness.v2.pi.security import audit_pi_bubblewrap, bubblewrap_pi_argv
from harness.v2.worker.artifacts import canonical_json_bytes


MANIFEST_ENV = "HARNESS_PI_E2E_INSTALL_MANIFEST"
GRAPH_ENV = "HARNESS_PI_E2E_DEPENDENCY_GRAPH"
BWRAP_ENV = "HARNESS_PI_E2E_BWRAP"
E2E_ENABLED = sys.platform == "linux" and all(
    os.environ.get(name) for name in (MANIFEST_ENV, GRAPH_ENV, BWRAP_ENV)
)
MODEL = "mistralai/Leanstral-1.5-119B-A6B"
MODEL_REVISION = "sealed-loopback-test-revision"


class _State:
    provider_requests: list[dict[str, Any]] = []


class _ProviderHandler(BaseHTTPRequestHandler):
    def log_message(self, _format: str, *_args: object) -> None:
        return

    def do_POST(self) -> None:
        length = int(self.headers.get("Content-Length", "0"))
        payload = json.loads(self.rfile.read(length))
        _State.provider_requests.append(
            {
                "path": self.path,
                "authorization": self.headers.get("Authorization"),
                "payload": payload,
            }
        )
        arguments = json.dumps(
            {
                "summary": "sealed Pi integration reached the bounded blocker tool",
                "exact_lean_type_or_error": "integration-only synthetic boundary",
                "attempted_routes": ["real Pi sealed transport and broker RPC"],
                "strongest_partial_result": "all six scoped tools were the only model tools",
            },
            separators=(",", ":"),
        )
        base = {
            "id": "chatcmpl-sealed-pi-e2e",
            "object": "chat.completion.chunk",
            "created": 1,
            "model": MODEL,
        }
        chunks = [
            {
                **base,
                "choices": [
                    {
                        "index": 0,
                        "delta": {"role": "assistant"},
                        "finish_reason": None,
                    }
                ],
            },
            {
                **base,
                "choices": [
                    {
                        "index": 0,
                        "delta": {
                            "tool_calls": [
                                {
                                    "index": 0,
                                    "id": "call-sealed-e2e",
                                    "type": "function",
                                    "function": {
                                        "name": "report_blocked",
                                        "arguments": arguments,
                                    },
                                }
                            ]
                        },
                        "finish_reason": None,
                    }
                ],
            },
            {
                **base,
                "choices": [
                    {"index": 0, "delta": {}, "finish_reason": "tool_calls"}
                ],
            },
            {
                **base,
                "choices": [],
                "usage": {
                    "prompt_tokens": 64,
                    "completion_tokens": 8,
                    "total_tokens": 72,
                },
            },
        ]
        body = b"".join(
            b"data: " + json.dumps(chunk, separators=(",", ":")).encode("utf-8") + b"\n\n"
            for chunk in chunks
        ) + b"data: [DONE]\n\n"
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


class _LoopbackServer(ThreadingHTTPServer):
    def server_bind(self) -> None:
        socketserver.TCPServer.server_bind(self)
        host, port = self.server_address[:2]
        self.server_name = str(host)
        self.server_port = int(port)


def _sealed_file(root: Path, name: str, data: bytes) -> Path:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    path.chmod(0o400)
    return path


@unittest.skipUnless(
    E2E_ENABLED,
    f"Linux sealed Pi E2E requires explicit {MANIFEST_ENV}, {GRAPH_ENV}, and {BWRAP_ENV}",
)
class ActualSealedPiIntegrationTest(unittest.TestCase):
    def test_real_attested_pi_uses_sealed_contract_and_only_scoped_rpc(self) -> None:
        manifest_path = Path(os.environ[MANIFEST_ENV]).expanduser().absolute()
        graph_path = Path(os.environ[GRAPH_ENV]).expanduser().absolute()
        bwrap = Path(os.environ[BWRAP_ENV]).expanduser().absolute()
        (
            install,
            _graph_bytes,
            _manifest_sha256,
            _sealed_manifest,
            _sealed_graph,
        ) = _verify_sealed_pi_install(
            manifest_path=manifest_path,
            dependency_graph_path=graph_path,
        )

        server = _LoopbackServer(("127.0.0.1", 0), _ProviderHandler)
        server_thread = threading.Thread(target=server.serve_forever, daemon=True)
        _State.provider_requests = []
        server_thread.start()
        self.addCleanup(server.server_close)
        self.addCleanup(lambda: server_thread.join(timeout=2))
        self.addCleanup(server.shutdown)

        with tempfile.TemporaryDirectory(prefix="sealed-pi-e2e-", dir="/tmp") as raw:
            root = Path(raw).resolve()
            inputs = root / "inputs"
            broker_root = root / "broker"
            broker_root.mkdir(mode=0o700)
            broker_socket = broker_root / "broker.sock"
            prompt = "# Sealed Pi E2E\nCall report_blocked once with the exact synthetic boundary."
            prompt_bytes = prompt.encode("utf-8")
            prompt_sha256 = hashlib.sha256(prompt_bytes).hexdigest()
            extension_bytes = (
                Path(__file__).resolve().parents[1] / "extension.ts"
            ).read_bytes()
            extension_sha256 = hashlib.sha256(extension_bytes).hexdigest()
            system_prompt_bytes = (SYSTEM_PROMPT + "\n").encode("utf-8")
            system_prompt_sha256 = hashlib.sha256(system_prompt_bytes).hexdigest()
            settings_bytes = PI_PRIVATE_SETTINGS_BYTES
            settings_sha256 = hashlib.sha256(settings_bytes).hexdigest()
            extension = _sealed_file(inputs, "extension.ts", extension_bytes)
            system_prompt = _sealed_file(
                inputs, "system-prompt.md", system_prompt_bytes
            )
            settings = _sealed_file(inputs, "settings.json", settings_bytes)

            session_id = str(uuid.uuid4())
            job_id = "sealed-pi-e2e-job"
            endpoint = f"http://127.0.0.1:{server.server_address[1]}/v1"
            public_config_bytes = canonical_json_bytes(
                {
                    "schema_version": "poincare.pi-public-config.v2",
                    "job_id": job_id,
                    "session_id": session_id,
                    "backend": {
                        "kind": "leanstral",
                        "model": MODEL,
                        "model_revision": MODEL_REVISION,
                        "endpoint": endpoint,
                        "sampling": {"max_tokens": 64, "temperature": 0},
                    },
                    "extension_sha256": extension_sha256,
                    "output_token_budget": 96,
                    "prompt_sha256": prompt_sha256,
                    "prompt_size_bytes": len(prompt_bytes),
                    "system_prompt_path": "/sealed/system-prompt.md",
                    "system_prompt_sha256": system_prompt_sha256,
                    "settings_path": "/sealed/agent/settings.json",
                    "settings_sha256": settings_sha256,
                    "broker": {
                        "socket_env": "HARNESS_PI_BROKER_SOCKET",
                        "token_env": "HARNESS_PI_BROKER_TOKEN",
                    },
                }
            )
            public_config = _sealed_file(
                inputs, "public-config.json", public_config_bytes
            )

            rpc_events: list[dict[str, Any]] = []
            broker_requests: list[dict[str, Any]] = []

            def execute(request: dict[str, Any]) -> dict[str, Any]:
                broker_requests.append(request)
                if request["tool"] != "report_blocked":
                    raise AssertionError("real Pi attempted a non-terminal scoped tool")
                return {"text": "synthetic blocker recorded", "details": {}}

            token = secrets.token_urlsafe(48)
            rpc = UnixRpcServer(
                broker_socket,
                job_id=job_id,
                session_id=session_id,
                token=token,
                execute=execute,
                append_event=rpc_events.append,
            ).start()
            self.addCleanup(rpc.close)

            sandbox = audit_pi_bubblewrap(
                configured_path=str(bwrap),
                expected_node_attestation=install["node"],
                install_root=install["install_root"],
                cli_relative=install["cli_js"]["relative_path"],
                expected_install_tree_sha256=install["tree"]["sha256"],
                extension_path=extension,
                extension_sha256=extension_sha256,
                public_config_path=public_config,
                public_config_sha256=hashlib.sha256(public_config_bytes).hexdigest(),
                system_prompt_path=system_prompt,
                system_prompt_sha256=system_prompt_sha256,
                settings_path=settings,
                settings_sha256=settings_sha256,
                broker_socket=broker_socket,
            )
            pi_arguments = [
                "--mode",
                "json",
                "--provider",
                PROVIDER_NAME,
                "--model",
                MODEL,
                "--session-id",
                session_id,
                "--session-dir",
                "/runtime/sessions",
                "--name",
                job_id,
                "--no-builtin-tools",
                "--tools",
                ",".join(TOOL_NAMES),
                "--extension",
                "/sealed/extension.ts",
                "--no-extensions",
                "--no-skills",
                "--no-prompt-templates",
                "--no-themes",
                "--no-context-files",
                "--no-approve",
                "--offline",
                "--system-prompt",
                "/sealed/system-prompt.md",
            ]
            argv = bubblewrap_pi_argv(
                spec=sandbox,
                pi_arguments=pi_arguments,
                broker_token=token,
            )
            completed = subprocess.run(
                argv,
                cwd="/",
                env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"},
                input=prompt_bytes,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=60,
                check=False,
            )
            rpc.close()
            events = [
                json.loads(line)
                for line in completed.stdout.decode("utf-8").splitlines()
                if line
            ]
            self.assertEqual(completed.returncode, 0, completed.stderr.decode("utf-8"))
            self.assertEqual(events[0]["type"], "session")
            self.assertEqual(events[0]["id"], session_id)
            self.assertTrue(any(event["type"] == "agent_settled" for event in events))
            self.assertEqual([item["tool"] for item in broker_requests], ["report_blocked"])
            self.assertTrue(
                any(item["event"] == "rpc_request_terminal" and item["ok"] for item in rpc_events)
            )
            self.assertEqual(len(_State.provider_requests), 1)
            provider = _State.provider_requests[0]
            self.assertEqual(provider["path"], "/v1/chat/completions")
            # Pi's OpenAI-compatible client requires a nonempty API-key value
            # and serializes this fixed, non-secret placeholder.  The sealed
            # environment cannot inherit or interpolate an ambient credential.
            self.assertEqual(provider["authorization"], "Bearer unused")
            payload = provider["payload"]
            self.assertEqual(payload["model"], MODEL)
            self.assertLessEqual(payload["max_tokens"], 64)
            self.assertEqual(payload["stream_options"], {"include_usage": True})
            tool_names = sorted(tool["function"]["name"] for tool in payload["tools"])
            self.assertEqual(tool_names, sorted(TOOL_NAMES))
            user_messages = [item for item in payload["messages"] if item["role"] == "user"]
            self.assertEqual(
                user_messages,
                [{"role": "user", "content": [{"type": "text", "text": prompt}]}],
            )
            self.assertEqual(
                sandbox["inputs"]["settings"]["destination"],
                "/sealed/agent/settings.json",
            )
            self.assertEqual(
                argv[-len(pi_arguments) - 2 : -len(pi_arguments)],
                ("/opt/pi-node/node", "/opt/pi-install/" + install["cli_js"]["relative_path"]),
            )


if __name__ == "__main__":
    unittest.main()
