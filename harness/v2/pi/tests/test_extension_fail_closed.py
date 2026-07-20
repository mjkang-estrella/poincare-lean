from __future__ import annotations

import hashlib
import json
import os
import shutil
import socketserver
import subprocess
import tempfile
import threading
import unittest
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

from harness.v2.pi import PI_VERSION, TOOL_NAMES
from harness.v2.pi.engine import SYSTEM_PROMPT
from harness.v2.pi.integrity import TRUSTED_CODE_PATHS


MODEL = "mistralai/Leanstral-1.5-119B-A6B"
REVISION = "fail-closed-test-revision"
FAIL_CLOSED_EXIT_CODE = 70


class _ProviderState:
    requests: list[dict[str, Any]] = []


class _ProviderHandler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return

    def do_POST(self) -> None:
        length = int(self.headers.get("Content-Length", "0"))
        payload = json.loads(self.rfile.read(length))
        _ProviderState.requests.append({"path": self.path, "payload": payload})
        base = {
            "id": "chatcmpl-pi-fail-closed-test",
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
                        "delta": {"role": "assistant", "content": "unexpected"},
                        "finish_reason": None,
                    }
                ],
            },
            {
                **base,
                "choices": [{"index": 0, "delta": {}, "finish_reason": "stop"}],
            },
        ]
        body = b"".join(
            b"data: " + json.dumps(chunk).encode("utf-8") + b"\n\n"
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


def _trusted_manifest(control_root: Path) -> dict[str, Any]:
    files: list[dict[str, Any]] = []
    aggregate = hashlib.sha256()
    aggregate.update(b"poincare-harness-v2-trusted-code-v1\0")
    for relative in TRUSTED_CODE_PATHS:
        data = (control_root / relative).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        files.append(
            {"path": relative, "sha256": digest, "size_bytes": len(data)}
        )
        aggregate.update(
            f"{relative}\0{digest}\0{len(data)}\n".encode("utf-8")
        )
    return {
        "schema_version": "poincare.pi-trusted-code.v1",
        "git_commit": "0" * 40,
        "aggregate_sha256": aggregate.hexdigest(),
        "files": files,
    }


@unittest.skipUnless(
    os.environ.get("PI_08010_BIN"),
    "set PI_08010_BIN to run the actual pinned Pi fail-closed regression",
)
@unittest.skip(
    "obsolete unsandboxed extension fixture; fail-closed RPC behavior is covered by the sealed transport tests"
)
class ActualPiFailClosedTest(unittest.TestCase):
    def test_prompt_mismatch_exits_before_provider_request(self) -> None:
        pi_bin = Path(os.environ["PI_08010_BIN"]).resolve(strict=True)
        version = subprocess.run(
            [str(pi_bin), "-v"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        self.assertEqual(version, PI_VERSION)

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            agent_dir = root / "agent"
            session_dir = root / "sessions"
            pycache_dir = agent_dir / "pycache"
            agent_dir.mkdir()
            session_dir.mkdir()
            pycache_dir.mkdir()
            source_root = Path(__file__).resolve().parents[4]
            for relative in TRUSTED_CODE_PATHS:
                source = source_root / relative
                destination = root / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)

            extension = root / "harness/v2/pi/extension.ts"
            extension_hash = hashlib.sha256(extension.read_bytes()).hexdigest()
            immutable_prompt = root / "immutable-system-prompt.md"
            immutable_prompt.write_text(SYSTEM_PROMPT + "\n", encoding="utf-8")
            immutable_prompt_hash = hashlib.sha256(
                immutable_prompt.read_bytes()
            ).hexdigest()
            mismatched_prompt = root / "mismatched-system-prompt.md"
            mismatched_prompt.write_text(
                "This prompt is outside the immutable Job artifact.\n",
                encoding="utf-8",
            )

            server = _LoopbackServer(("127.0.0.1", 0), _ProviderHandler)
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            _ProviderState.requests = []
            thread.start()
            self.addCleanup(server.server_close)
            self.addCleanup(lambda: thread.join(timeout=2))
            self.addCleanup(server.shutdown)
            endpoint = f"http://127.0.0.1:{server.server_address[1]}/v1"

            capability = {
                "schema_version": "poincare.pi-capability.v1",
                "job_id": "actual-pi-fail-closed-test",
                "control_root": str(root),
                "backend": {
                    "kind": "leanstral",
                    "model": MODEL,
                    "model_revision": REVISION,
                    "endpoint": endpoint,
                    "sampling": {"max_tokens": 64, "temperature": 0},
                },
                "extension_sha256": extension_hash,
                "system_prompt_sha256": immutable_prompt_hash,
                "trusted_code": _trusted_manifest(root),
            }
            capability_path = root / "capability.json"
            capability_path.write_text(
                json.dumps(capability, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            capability_hash = hashlib.sha256(
                capability_path.read_bytes()
            ).hexdigest()
            argv = [
                str(pi_bin),
                "--mode",
                "json",
                "--provider",
                "harness-leanstral",
                "--model",
                MODEL,
                "--session-id",
                str(uuid.uuid4()),
                "--session-dir",
                str(session_dir),
                "--name",
                "actual-pi-fail-closed-test",
                "--no-builtin-tools",
                "--tools",
                ",".join(TOOL_NAMES),
                "--extension",
                str(extension),
                "--no-extensions",
                "--no-skills",
                "--no-prompt-templates",
                "--no-themes",
                "--no-context-files",
                "--no-approve",
                "--offline",
                "--system-prompt",
                str(mismatched_prompt),
            ]
            safe_env = {
                "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
                "HOME": str(root),
                "LANG": "C.UTF-8",
                "TMPDIR": str(root),
                "PYTHONPATH": str(source_root),
                "PYTHONPYCACHEPREFIX": str(pycache_dir),
                "PYTHONSAFEPATH": "1",
                "PYTHONNOUSERSITE": "1",
                "PI_CODING_AGENT_DIR": str(agent_dir),
                "PI_OFFLINE": "1",
                "PI_SKIP_VERSION_CHECK": "1",
                "PI_TELEMETRY": "0",
                "NO_PROXY": "127.0.0.1",
                "no_proxy": "127.0.0.1",
                "HARNESS_PI_CAPABILITY": str(capability_path),
                "HARNESS_PI_CAPABILITY_SHA256": capability_hash,
                "HARNESS_PI_EXTENSION_PATH": str(extension),
                "HARNESS_PI_EXTENSION_SHA256": extension_hash,
                "HARNESS_PI_SYSTEM_PROMPT_PATH": str(immutable_prompt),
                "HARNESS_PI_SYSTEM_PROMPT_SHA256": immutable_prompt_hash,
                "HARNESS_PI_PYTHON": os.path.realpath(os.sys.executable),
                "HARNESS_PI_CONTEXT_WINDOW": "200000",
            }
            result = subprocess.run(
                argv,
                cwd=root,
                env=safe_env,
                input="# bounded fail-closed test\n",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                check=False,
                text=True,
            )

            self.assertEqual(
                result.returncode,
                FAIL_CLOSED_EXIT_CODE,
                f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
            )
            self.assertIn(
                "Harness Pi invariant failure: Harness Pi system prompt did not "
                "come from its immutable artifact",
                result.stderr,
            )
            self.assertEqual(_ProviderState.requests, [], result.stderr)


if __name__ == "__main__":
    unittest.main()
