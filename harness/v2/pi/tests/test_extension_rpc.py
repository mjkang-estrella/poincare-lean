from __future__ import annotations

import base64
import json
import re
import shutil
import subprocess
import unittest
from pathlib import Path

from harness.v2.pi.engine import PI_PRIVATE_SETTINGS_BYTES


PI_DIR = Path(__file__).resolve().parents[1]
EXTENSION = PI_DIR / "extension.ts"
TSC = PI_DIR / "node_modules/.bin/tsc"
NODE = shutil.which("node")

EXPECTED_TOOLS = [
    "read_context",
    "search_symbol",
    "apply_patch_scoped",
    "lean_check",
    "git_diff",
    "report_blocked",
]


class ExtensionRpcSourceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source = EXTENSION.read_text(encoding="utf-8")

    def _string_array(self, name: str) -> list[str]:
        match = re.search(
            rf"const\s+{re.escape(name)}\s*=\s*\[(.*?)\]\s*as const;",
            self.source,
            flags=re.DOTALL,
        )
        self.assertIsNotNone(match, f"missing inspectable {name} contract")
        return re.findall(r'"([^"\\]*(?:\\.[^"\\]*)*)"', match.group(1))

    def test_extension_has_no_process_spawn_or_host_path_contract(self) -> None:
        for forbidden in (
            "node:child_process",
            "spawn(",
            "execFile(",
            "HARNESS_PI_CAPABILITY",
            "HARNESS_PI_EXTENSION_PATH",
            "HARNESS_PI_PYTHON",
            "HARNESS_PI_SYSTEM_PROMPT_PATH",
            "PYTHONPATH",
            '"control_root"',
            '"artifact_dir"',
            '"worktree"',
        ):
            with self.subTest(forbidden=forbidden):
                self.assertNotIn(forbidden, self.source)

        node_imports = set(re.findall(r'from "(node:[^"]+)"', self.source))
        self.assertEqual(
            node_imports,
            {
                "node:crypto",
                "node:fs",
                "node:net",
                "node:path",
                "node:url",
                "node:util",
            },
        )

    def test_public_config_is_fixed_sealed_and_exact(self) -> None:
        self.assertIn(
            'const SEALED_PUBLIC_CONFIG_PATH = "/sealed/public-config.json";',
            self.source,
        )
        self.assertIn(
            'const SEALED_SYSTEM_PROMPT_PATH = "/sealed/system-prompt.md";',
            self.source,
        )
        self.assertIn(
            'const SEALED_EXTENSION_PATH = "/sealed/extension.ts";',
            self.source,
        )
        self.assertNotIn("HARNESS_PI_PUBLIC_CONFIG", self.source)
        self.assertEqual(
            self._string_array("PUBLIC_CONFIG_KEYS"),
            [
                "schema_version",
                "job_id",
                "session_id",
                "backend",
                "extension_sha256",
                "output_token_budget",
                "prompt_sha256",
                "prompt_size_bytes",
                "system_prompt_path",
                "system_prompt_sha256",
                "settings_path",
                "settings_sha256",
                "broker",
            ],
        )
        self.assertEqual(
            self._string_array("BACKEND_KEYS"),
            ["kind", "model", "model_revision", "endpoint", "sampling"],
        )
        self.assertEqual(
            self._string_array("SAMPLING_KEYS"),
            ["max_tokens", "temperature"],
        )
        self.assertEqual(
            self._string_array("BROKER_KEYS"),
            ["socket_env", "token_env"],
        )
        self.assertIn(
            "broker.socket_env !== BROKER_SOCKET_ENV || broker.token_env !== BROKER_TOKEN_ENV",
            self.source,
        )
        self.assertIn("fileURLToPath(import.meta.url)", self.source)
        self.assertIn("sha256(extension) !== config.extension_sha256", self.source)
        self.assertIn("sha256(prompt) !== config.system_prompt_sha256", self.source)
        self.assertIn(
            'const SEALED_SETTINGS_PATH = "/sealed/agent/settings.json";',
            self.source,
        )
        self.assertIn(
            "!settings.equals(PRIVATE_SETTINGS_BYTES)",
            self.source,
        )
        self.assertEqual(
            PI_PRIVATE_SETTINGS_BYTES,
            b'{"compaction":{"enabled":false}}',
        )
        self.assertIn(PI_PRIVATE_SETTINGS_BYTES.decode("ascii"), self.source)
        self.assertIn('requiredEnv("PI_CODING_AGENT_DIR")', self.source)

    def test_rpc_is_authenticated_length_prefixed_and_bounded(self) -> None:
        self.assertIn('const RPC_SCHEMA = "poincare.pi-rpc.v1";', self.source)
        self.assertEqual(
            self._string_array("RPC_REQUEST_KEYS"),
            [
                "protocol",
                "job_id",
                "session_id",
                "sequence",
                "tool_call_id",
                "tool",
                "token",
                "params",
            ],
        )
        self.assertIn(
            'const BROKER_SOCKET_ENV = "HARNESS_PI_BROKER_SOCKET";',
            self.source,
        )
        self.assertIn(
            'const BROKER_TOKEN_ENV = "HARNESS_PI_BROKER_TOKEN";',
            self.source,
        )
        self.assertRegex(
            self.source,
            r"const MAX_RPC_REQUEST_BYTES = 768 \* 1024;",
        )
        self.assertRegex(
            self.source,
            r"const MAX_RPC_RESPONSE_BYTES = 2 \* 1024 \* 1024;",
        )
        self.assertIn("const RPC_TIMEOUT_MS = 30_000;", self.source)
        self.assertIn("frame.writeUInt32BE(payload.length, 0)", self.source)
        self.assertIn("received.readUInt32BE(0)", self.source)
        self.assertIn("createConnection({ path: runtime.socketPath })", self.source)
        self.assertIn("expectedLength > MAX_RPC_RESPONSE_BYTES", self.source)
        self.assertIn("received.length > framedLength", self.source)
        self.assertIn("timer = setTimeout(", self.source)
        self.assertIn('signal?.addEventListener("abort", abort, { once: true })', self.source)

    @unittest.skipUnless(
        NODE and (PI_DIR / "node_modules").is_dir(),
        "Node and local Pi dependencies are required for the wire-byte test",
    )
    def test_canonical_frame_is_byte_exact_and_rejects_nonfinite_values(self) -> None:
        javascript = r"""
            import { encodeRpcFrame } from "./extension.ts";
            const value = {
                params: { z: [{ beta: 2, alpha: "é" }], amount: 1.25 },
                protocol: "poincare.pi-rpc.v1",
                sequence: 7,
                job_id: "rpc-test-job",
                session_id: "00000000-0000-4000-8000-000000000000",
                tool_call_id: "call-7",
                tool: "git_diff",
                token: "token_token_token_token_token_token_token_token",
            };
            const frame = encodeRpcFrame(value);
            let rejectedNonfinite = false;
            try { encodeRpcFrame({ value: Number.NaN }); }
            catch { rejectedNonfinite = true; }
            process.stdout.write(JSON.stringify({
                frame: frame.toString("base64"),
                rejectedNonfinite,
            }));
        """
        result = subprocess.run(
            [
                str(NODE),
                "--no-warnings",
                "--experimental-strip-types",
                "--input-type=module",
                "--eval",
                javascript,
            ],
            cwd=PI_DIR,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        observed = json.loads(result.stdout)
        frame = base64.b64decode(observed["frame"], validate=True)
        value = {
            "params": {"z": [{"beta": 2, "alpha": "é"}], "amount": 1.25},
            "protocol": "poincare.pi-rpc.v1",
            "sequence": 7,
            "job_id": "rpc-test-job",
            "session_id": "00000000-0000-4000-8000-000000000000",
            "tool_call_id": "call-7",
            "tool": "git_diff",
            "token": "token_token_token_token_token_token_token_token",
        }
        expected_payload = json.dumps(
            value,
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        self.assertEqual(int.from_bytes(frame[:4], "big"), len(expected_payload))
        self.assertEqual(frame[4:], expected_payload)
        self.assertTrue(observed["rejectedNonfinite"])

    def test_rpc_rejects_replay_and_mismatched_response_identity(self) -> None:
        self.assertIn("const usedToolCallIds = new Set<string>();", self.source)
        self.assertIn("usedToolCallIds.has(toolCallId)", self.source)
        self.assertIn("usedToolCallIds.add(toolCallId)", self.source)
        self.assertIn("nextSequence += 1", self.source)
        self.assertIn("reply.sequence !== sequence", self.source)
        self.assertIn("reply.tool_call_id !== toolCallId", self.source)
        self.assertEqual(
            self._string_array("RPC_RESPONSE_KEYS"),
            [
                "protocol",
                "job_id",
                "session_id",
                "sequence",
                "tool_call_id",
                "ok",
                "result",
                "error",
            ],
        )
        self.assertIn("reply.job_id !== runtime.config.job_id", self.source)
        self.assertIn("reply.session_id !== runtime.config.session_id", self.source)
        self.assertEqual(self._string_array("RPC_RESULT_KEYS"), ["text"])
        self.assertEqual(
            self._string_array("RPC_RESULT_WITH_DETAILS_KEYS"),
            ["text", "details"],
        )
        self.assertIn("reply.error !== null", self.source)
        self.assertIn("reply.result !== null", self.source)

    def test_exact_tools_prompt_sampling_and_blocked_termination_remain(self) -> None:
        self.assertEqual(self._string_array("TOOLS"), EXPECTED_TOOLS)
        self.assertEqual(self.source.count("pi.registerTool({"), len(EXPECTED_TOOLS))
        self.assertEqual(
            self.source.count('executionMode: "sequential"'),
            len(EXPECTED_TOOLS),
        )
        self.assertIn("assertProviderPromptAndTools(payload, runtime)", self.source)
        self.assertIn("payload.temperature = temperature", self.source)
        self.assertIn(
            "payload.max_tokens = budget.beginRequest(payload.max_tokens)",
            self.source,
        )
        self.assertIn("return { ...reply, terminate: true }", self.source)
        self.assertIn('pi.on("message_end", (event) => {', self.source)
        self.assertIn(
            "Harness Pi requires report_blocked to be the only call in its turn",
            self.source,
        )

    def test_prompt_usage_and_compaction_invariants_are_fail_closed(self) -> None:
        self.assertIn('pi.on("session_before_compact", () => {', self.source)
        self.assertIn('pi.on("session_compact", () => {', self.source)
        self.assertIn('pi.on("message_update", (event) => {', self.source)
        self.assertIn('pi.on("agent_settled", () => {', self.source)
        self.assertIn("assertPromptIdentity(", self.source)
        self.assertIn("budget.complete(event.message)", self.source)
        self.assertNotIn("payload.max_tokens = maxTokens", self.source)

    @unittest.skipUnless(
        NODE and (PI_DIR / "node_modules").is_dir(),
        "Node and local Pi dependencies are required for budget/prompt tests",
    )
    def test_prompt_trim_regression_and_cumulative_budget_tracker(self) -> None:
        javascript = r"""
            import { createHash } from "node:crypto";
            import {
                HarnessOutputBudget,
                assertPromptIdentity,
            } from "./extension.ts";

            const canonical = "x".repeat(29_202);
            const piped = canonical + "\n";
            const digest = createHash("sha256").update(Buffer.from(canonical)).digest("hex");
            assertPromptIdentity(canonical, digest, 29_202);
            let rejectedPretrimSnapshot = false;
            try { assertPromptIdentity(piped, digest, 29_202); }
            catch { rejectedPretrimSnapshot = true; }

            const message = (output) => ({ role: "assistant", usage: { output } });
            const budget = new HarnessOutputBudget(80, 100);
            const preservedUpstreamClamp = budget.beginRequest(50);
            budget.observe(message(30));
            budget.complete(message(40));
            const remainingClamp = budget.beginRequest(80);
            let rejectedStreamingOvershoot = false;
            try { budget.observe(message(61)); }
            catch { rejectedStreamingOvershoot = true; }

            const missing = new HarnessOutputBudget(10, 10);
            missing.beginRequest(10);
            let rejectedMissingUsage = false;
            try { missing.complete({ role: "assistant" }); }
            catch { rejectedMissingUsage = true; }

            const zero = new HarnessOutputBudget(10, 10);
            zero.beginRequest(10);
            let rejectedZeroUsage = false;
            try { zero.complete(message(0)); }
            catch { rejectedZeroUsage = true; }

            process.stdout.write(JSON.stringify({
                canonicalBytes: Buffer.byteLength(canonical),
                pipedBytes: Buffer.byteLength(piped),
                trimmedBytes: Buffer.byteLength(piped.trim()),
                rejectedPretrimSnapshot,
                preservedUpstreamClamp,
                remainingClamp,
                rejectedStreamingOvershoot,
                rejectedMissingUsage,
                rejectedZeroUsage,
            }));
        """
        result = subprocess.run(
            [
                str(NODE),
                "--no-warnings",
                "--experimental-strip-types",
                "--input-type=module",
                "--eval",
                javascript,
            ],
            cwd=PI_DIR,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        observed = json.loads(result.stdout)
        self.assertEqual(observed["pipedBytes"], 29_203)
        self.assertEqual(observed["canonicalBytes"], 29_202)
        self.assertEqual(observed["trimmedBytes"], 29_202)
        self.assertTrue(observed["rejectedPretrimSnapshot"])
        self.assertEqual(observed["preservedUpstreamClamp"], 50)
        self.assertEqual(observed["remainingClamp"], 60)
        self.assertTrue(observed["rejectedStreamingOvershoot"])
        self.assertTrue(observed["rejectedMissingUsage"])
        self.assertTrue(observed["rejectedZeroUsage"])

    def test_all_rpc_failures_use_unswallowable_exit_70(self) -> None:
        self.assertIn("const FAIL_CLOSED_EXIT_CODE = 70;", self.source)
        self.assertIn("process.exit(FAIL_CLOSED_EXIT_CODE)", self.source)
        self.assertRegex(
            self.source,
            r"runBrokerRpc\(runtime, name, toolCallId, params, signal\)\.then\(\s*"
            r"result,\s*failClosedInvariant,\s*\)",
        )
        self.assertNotRegex(self.source, r"\.catch\(\s*\(?.*?=>\s*\{?\s*return")

    @unittest.skipUnless(TSC.is_file(), "local Pi TypeScript dependencies are not installed")
    def test_extension_typechecks(self) -> None:
        result = subprocess.run(
            [
                str(TSC),
                "--noEmit",
                "--skipLibCheck",
                "--target",
                "ES2022",
                "--module",
                "NodeNext",
                "--moduleResolution",
                "NodeNext",
                "--types",
                "node",
                EXTENSION.name,
            ],
            cwd=PI_DIR,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
            text=True,
        )
        self.assertEqual(
            result.returncode,
            0,
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
        )


if __name__ == "__main__":
    unittest.main()
