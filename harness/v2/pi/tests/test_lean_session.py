from __future__ import annotations

import json
import os
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch

from harness.v2.pi.lean_session import LeanProofSession, LeanSessionUnavailable, header_fingerprint


# Adversarial protocol fixture, never a compiler substitute. The real pinned
# Lean smoke below verifies elaboration and document edits independently.
PEER = r'''
import json,sys,time
mode=sys.argv[1]
def send(m):
 b=json.dumps(dict(jsonrpc="2.0",**m)).encode()
 sys.stdout.buffer.write(("Content-Length: %d\r\n\r\n"%len(b)).encode()+b)
 sys.stdout.buffer.flush()
while True:
 headers={}
 while True:
  line=sys.stdin.buffer.readline()
  if not line:sys.exit(0)
  if line==b"\r\n":break
  k,v=line.decode().split(":",1);headers[k.lower()]=v.strip()
 m=json.loads(sys.stdin.buffer.read(int(headers["content-length"])))
 if m.get("method")=="initialize":send(dict(id=m["id"],result={"capabilities":{}}))
 if m.get("method")=="textDocument/waitForDiagnostics":
  if mode=="timeout":time.sleep(30)
  if mode=="output":sys.stdout.buffer.write(b"Content-Length: 999999999\r\n\r\n");sys.stdout.buffer.flush();time.sleep(30)
  if mode=="unsupported":send(dict(id=m["id"],error={"code":-32601,"message":"missing"}));continue
  p=m["params"]
  if mode in {"progress","hostile-progress"}:
   progress=dict(method="$/lean/fileProgress",params=dict(textDocument=dict(uri=p["uri"],version=p["version"]),processing=[dict(kind=1,range=dict(start=dict(line=0,character=0),end=dict(line=1,character=0))) for _ in range(8)]))
   for _ in range(2000):send(progress)
  if mode=="diagnostic-traffic":
   for _ in range(2400):send(dict(method="textDocument/publishDiagnostics",params=dict(uri=p["uri"],version=p["version"],diagnostics=[{"severity":3,"message":"cached warning replay "*32}])))
  if mode=="fatal-progress":send(dict(method="$/lean/fileProgress",params=dict(textDocument=dict(uri=p["uri"],version=p["version"]),processing=[dict(kind=2,range=dict(start=dict(line=0,character=0),end=dict(line=1,character=0)))])))
  if mode=="diagnostic-output":send(dict(method="textDocument/publishDiagnostics",params=dict(uri=p["uri"],version=p["version"],diagnostics=[{"severity":1,"message":"x"*8192}])))
  if mode=="stderr-output":sys.stderr.buffer.write(b"x"*8192);sys.stderr.buffer.flush();time.sleep(30)
  send(dict(method="textDocument/publishDiagnostics",params=dict(uri=p["uri"],version=p["version"]-1,diagnostics=[{"severity":1,"message":"outdated"}])))
  if mode!="stale":send(dict(method="textDocument/publishDiagnostics",params=dict(uri=p["uri"],version=p["version"],diagnostics=[])))
  send(dict(id=m["id"],result={}))
'''


class LeanSessionProtocolTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.allowed = threading.Event()
        self.allowed.set()

    def session(self, mode: str = "ok", *, cap: int = 1024 * 1024) -> LeanProofSession:
        result = LeanProofSession((sys.executable, "-u", "-c", PEER, mode),
            cwd=self.directory, env=os.environ.copy(), uri=(self.directory / "Test.lean").as_uri(),
            guard=self.allowed.is_set, output_limit_bytes=cap,
            resource_limits=None, supervise_parent=False)
        self.addCleanup(result.close)
        return result

    def test_version_barrier_discards_outdated_diagnostics_and_reuses_only_exact_input(self) -> None:
        session = self.session()
        first = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
        self.assertEqual(first.returncode, 0)
        self.assertEqual(json.loads(first.stdout)["version"], 1)
        reused = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
        self.assertTrue(reused.reused_success)
        changed_dependencies = session.check("theorem x : True := by trivial\n", input_key="b", timeout_seconds=3)
        self.assertFalse(changed_dependencies.reused_success)
        self.assertEqual(changed_dependencies.document_version, 2)

    def test_stale_diagnostics_cannot_pass_current_version(self) -> None:
        session = self.session("stale")
        result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
        self.assertEqual(result.returncode, -1)
        self.assertIn(b"exact version", result.stderr)
        self.assertFalse(session.alive)

    def test_timeout_terminates_group_and_closes_session(self) -> None:
        session = self.session("timeout")
        result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=0.25)
        self.assertTrue(result.timed_out)
        self.assertFalse(session.alive)
        self.assertIsNotNone(session._process.returncode)

    def test_oversized_protocol_message_is_rejected(self) -> None:
        session = self.session("output", cap=1024)
        result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
        self.assertTrue(result.output_limited)
        self.assertFalse(session.alive)

    def test_benign_progress_over_evidence_cap_does_not_exhaust_diagnostic_queue(self) -> None:
        session = self.session("progress", cap=1024)
        result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertGreater(session._operation_bytes, 1024 * 1024)
        self.assertLessEqual(len(session._stdout), 1024)
        self.assertLessEqual(len(result.stdout) + len(result.stderr), 1024)
        self.assertTrue(session.alive)

    def test_hostile_progress_remains_bounded_by_wire_budget(self) -> None:
        with patch("harness.v2.pi.lean_session.MAX_OPERATION_WIRE_BYTES", 4096):
            session = self.session("hostile-progress", cap=1024)
            result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=5)
        self.assertTrue(result.output_limited)
        self.assertIn(b"wire traffic", result.stderr)
        self.assertFalse(session.alive)
        self.assertLessEqual(len(result.stdout) + len(result.stderr), 1024)

    def test_transient_cached_warning_traffic_can_exceed_final_evidence_cap(self) -> None:
        session = self.session("diagnostic-traffic")
        result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertGreater(result.transport["operation_wire_bytes"], 1024 * 1024)
        self.assertEqual(json.loads(result.stdout)["diagnostics"], [])

    def test_lifetime_wire_budget_stops_progress(self) -> None:
        with patch("harness.v2.pi.lean_session.MAX_SESSION_WIRE_BYTES", 4096):
            session = self.session("hostile-progress", cap=1024)
            result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=5)
        self.assertTrue(result.output_limited)
        self.assertFalse(session.alive)

    def test_large_diagnostics_and_stderr_remain_under_evidence_cap(self) -> None:
        for mode in ("diagnostic-output", "stderr-output"):
            with self.subTest(mode=mode):
                session = self.session(mode, cap=1024)
                result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
                self.assertTrue(result.output_limited)
                self.assertFalse(session.alive)
                self.assertLessEqual(len(result.stdout) + len(result.stderr), 1024)

    def test_fatal_progress_is_preserved_when_benign_progress_is_discarded(self) -> None:
        session = self.session("fatal-progress")
        result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
        self.assertEqual(result.returncode, 1)

    def test_unsupported_sync_protocol_is_explicit(self) -> None:
        session = self.session("unsupported")
        with self.assertRaises(LeanSessionUnavailable):
            session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
        self.assertFalse(session.alive)

    def test_idle_lease_revocation_terminates_server_without_another_tool_call(self) -> None:
        session = self.session()
        result = session.check("theorem x : True := by trivial\n", input_key="a", timeout_seconds=3)
        self.assertEqual(result.returncode, 0)
        self.allowed.clear()
        deadline = time.monotonic() + 3
        while session._process.returncode is None and time.monotonic() < deadline:
            time.sleep(0.02)
        self.assertIsNotNone(session._process.returncode)
        self.assertFalse(session.alive)

    def test_close_is_idempotent_and_reaps_process(self) -> None:
        session = self.session()
        session.close()
        session.close()
        self.assertIsNotNone(session._process.returncode)

    def test_header_comments_multiline_imports_and_body_edit_invalidation(self) -> None:
        text = "/- nested /- comment -/ -/\nimport Init\n  Std\nnamespace X\ntheorem x : True := by trivial\n"
        self.assertEqual(header_fingerprint(text), header_fingerprint(text.replace("trivial", "exact True.intro")))
        self.assertNotEqual(header_fingerprint(text), header_fingerprint(text.replace("Std", "Lean")))
        self.assertNotEqual(header_fingerprint(text), header_fingerprint(text.replace("import Init", "prelude\nimport Init")))


def pinned_lean() -> str | None:
    configured = os.environ.get("HARNESS_TEST_LEAN_SERVER")
    if configured:
        return configured
    root = Path(__file__).resolve().parents[4]
    toolchain = (root / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    candidate = Path.home() / ".elan/toolchains" / toolchain / "bin/lean"
    return str(candidate) if candidate.is_file() else None


@unittest.skipUnless(pinned_lean(), "requires the installed repository-pinned Lean compiler")
class RealLeanSessionTest(unittest.TestCase):
    def test_real_compiler_incremental_success_error_repair_and_fresh_agreement(self) -> None:
        import subprocess
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary).resolve()
            path = directory / "Test.lean"
            # A test-only command counts actual elaborations, proving that
            # unchanged prefix commands reuse Lean snapshots rather than just
            # a process. Production brokers conservatively use fresh mode for
            # explicit IO commands; this fixture exercises transport semantics.
            initial = (
                'import Lean\nopen Lean Elab Command\n'
                'elab "count_elaboration" : command => do\n'
                '  liftIO <| IO.FS.withFile "elaboration-count.txt" .append fun h => h.putStrLn "elaborated"\n'
                'count_elaboration\ntheorem one : 1 + 1 = 2 := by decide\n'
            )
            path.write_text(initial)
            session = LeanProofSession((pinned_lean(), "--server"), cwd=directory,
                env=os.environ.copy(), uri=path.as_uri(), guard=lambda: True,
                output_limit_bytes=1024 * 1024, resource_limits=None, supervise_parent=False)
            try:
                first = session.check(initial, input_key="base", timeout_seconds=20)
                self.assertEqual(first.returncode, 0, first.stderr)
                counter = directory / "elaboration-count.txt"
                self.assertEqual(counter.read_text().splitlines(), ["elaborated"])
                erroneous = initial + "theorem two : True := by invalidTactic\n"
                second = session.check(erroneous, input_key="edit1", timeout_seconds=20)
                self.assertEqual(second.returncode, 1)
                self.assertIn(b"unknown tactic", second.stdout)
                repaired = initial + "theorem two : True := by trivial\n"
                third = session.check(repaired, input_key="edit2", timeout_seconds=20)
                self.assertEqual(third.returncode, 0, third.stderr)
                self.assertEqual(third.document_version, 3)
                self.assertEqual(json.loads(third.stdout)["diagnostics"], [])
                self.assertEqual(counter.read_text().splitlines(), ["elaborated"])
                path.write_text(repaired)
                fresh = subprocess.run((pinned_lean(), str(path)), cwd=directory,
                    capture_output=True, timeout=20)
                self.assertEqual(fresh.returncode, third.returncode, fresh.stderr)
                self.assertEqual(counter.read_text().splitlines(), ["elaborated", "elaborated"])
            finally:
                session.close()


if __name__ == "__main__":
    unittest.main()
