from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch

from harness.v2.deploy import focused_review as focused
from harness.v2.runtime.store import _validate_gate_document
from harness.v2.tests.test_statement_contracts import strict_task


ROOT = Path(__file__).resolve().parents[4]


def success_output(task: dict) -> bytes:
    lines = []
    for symbol in task["acceptance"]["required_declarations"]:
        lines.append(f"AXIOM_CONTRACT_OK: {symbol}")
        if task["schema_version"] == "2.1":
            lines.append(f"FROZEN_CONTRACT_OK: {symbol}")
    return ("\n".join(lines) + "\n").encode()


class FocusedProbeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.artifacts = Path(self.temporary.name)
        self.review = self.artifacts / "review"
        self.review.mkdir()
        self.task, _ = strict_task()
        self.timings: list[dict] = []

    def run_batch(self):
        return focused._run_declaration_batch(
            self.task,
            lean=Path("/pinned/bin/lean"),
            cwd=self.artifacts,
            environment={"LEAN_NUM_THREADS": "1"},
            timeout_seconds=30,
            review_dir=self.review,
            timings=self.timings,
        )

    def test_batch_has_one_root_import_and_all_exact_type_and_axiom_checks(self):
        symbols = self.task["acceptance"]["required_declarations"]
        source = focused._batched_declaration_source(self.task, symbols)
        self.assertEqual(source.splitlines().count("import Poincare"), 1)
        self.assertEqual(source.splitlines().count("import Lean"), 1)
        for entry in self.task["statement_contract"]["declarations"]:
            self.assertIn(json.dumps(entry["lean_type"], ensure_ascii=False), source)
            self.assertIn(f'FROZEN_CONTRACT_OK: {entry["name"]}', source)
            self.assertIn(f'AXIOM_CONTRACT_OK: {entry["name"]}', source)
        self.assertIn("isDefEq actual expected", source)
        self.assertIn("info.levelParams.length", source)
        self.assertIn("info.isUnsafe || info.isPartial", source)
        self.assertIn("collectAxioms name", source)

    def test_one_process_retains_per_symbol_canonical_runtime_evidence(self):
        stdout = success_output(self.task)
        with patch.object(focused.subprocess, "run", return_value=subprocess.CompletedProcess(
            ["lean", "--stdin"], 0, stdout, b""
        )) as execute:
            declarations, batch = self.run_batch()
        self.assertEqual(execute.call_count, 1)
        self.assertEqual(len(declarations), 2)
        for index, entry in enumerate(declarations):
            self.assertEqual(entry["source"], focused._declaration_source(
                self.task, index, entry["symbol"]
            ))
            self.assertEqual(entry["stdout_sha256"], hashlib.sha256(stdout).hexdigest())
            self.assertEqual((self.artifacts / entry["stdout_path"]).read_bytes(), stdout)
        source = (self.artifacts / batch["source_path"]).read_bytes()
        self.assertEqual(execute.call_args.kwargs["input"], source)
        self.assertEqual(batch["source_sha256"], hashlib.sha256(source).hexdigest())
        document = {
            "schema_version": "2.0", "status": "passed",
            "accepted_commit": "a" * 40, "accepted_tree": "b" * 40,
            "commands": [{"argv": argv, "status": "passed", "exit_code": 0}
                         for argv in self.task["acceptance"]["commands"]],
            "declarations": declarations,
        }
        _validate_gate_document(
            document, task=self.task, expected_status="passed",
            accepted_commit="a" * 40, accepted_tree="b" * 40,
            artifact_dir=self.artifacts,
        )
        self.assertEqual(self.timings[0]["phase"], "declaration_batch")
        self.assertEqual(self.timings[0]["status"], "passed")
        self.assertGreaterEqual(self.timings[0]["elapsed_seconds"], 0)

    def test_zero_exit_missing_secondary_type_marker_fails_closed(self):
        second = self.task["acceptance"]["required_declarations"][1]
        stdout = success_output(self.task).replace(f"FROZEN_CONTRACT_OK: {second}\n".encode(), b"")
        with patch.object(focused.subprocess, "run", return_value=subprocess.CompletedProcess(
            ["lean"], 0, stdout, b""
        )):
            with self.assertRaisesRegex(focused.FocusedReviewError, second):
                self.run_batch()
        self.assertEqual((self.review / "declaration-probes/batch.stdout").read_bytes(), stdout)
        timing = json.loads(next((self.review / "timings").glob("*.json")).read_bytes())
        self.assertEqual(timing["status"], "failed")

    def test_nonzero_exit_even_with_all_success_markers_rejects(self):
        with patch.object(focused.subprocess, "run", return_value=subprocess.CompletedProcess(
            ["lean"], 1, success_output(self.task), b"secondary type mismatch\n"
        )):
            with self.assertRaisesRegex(focused.FocusedReviewError, "exit 1"):
                self.run_batch()
        self.assertEqual(self.timings[0]["exit_code"], 1)
        self.assertEqual(self.timings[0]["status"], "failed")
        self.assertEqual((self.review / "declaration-probes/batch.stderr").read_bytes(),
                         b"secondary type mismatch\n")

    def test_timeout_preserves_partial_output_and_timing(self):
        with patch.object(focused.subprocess, "run", side_effect=subprocess.TimeoutExpired(
            ["lean"], 30, output=b"partial\n", stderr=b"diagnostic\n"
        )):
            with self.assertRaisesRegex(focused.FocusedReviewError, "exit 124"):
                self.run_batch()
        self.assertEqual((self.review / "declaration-probes/batch.stdout").read_bytes(), b"partial\n")
        self.assertEqual(self.timings[0]["exit_code"], 124)
        self.assertEqual(self.timings[0]["status"], "failed")

    def test_legacy_canonical_source_is_preserved_with_one_named_axiom_batch(self):
        self.task["schema_version"] = "2.0"
        self.task["objective"]["frozen_lean_type"] = "∀ (n : Nat), Nat.succ n ≠ 0"
        source = focused._batched_declaration_source(
            self.task, self.task["acceptance"]["required_declarations"]
        )
        self.assertEqual(source.splitlines().count("import Poincare"), 1)
        self.assertIn("#check (Nat.succ_ne_zero : ∀ (n : Nat), Nat.succ n ≠ 0)", source)
        self.assertIn("#check Nat.zero_ne_one", source)
        for name in self.task["acceptance"]["required_declarations"]:
            self.assertIn(f"AXIOM_CONTRACT_OK: {name}", source)
        with patch.object(focused.subprocess, "run", return_value=subprocess.CompletedProcess(
            ["lean"], 0, success_output(self.task), b""
        )):
            entries, _ = self.run_batch()
        self.assertEqual(entries[1]["source"], "import Poincare\n#check Nat.zero_ne_one\n")

    def test_empty_batch_and_non_utf8_output_reject(self):
        with self.assertRaisesRegex(focused.FocusedReviewError, "must not be empty"):
            focused._batched_declaration_source(self.task, [])
        with patch.object(focused.subprocess, "run", return_value=subprocess.CompletedProcess(
            ["lean"], 0, b"\xff", b""
        )):
            with self.assertRaisesRegex(focused.FocusedReviewError, "not UTF-8"):
                self.run_batch()

    def test_evidence_cannot_be_overwritten_by_a_retry(self):
        with patch.object(focused.subprocess, "run", return_value=subprocess.CompletedProcess(
            ["lean"], 0, success_output(self.task), b""
        )) as execute:
            self.run_batch()
            with self.assertRaises(FileExistsError):
                self.run_batch()
        self.assertEqual(execute.call_count, 1)


class FocusedReviewTimingTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.worktrees = self.root / "worktrees"
        self.worktree = self.worktrees / "job"
        self.worktree.mkdir(parents=True)
        self.artifacts = self.root / "artifacts"
        self.artifacts.mkdir()
        self.task, _ = strict_task()
        self.task["base_commit"] = "a" * 40
        self.task["acceptance"]["commands"] = [
            [*focused.LEAN_COMMAND_PREFIX, "Poincare/Example.lean"],
            ["git", "diff", "--check"],
        ]
        self.cache = self.root / "cache" / self.task["base_commit"]
        for relative in ("build/lib/lean/Poincare", "config", "packages"):
            (self.cache / relative).mkdir(parents=True, exist_ok=True)
        (self.cache / "build/lib/lean/Poincare/Example.olean").write_bytes(b"base")
        overrides = json.dumps({"packages": [
            {"name": "mathlib", "dir": "/work/.lake/packages/mathlib"}
        ]}).encode()
        (self.cache / ".harness-package-overrides.json").write_bytes(overrides)
        (self.cache / ".harness-cache.json").write_text(json.dumps({
            "schema_version": "poincare-lake-cache-v1",
            "base_commit": self.task["base_commit"], "base_tree": "d" * 40,
            "package_overrides_sha256": hashlib.sha256(overrides).hexdigest(),
        }))
        self.toolchain = self.root / "toolchain"
        (self.toolchain / "bin").mkdir(parents=True)
        for name in ("lake", "lean"):
            (self.toolchain / "bin" / name).touch()
        self.environment = {
            "POINCARE_STATE_DIR": str(self.root / "state"),
            "POINCARE_REPO_ROOT": str(self.root / "integration"),
            "POINCARE_WORKTREE_ROOT": str(self.worktrees),
            "POINCARE_PI_LAKE_CACHE_ROOT": str(self.root / "cache"),
            "POINCARE_PI_TOOLCHAIN_ROOT": str(self.toolchain),
            "HARNESS_PI_GIT": "/pinned/git",
        }
        self.store = Mock()
        self.store.get_job.return_value = {
            "job": {"state": "reviewing", "task_id": "strict-task", "task_revision": 1,
                    "workspace": {"worktree": str(self.worktree)}},
            "runtime": {"artifact_directory": str(self.artifacts), "scopes": [{"owner": "worker"}]},
        }
        self.store.get_task.return_value = {"task": self.task}

    def git_result(self, git, worktree, *arguments):
        if arguments[0] == "status":
            return ""
        if arguments[0] == "diff":
            return "Poincare/Example.lean"
        if arguments[-1] == "HEAD^{commit}":
            return "b" * 40
        if arguments[-1] == "HEAD^{tree}":
            return "c" * 40
        return "d" * 40

    def process_result(self, argv, **kwargs):
        if argv[-1] == "LEAN_PATH":
            return subprocess.CompletedProcess(argv, 0, "<cache-path>\n", "")
        if argv[-1] == "--stdin":
            return subprocess.CompletedProcess(argv, 0, success_output(self.task), b"")
        return subprocess.CompletedProcess(argv, 0, b"", b"")

    def command_result(self, argv, **kwargs):
        if "-o" in argv:
            Path(argv[argv.index("-o") + 1]).write_bytes(b"verified overlay")
        return 0, b"compiled\n", b""

    def run_review(self, execute=None):
        with patch.dict(os.environ, self.environment), \
             patch.object(focused, "HarnessStore", return_value=self.store), \
             patch.object(focused, "_git", side_effect=self.git_result), \
             patch.object(focused.subprocess, "run", side_effect=self.process_result), \
             patch.object(focused, "_run", side_effect=execute or self.command_result):
            return focused.run_focused_review("job", "codex-reviewer", 30)

    def test_complete_review_records_all_phase_timings_without_changing_gate_schema(self):
        result = self.run_review()
        manifest = json.loads((self.artifacts / result["review_manifest"]).read_bytes())
        self.assertEqual(result["phase_timings"], manifest["phase_timings"])
        self.assertEqual([entry["phase"] for entry in manifest["phase_timings"]], [
            "cache_setup", "module_compile", "acceptance_command", "root_overlay", "declaration_batch"
        ])
        self.assertGreaterEqual(manifest["commands"][0]["elapsed_seconds"], 0)
        self.assertGreaterEqual(manifest["root_overlay"]["elapsed_seconds"], 0)
        document = json.loads((self.artifacts / result["gate_result"]).read_bytes())
        _validate_gate_document(
            document, task=self.task, expected_status="passed",
            accepted_commit="b" * 40, accepted_tree="c" * 40, artifact_dir=self.artifacts,
        )
        self.assertFalse(os.path.lexists(self.worktree / ".lake"))

    def test_failed_module_compilation_retains_phase_and_compiler_evidence(self):
        with self.assertRaisesRegex(focused.FocusedReviewError, "command 0 failed"):
            self.run_review(lambda *args, **kwargs: (1, b"partial compiler output", b"failed module"))
        review = next(self.artifacts.iterdir())
        timings = [json.loads(path.read_bytes()) for path in sorted((review / "timings").glob("*.json"))]
        self.assertEqual([entry["phase"] for entry in timings], ["cache_setup", "module_compile"])
        self.assertEqual(timings[-1]["status"], "failed")
        self.assertEqual((review / "acceptance-commands/0.stderr").read_bytes(), b"failed module")
        self.assertFalse((review / "gate.json").exists())
        self.assertFalse(os.path.lexists(self.worktree / ".lake"))

    def test_failed_phase_has_append_only_timing_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            review = Path(temporary)
            timings = []
            with self.assertRaisesRegex(RuntimeError, "resisting check"):
                with focused._timed_phase(review, "module_compile", timings, target="Target.lean"):
                    raise RuntimeError("resisting check")
            self.assertEqual(timings[0]["status"], "failed")
            self.assertEqual(json.loads((review / "timings/000-module_compile.json").read_bytes()),
                             timings[0])
            self.assertEqual((review / "timings/000-module_compile.json").stat().st_mode & 0o777, 0o400)


@unittest.skipUnless(shutil.which("lean"), "Lean executable is required for batched contract probes")
class ExecutableBatchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temporary.name)
        cls.lean = Path(shutil.which("lean"))
        cls.environment = {**os.environ, "LEAN_PATH": str(cls.root), "LEAN_NUM_THREADS": "1"}
        (cls.root / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
        (cls.root / "Poincare.lean").write_text(
            "import Lean\naxiom Fixture.forbidden : True\n"
            "unsafe def Fixture.unsafe : True := True.intro\n", encoding="utf-8"
        )
        result = subprocess.run(
            [str(cls.lean), "Poincare.lean", "-o", "Poincare.olean"],
            cwd=cls.root, env=cls.environment, capture_output=True, timeout=60,
        )
        if result.returncode != 0:
            cls.temporary.cleanup()
            raise RuntimeError(result.stdout.decode() + result.stderr.decode())
        (cls.root / "Poincare").mkdir()
        for name, source in {
            "Example": "import Poincare\ntheorem ExampleTarget : True := by trivial\n"
                       "private theorem hiddenTarget : True := by trivial\n",
            "Invalid": "import Poincare\ntheorem GoodTarget : True := by trivial\n"
                       "private theorem hiddenTarget : True := Fixture.forbidden\n",
        }.items():
            (cls.root / "Poincare" / f"{name}.lean").write_text(source)
            result = subprocess.run(
                [str(cls.lean), f"Poincare/{name}.lean", "-o", f"Poincare/{name}.olean"],
                cwd=cls.root, env=cls.environment, capture_output=True, timeout=60,
            )
            if result.returncode != 0:
                cls.temporary.cleanup()
                raise RuntimeError(result.stdout.decode() + result.stderr.decode())

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def setUp(self):
        self.task, _ = strict_task()
        self.review = Path(tempfile.mkdtemp(dir=self.root))

    def run_batch(self):
        return focused._run_declaration_batch(
            self.task, lean=self.lean, cwd=self.root, environment=self.environment,
            timeout_seconds=60, review_dir=self.review, timings=[],
        )

    def assert_rejected(self, expected: str):
        with self.assertRaisesRegex(focused.FocusedReviewError, "exit 1"):
            self.run_batch()
        output = (self.review / "declaration-probes/batch.stdout").read_text()
        self.assertIn(expected, output)

    def test_all_symbols_pass_in_one_executable_batch(self):
        declarations, _ = self.run_batch()
        self.assertEqual(len(declarations), 2)

    def test_wrong_secondary_frozen_type_rejects(self):
        self.task["statement_contract"]["declarations"][1]["lean_type"] = "(0 : Nat) ≠ 2"
        self.assert_rejected("frozen type mismatch")

    def test_missing_secondary_symbol_rejects(self):
        self.task["statement_contract"]["declarations"][1]["name"] = "Fixture.missing"
        self.task["acceptance"]["required_declarations"][1] = "Fixture.missing"
        self.assert_rejected("Unknown constant")

    def test_secondary_forbidden_axiom_rejects(self):
        self.task["statement_contract"]["declarations"][1] = {
            "name": "Fixture.forbidden", "lean_type": "True"
        }
        self.task["acceptance"]["required_declarations"][1] = "Fixture.forbidden"
        self.assert_rejected("forbidden axiom")

    def test_secondary_unsafe_definition_rejects(self):
        self.task["statement_contract"]["declarations"][1] = {
            "name": "Fixture.unsafe", "lean_type": "True"
        }
        self.task["acceptance"]["required_declarations"][1] = "Fixture.unsafe"
        self.assert_rejected("unsafe or partial declaration")

    def run_legacy_gate(self, module, symbol):
        executable = self.review / "bin"
        executable.mkdir()
        (executable / "git").write_text("#!/bin/sh\nexit 0\n")
        (executable / "lake").write_text(
            "#!/bin/sh\n"
            'if [ "$1" = build ]; then exit 0; fi\n'
            'exec "$GATE_LEAN_EXECUTABLE" "$3"\n'
        )
        for entry in executable.iterdir():
            entry.chmod(0o700)
        return subprocess.run(
            ["bash", str(ROOT / "harness/gate.sh"), str(self.root), module, symbol],
            env={**self.environment, "PATH": f"{executable}:/usr/bin:/bin",
                 "GATE_LEAN_EXECUTABLE": str(self.lean)},
            capture_output=True, text=True, timeout=60,
        )

    def test_real_legacy_batch_scans_private_declarations_and_named_target(self):
        result = self.run_legacy_gate("Poincare.Example", "ExampleTarget")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("GATE_SCAN declarations=2 nonstandard=[]", result.stdout)
        self.assertIn("GATE_NAMED_OK ExampleTarget", result.stdout)

    def test_real_legacy_batch_rejects_private_forbidden_dependency(self):
        result = self.run_legacy_gate("Poincare.Invalid", "GoodTarget")
        self.assertEqual(result.returncode, 5, result.stdout + result.stderr)
        self.assertIn("Fixture.forbidden", result.stdout)

    def test_real_legacy_batch_rejects_missing_named_symbol(self):
        result = self.run_legacy_gate("Poincare.Example", "NoSuchTarget")
        self.assertEqual(result.returncode, 5, result.stdout + result.stderr)
        self.assertIn("NoSuchTarget", result.stdout)


class LegacyGateBatchTests(unittest.TestCase):
    def run_gate(self, *, scan_exit=0, named=True, missing_marker=False, missing_file=False):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            executable = root / "bin"
            executable.mkdir()
            target = root / "Poincare/Example.lean"
            target.parent.mkdir()
            if not missing_file:
                target.write_text("theorem ExampleTarget : True := True.intro\n")
            log = root / "calls"
            source = root / "scan.lean"
            (executable / "git").write_text("#!/bin/sh\nexit 0\n")
            (executable / "lake").write_text(
                "#!/bin/sh\n"
                'printf "%s\\n" "$*" >> "$GATE_TEST_LOG"\n'
                'if [ "$1" = build ]; then exit 0; fi\n'
                'cp "$3" "$GATE_TEST_SOURCE"\n'
                'printf "%s\\n" "GATE_SCAN declarations=2 nonstandard=[]"\n'
                + ("" if missing_marker else 'printf "%s\\n" "GATE_NAMED_OK ExampleTarget"\n')
                + f"exit {scan_exit}\n"
            )
            for path in executable.iterdir():
                path.chmod(0o700)
            result = subprocess.run(
                ["bash", str(ROOT / "harness/gate.sh"), str(root), "Poincare.Example"]
                + (["ExampleTarget"] if named else []),
                env={**os.environ, "PATH": f"{executable}:/usr/bin:/bin",
                     "GATE_TEST_LOG": str(log), "GATE_TEST_SOURCE": str(source)},
                capture_output=True, text=True, timeout=30,
            )
            return result, log.read_text() if log.exists() else "", source.read_text() if source.exists() else ""

    def test_module_and_named_checks_use_one_lean_process_and_include_internal(self):
        result, calls, source = self.run_gate()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(sum(line.startswith("env lean ") for line in calls.splitlines()), 1)
        self.assertEqual(source.splitlines().count("import Poincare.Example"), 1)
        self.assertNotIn("!n.isInternal", source)
        self.assertIn("#print axioms ExampleTarget", source)
        self.assertIn("nonstandard named axiom", source)

    def test_success_marker_cannot_hide_nonzero_lean_exit(self):
        result, _, _ = self.run_gate(scan_exit=1)
        self.assertEqual(result.returncode, 5)
        self.assertIn("REJECT", result.stdout)

    def test_missing_named_success_marker_and_missing_module_fail_closed(self):
        result, _, _ = self.run_gate(missing_marker=True)
        self.assertEqual(result.returncode, 5)
        result, calls, _ = self.run_gate(missing_file=True)
        self.assertEqual(result.returncode, 3)
        self.assertEqual(calls, "")


if __name__ == "__main__":
    unittest.main()
