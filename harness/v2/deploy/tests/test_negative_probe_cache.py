from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from harness.v2.deploy import negative_probe_cache as probe


EXACT_ERROR = (
    "<stdin>:11:8: error: Unknown identifier `Poincare.poincare_conjecture`\n"
    "<stdin>:12:14: error: Unknown constant `Poincare.poincare_conjecture`\n"
)
TAGGED_EXACT_ERROR = (
    "<stdin>:3:8: error(lean.unknownIdentifier): Unknown identifier `Poincare.poincare_conjecture`\n"
    "<stdin>:4:14: error(lean.unknownIdentifier): Unknown constant `Poincare.poincare_conjecture`\n"
)


class ProbeWrapperTest(unittest.TestCase):
    def test_default_and_fresh_argv_work_with_nounset_shell(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary).resolve()
            wrapper = directory / "exact-completion-probe.sh"
            wrapper.write_bytes(Path(probe.__file__).with_name(wrapper.name).read_bytes())
            python = shlex.quote(os.sys.executable)
            (directory / "common.sh").write_text(
                f"HARNESS_PI_PYTHON={python}\n"
                "load_config() {\n"
                " POINCARE_REPO_ROOT=/test/repo\n"
                " POINCARE_PI_TOOLCHAIN_ROOT=/test/toolchain\n"
                " POINCARE_CONFIG_FILE=$1\n"
                " POINCARE_CONFIG_FINGERPRINT=test-fingerprint\n"
                "}\n")
            (directory / "negative_probe_cache.py").write_text(
                "import json,os,sys\n"
                "print(json.dumps({'argv':sys.argv[1:],'override':os.environ.get('LEAN_SYSROOT')}))\n")
            cases = (([], True), (["--fresh", str(directory / "config with spaces.env")], True),
                     (["--reuse-negative", str(directory / "config with spaces.env")], False),
                     ([str(directory / "config with spaces.env")], True))
            for arguments, expected_fresh in cases:
                with self.subTest(arguments=arguments):
                    result = subprocess.run(["/bin/bash", str(wrapper), *arguments],
                                            env=dict(os.environ, LEAN_SYSROOT="/untrusted/override"),
                                            text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    recorded = json.loads(result.stdout)
                    self.assertEqual("--fresh" in recorded["argv"], expected_fresh)
                    self.assertNotIn("--reuse-negative", recorded["argv"])
                    self.assertIsNone(recorded["override"])
                    self.assertIn("--root", recorded["argv"])
                    self.assertEqual(recorded["argv"][recorded["argv"].index("--config") + 1],
                                     str(directory / "config with spaces.env") if arguments else str(directory / ".env"))


class ProbeClassificationTest(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("POINCARE_TEST_LEAN_TOOLCHAIN"),
                         "real Lean smoke requires an explicitly selected serialized toolchain")
    def test_real_manifest_syntax_if_explicitly_requested(self) -> None:
        toolchain = Path(os.environ["POINCARE_TEST_LEAN_TOOLCHAIN"]).resolve(strict=True)
        source = probe.PROBE_SOURCE.split("#check", 1)[0].replace("import Poincare", "import Lean", 1)
        env = probe._probe_environment()
        env.pop("LEAN_PATH", None)
        result = subprocess.run([str(toolchain / "bin/lean"), "--stdin"], input=source,
                                env=env, text=True, capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        prefix = "POINCARE_NEGATIVE_PROBE_IMPORTS="
        manifests = [json.loads(line[len(prefix):]) for line in result.stdout.splitlines()
                     if line.startswith(prefix)]
        self.assertEqual(len(manifests), 1)
        self.assertTrue(any(row["module"] == "Lean" for row in manifests[0]))
        self.assertTrue(all(Path(row["olean"]).is_file() for row in manifests[0]))

    def test_only_exact_reserved_errors_are_absence(self) -> None:
        self.assertEqual(probe.classify_probe(1, EXACT_ERROR), ("absent", 3))
        for output in (
            "<stdin>:3:8: error: Unknown identifier `Poincare.other_theorem`\n",
            "error: object file Poincare.olean does not exist\n",
            EXACT_ERROR + "error: unexpected token\n",
            "Unknown identifier `Poincare.poincare_conjecture`\n",
            "<stdin>:3:8: error: Unknown identifier `Poincare.poincare_conjecture_extra`\n",
        ):
            with self.subTest(output=output):
                self.assertEqual(probe.classify_probe(1, output), ("invalid", 4))
        for status in (-9, 2, 124):
            self.assertEqual(probe.classify_probe(status, EXACT_ERROR), ("invalid", 4))

    def test_actual_lean_tagged_unknown_identifier_output_is_absence(self) -> None:
        self.assertEqual(probe.classify_probe(1, TAGGED_EXACT_ERROR), ("absent", 3))
        for output in (
            TAGGED_EXACT_ERROR + "<stdin>:6:2: error(lean.parserError): unexpected token\n",
            TAGGED_EXACT_ERROR.replace("Poincare.poincare_conjecture", "Poincare.unrelated"),
            TAGGED_EXACT_ERROR + "error: object file missing\n",
            EXACT_ERROR + "error(lean.unknownIdentifier): Unknown identifier `Poincare.other`\n",
        ):
            self.assertEqual(probe.classify_probe(1, output), ("invalid", 4))

    @unittest.skipUnless(os.environ.get("POINCARE_TEST_EXACT_PROBE_ROOT") and os.environ.get("POINCARE_TEST_LEAN_TOOLCHAIN"),
                         "real exact probe requires an explicitly selected serialized project and toolchain")
    def test_real_minimal_exact_probe_classifies_compiler_result(self) -> None:
        root = Path(os.environ["POINCARE_TEST_EXACT_PROBE_ROOT"]).resolve(strict=True)
        toolchain = Path(os.environ["POINCARE_TEST_LEAN_TOOLCHAIN"]).resolve(strict=True)
        command = [str(toolchain / "bin/lake"), "env", str(toolchain / "bin/lean"), "--stdin"]
        returncode, transcript = probe._run_lean(root, command, source=probe.MINIMAL_PROBE_SOURCE)
        self.assertNotIn("POINCARE_NEGATIVE_PROBE_IMPORTS", transcript)
        expected = os.environ.get("POINCARE_TEST_EXPECT_EXACT_STATUS", "absent")
        self.assertEqual(probe.classify_probe(returncode, transcript)[0], expected, transcript)

    def test_positive_and_nonstandard_results_are_distinct(self) -> None:
        self.assertEqual(probe.classify_probe(0, "depends on axioms: [propext, Classical.choice, Quot.sound]"), ("verified", 0))
        self.assertEqual(probe.classify_probe(0, "does not depend on any axioms"), ("verified", 0))
        self.assertEqual(probe.classify_probe(0, "depends on axioms: [Poincare.something_unproved]"), ("nonstandard_axioms", 5))
        self.assertEqual(probe.classify_probe(0, "arbitrary successful output"), ("nonstandard_axioms", 5))

    def test_actual_probe_environment_removes_compiler_overrides(self) -> None:
        overrides = {"LAKE_OVERRIDE_LEAN": "true", "LAKE_OVERRIDE_LAKE": "true",
                     "LEAN_SYSROOT": "/tmp/other-toolchain", "LEAN": "/tmp/other-lean"}
        with patch.dict(os.environ, overrides):
            env = probe._probe_environment()
        self.assertEqual(env["LEAN_NUM_THREADS"], "1")
        self.assertTrue(all(name not in env for name in overrides))


class NegativeProbeCacheTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.root = self.directory / "repo"
        self.root.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Harness Test")
        self.git("config", "user.email", "harness-test@example.invalid")
        (self.root / ".gitignore").write_text(".lake/\nharness/v2/state/\n")
        self.source = self.root / "Poincare.lean"
        self.source.write_text("import Poincare.Test\n")
        self.git("add", ".")
        self.git("commit", "-qm", "Create isolated test source")
        self.toolchain = self.directory / "toolchain"
        (self.toolchain / "bin").mkdir(parents=True)
        for name in ("lean", "lake"):
            path = self.toolchain / "bin" / name
            path.write_text("#!/bin/sh\nexit 99\n")
            path.chmod(0o755)
        self.config = self.directory / "config.env"
        self.config.write_text("fixture configuration\n")
        self.config.chmod(0o600)
        self.code = self.directory / "code"
        (self.code / "scripts").mkdir(parents=True)
        self.receipts_code = self.code / "scripts/verification_receipts.py"
        self.receipts_code.write_text("# isolated identity implementation\n")
        self.code_patch = patch.object(probe, "CODE_ROOT", self.code)
        self.code_patch.start()
        self.addCleanup(self.code_patch.stop)
        self.paths = [self.root / ".lake/build/lib/lean",
                      self.root / ".lake/packages/mathlib/.lake/build/lib/lean",
                      self.toolchain / "lib/lean"]
        for path in self.paths:
            path.mkdir(parents=True)
        self.artifacts = {
            "Poincare": self.paths[0] / "Poincare.olean",
            "Poincare.Test": self.paths[0] / "Poincare/Test.olean",
            "Mathlib.Test": self.paths[1] / "Mathlib/Test.olean",
            "Init": self.paths[2] / "Init.olean",
        }
        for name, path in self.artifacts.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(("compiled " + name).encode())
        self.package_source = self.root / ".lake/packages/mathlib/Mathlib/Test.lean"
        self.package_source.parent.mkdir(parents=True)
        self.package_source.write_text("def packageValue := 1\n")
        self.calls = 0
        self.status = 1
        self.output = EXACT_ERROR
        self.on_run = None
        self.cache = self.make_cache()

    def git(self, *args: str) -> str:
        return subprocess.check_output(["git", "-C", str(self.root), *args], text=True).strip()

    def capture(self, root: Path, toolchain: Path) -> dict:
        digest = hashlib.sha256(self.source.read_bytes() + self.package_source.read_bytes()).hexdigest()
        return {"head": self.git("rev-parse", "HEAD"), "tree": self.git("rev-parse", "HEAD^{tree}"),
                "identity_sha256": digest, "clean": True}

    def manifest(self) -> list[dict]:
        return sorted([{"module": name, "olean": str(path)} for name, path in self.artifacts.items()],
                      key=lambda row: row["module"])

    def runner(self, root: Path, command: list[str]) -> tuple[int, str]:
        self.calls += 1
        self.assertEqual(command[-1], "--stdin")
        self.assertEqual(command[0], str(self.toolchain / "bin/lake"))
        if self.on_run is not None:
            self.on_run()
        output = "POINCARE_NEGATIVE_PROBE_IMPORTS=" + json.dumps(self.manifest()) + "\n" + self.output
        return self.status, output

    def make_cache(self, **kwargs) -> probe.NegativeProbeCache:
        return probe.NegativeProbeCache(self.root, self.toolchain, self.config, "test-config-fingerprint",
                                        capture=self.capture, search_paths=lambda root, toolchain: self.paths,
                                        runner=self.runner, **kwargs)

    @contextlib.contextmanager
    def stub_actual_lean_process(self):
        """Exercise the real source-selection path without starting Lean."""
        self.cache.runner = probe._run_lean
        actual_run = subprocess.run
        inputs = []

        def run(command, *args, **kwargs):
            if command != self.cache.command:
                return actual_run(command, *args, **kwargs)
            self.calls += 1
            source = kwargs["input"]
            inputs.append(source)
            output = self.output
            if source == probe.PROBE_SOURCE:
                output = "POINCARE_NEGATIVE_PROBE_IMPORTS=" + json.dumps(self.manifest()) + "\n" + output
            return subprocess.CompletedProcess(command, self.status, stdout=output)

        with patch.object(probe.subprocess, "run", side_effect=run):
            yield inputs

    def prime(self) -> probe.ProbeResult:
        result = self.cache.run()
        self.assertEqual(result.exit_code, 3)
        self.assertEqual(result.execution, "fresh")
        self.assertIsNotNone(result.evidence_path, result.cache_note)
        return result

    def test_hit_does_not_invoke_lean_and_reports_original_provenance(self) -> None:
        original = self.prime()
        result = self.cache.run()
        self.assertEqual(self.calls, 1)
        self.assertEqual(result.execution, "reused_negative")
        self.assertEqual(result.evidence_time, original.evidence_time)
        self.assertEqual(result.identity, original.identity)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            result.emit()
        lines = output.getvalue().splitlines()
        self.assertEqual(lines[0], "EXACT_DECLARATION_PROBE=absent")
        self.assertIn("Reused negative result", lines[1])
        self.assertIn(original.evidence_time, lines[1])
        self.assertIn(self.git("rev-parse", "HEAD"), lines[1])
        self.assertIn('"execution": "reused_negative"', lines[2])

    def test_fresh_always_invokes_lean_without_reading_or_updating_cache(self) -> None:
        first = self.prime()
        receipt_before = (self.cache.state / "receipt.json").read_bytes()
        with patch.object(self.cache, "identity", side_effect=AssertionError("fresh read cache identity")), \
                patch.object(self.cache, "search_paths", side_effect=AssertionError("fresh read import cache")):
            second = self.cache.run(fresh=True)
        self.assertEqual(self.calls, 2)
        self.assertEqual(second.execution, "fresh")
        self.assertIsNone(second.evidence_path)
        self.assertTrue((self.cache.state / first.evidence_path).exists())
        self.assertEqual((self.cache.state / "receipt.json").read_bytes(), receipt_before)

    def test_fresh_no_capture_callbacks_and_no_cache_receipt(self) -> None:
        with patch.object(self.cache, "capture", side_effect=AssertionError("fresh captured source")), \
                patch.object(self.cache, "search_paths", side_effect=AssertionError("fresh captured artifacts")):
            result = self.cache.run(fresh=True)
        self.assertEqual((result.exit_code, result.execution, self.calls), (3, "fresh", 1))
        self.assertIsNone(result.identity)
        self.assertFalse(self.cache.state.exists())

    def test_fresh_real_runner_uses_minimal_source_and_no_manifest_transcript(self) -> None:
        with self.stub_actual_lean_process() as inputs:
            result = self.cache.run(fresh=True)
        self.assertEqual(inputs, [probe.MINIMAL_PROBE_SOURCE])
        self.assertNotIn("POINCARE_NEGATIVE_PROBE_IMPORTS", result.transcript)
        self.assertEqual(result.probe_source_sha256, probe._sha256(probe.MINIMAL_PROBE_SOURCE.encode()))
        self.assertEqual(result.command, self.cache.command)
        output = io.StringIO()
        errors = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            result.emit()
        metadata = json.loads(output.getvalue().splitlines()[1].split("=", 1)[1])
        self.assertEqual(metadata["command"], self.cache.command)
        self.assertIsNone(metadata["original_probe_command"])
        self.assertNotIn("POINCARE_NEGATIVE_PROBE_IMPORTS", errors.getvalue())

    def test_dirty_uncachable_real_runner_falls_back_to_minimal_source(self) -> None:
        self.source.write_text("import Poincare.Test\n-- in-progress edit\n")
        with self.stub_actual_lean_process() as inputs:
            result = self.cache.run()
        self.assertEqual(inputs, [probe.MINIMAL_PROBE_SOURCE])
        self.assertNotIn("POINCARE_NEGATIVE_PROBE_IMPORTS", result.transcript)
        self.assertIsNone(result.evidence_path)

    def test_unattested_artifacts_use_minimal_source_without_manifest(self) -> None:
        with self.stub_actual_lean_process() as inputs, \
                patch.object(self.cache, "search_paths", side_effect=probe.CacheUnavailable("unattested artifacts")):
            result = self.cache.run()
        self.assertEqual(inputs, [probe.MINIMAL_PROBE_SOURCE])
        self.assertNotIn("POINCARE_NEGATIVE_PROBE_IMPORTS", result.transcript)
        self.assertIsNone(result.evidence_path)

    def test_actual_runner_only_cacheable_prime_uses_manifest_source(self) -> None:
        with self.stub_actual_lean_process() as inputs:
            result = self.prime()
        self.assertEqual(inputs, [probe.PROBE_SOURCE])
        self.assertIn("POINCARE_NEGATIVE_PROBE_IMPORTS=", result.transcript)
        self.assertEqual(result.probe_source_sha256, probe._sha256(probe.PROBE_SOURCE.encode()))

    def test_dirty_source_and_untracked_file_never_reuse_or_publish(self) -> None:
        self.prime()
        self.source.write_text("import Poincare.Test\n-- in progress\n")
        result = self.cache.run()
        self.assertEqual((result.execution, self.calls), ("fresh", 2))
        self.assertIsNone(result.evidence_path)
        self.git("checkout", "--", "Poincare.lean")
        (self.root / "unknown.lean").write_text("-- untracked work\n")
        result = self.cache.run()
        self.assertEqual((result.execution, self.calls), ("fresh", 3))
        self.assertIsNone(result.evidence_path)

    def test_clean_commit_source_change_invalidates(self) -> None:
        self.prime()
        self.source.write_text("import Poincare.Test\n-- committed change\n")
        self.git("add", "Poincare.lean")
        self.git("commit", "-qm", "Change source identity")
        result = self.cache.run()
        self.assertEqual((result.execution, self.calls), ("fresh", 2))

    def test_actual_package_source_and_artifact_changes_invalidate(self) -> None:
        self.prime()
        self.package_source.write_text("def packageValue := 2\n")
        self.assertEqual(self.cache.run().execution, "fresh")
        self.artifacts["Mathlib.Test"].write_bytes(b"recompiled package")
        self.assertEqual(self.cache.run().execution, "fresh")
        self.assertEqual(self.calls, 3)

    def test_compiler_config_and_probe_code_changes_invalidate(self) -> None:
        self.prime()
        for path in (self.toolchain / "bin/lean", self.toolchain / "bin/lake", self.config, self.receipts_code):
            with self.subTest(path=path):
                path.write_text(path.read_text() + "# changed identity\n")
                result = self.cache.run()
                self.assertEqual(result.execution, "fresh")
                self.assertIsNotNone(result.evidence_path, result.cache_note)
        self.assertEqual(self.calls, 5)

    def test_root_stdlib_optional_ir_and_new_shadow_invalidate(self) -> None:
        self.prime()
        for name in ("Poincare", "Poincare.Test", "Init"):
            self.artifacts[name].write_bytes(("changed " + name).encode())
            self.assertEqual(self.cache.run().execution, "fresh")
        companion = self.artifacts["Poincare.Test"].with_suffix(".ir")
        companion.write_bytes(b"new evaluator code")
        self.assertEqual(self.cache.run().execution, "fresh")
        companion.unlink()
        self.assertEqual(self.cache.run().execution, "fresh")
        shadow = self.paths[0] / "Mathlib/Test.olean"
        shadow.parent.mkdir()
        shadow.write_bytes(b"new higher precedence shadow")
        result = self.cache.run()
        self.assertEqual(result.execution, "fresh")
        self.assertIsNone(result.evidence_path)

    def test_positive_invalid_and_nonstandard_are_never_published(self) -> None:
        for status, output, expected in ((0, "depends on axioms: [propext]", 0),
                                          (0, "depends on axioms: [sorryAx]", 5),
                                          (1, "error: Unknown identifier `Poincare.unrelated`", 4)):
            with self.subTest(output=output):
                self.status, self.output = status, output
                for _ in range(2):
                    result = self.cache.run()
                    self.assertEqual(result.exit_code, expected)
                    self.assertEqual(result.execution, "fresh")
                self.assertFalse((self.cache.state / "receipt.json").exists())
        self.assertEqual(self.calls, 6)

    def test_positive_when_inputs_change_cannot_reuse_previous_absence(self) -> None:
        self.prime()
        self.artifacts["Poincare.Test"].write_bytes(b"new real proof")
        self.status, self.output = 0, "depends on axioms: [propext]"
        result = self.cache.run()
        self.assertEqual((result.exit_code, result.execution, self.calls), (0, "fresh", 2))
        self.assertEqual(self.cache.run().execution, "fresh")
        self.assertEqual(self.calls, 3)

    def test_receipt_with_positive_status_never_reuses_negative_evidence(self) -> None:
        self.prime()
        path = self.cache.state / "receipt.json"
        value = json.loads(path.read_text())
        value["status"] = 0
        path.chmod(0o600)
        path.write_text(json.dumps(value))
        path.chmod(0o400)
        self.assertEqual(self.cache.run().execution, "fresh")
        self.assertEqual(self.calls, 2)

    def test_absence_without_compiler_import_provenance_is_not_cached(self) -> None:
        self.cache.runner = lambda root, command: (1, EXACT_ERROR)
        result = self.cache.run()
        self.assertEqual(result.exit_code, 3)
        self.assertIsNone(result.evidence_path)
        self.assertFalse((self.cache.state / "receipt.json").exists())

    def test_artifact_changed_during_fresh_probe_is_not_cached(self) -> None:
        self.on_run = lambda: self.artifacts["Poincare.Test"].write_bytes(b"concurrent replacement")
        result = self.cache.run()
        self.assertEqual(result.exit_code, 3)
        self.assertIsNone(result.evidence_path)
        self.assertFalse((self.cache.state / "receipt.json").exists())

    def test_import_symlink_retargeted_during_fresh_probe_is_not_cached(self) -> None:
        old = self.paths[0] / "Old.olean"
        new = self.paths[0] / "New.olean"
        old.write_bytes(b"old environment imported by compiler")
        new.write_bytes(b"new completed environment not imported")
        path = self.artifacts["Poincare"]
        path.unlink()
        path.symlink_to(old)

        def retarget() -> None:
            path.unlink()
            path.symlink_to(new)

        self.on_run = retarget
        result = self.cache.run()
        self.assertEqual(result.exit_code, 3)
        self.assertIsNone(result.evidence_path)
        self.assertFalse((self.cache.state / "receipt.json").exists())
        self.on_run = None
        self.status, self.output = 0, "depends on axioms: [propext]"
        result = self.cache.run()
        self.assertEqual((result.execution, result.exit_code, self.calls), ("fresh", 0, 2))

    def test_artifact_changed_during_final_source_recheck_forces_fresh(self) -> None:
        self.prime()
        identity = self.cache.identity
        identity_calls = 0

        def raced_identity() -> dict:
            nonlocal identity_calls
            identity_calls += 1
            result = identity()
            if identity_calls == 2:
                self.artifacts["Poincare.Test"].write_bytes(b"new proof during source recheck")
                self.status, self.output = 0, "depends on axioms: [propext]"
            return result

        self.cache.identity = raced_identity
        result = self.cache.run()
        self.assertEqual((result.execution, result.exit_code, self.calls), ("fresh", 0, 2))

    def test_optional_artifact_added_during_final_source_recheck_forces_fresh(self) -> None:
        self.prime()
        identity = self.cache.identity
        identity_calls = 0

        def raced_identity() -> dict:
            nonlocal identity_calls
            identity_calls += 1
            result = identity()
            if identity_calls == 2:
                self.artifacts["Poincare.Test"].with_suffix(".ir").write_bytes(b"new imported evaluator")
            return result

        self.cache.identity = raced_identity
        result = self.cache.run()
        self.assertEqual((result.execution, self.calls), ("fresh", 2))

    def test_optional_companion_symlink_retarget_race_forces_fresh(self) -> None:
        old = self.paths[0] / "old-private.bin"
        new = self.paths[0] / "new-private.bin"
        old.write_bytes(b"original imported private declarations")
        new.write_bytes(b"different private declarations")
        companion = Path(str(self.artifacts["Poincare.Test"]) + ".private")
        companion.symlink_to(old)
        self.prime()
        identity = self.cache.identity
        identity_calls = 0

        def raced_identity() -> dict:
            nonlocal identity_calls
            identity_calls += 1
            result = identity()
            if identity_calls == 2:
                companion.unlink()
                companion.symlink_to(new)
                self.status, self.output = 0, "depends on axioms: [propext]"
            return result

        self.cache.identity = raced_identity
        result = self.cache.run()
        self.assertEqual((result.execution, result.exit_code, self.calls), ("fresh", 0, 2))

    def test_corrupt_receipt_and_tampered_transcript_fall_back_fresh(self) -> None:
        self.prime()
        receipt = self.cache.state / "receipt.json"
        receipt.chmod(0o600)
        receipt.write_text("not JSON\n")
        receipt.chmod(0o400)
        result = self.cache.run()
        self.assertEqual(result.execution, "fresh")
        transcript = self.cache.state / result.evidence_path.replace(".json", ".log")
        transcript.chmod(0o600)
        transcript.write_text("forged error: Unknown identifier `Poincare.poincare_conjecture`\n")
        transcript.chmod(0o400)
        self.assertEqual(self.cache.run().execution, "fresh")
        self.assertEqual(self.calls, 3)

    def test_writable_and_redirected_evidence_cannot_be_reused(self) -> None:
        result = self.prime()
        evidence = self.cache.state / result.evidence_path
        evidence.chmod(0o600)
        self.assertEqual(self.cache.run().execution, "fresh")
        receipt = self.cache.state / "receipt.json"
        target = self.directory / "redirected-receipt.json"
        target.write_bytes(receipt.read_bytes())
        target.chmod(0o400)
        receipt.unlink()
        receipt.symlink_to(target)
        self.assertEqual(self.cache.run().execution, "fresh")
        self.assertFalse(receipt.is_symlink())

    def test_append_only_evidence_quota_disables_publish_without_deleting(self) -> None:
        result = self.prime()
        files = set((self.cache.state / "evidence").iterdir())
        self.cache.maximum_evidence_bytes = 1
        self.artifacts["Poincare.Test"].write_bytes(b"new module forces another negative observation")
        second = self.cache.run()
        self.assertEqual(second.exit_code, 3)
        self.assertIsNone(second.evidence_path)
        self.assertEqual(files, set((self.cache.state / "evidence").iterdir()))
        self.assertTrue((self.cache.state / result.evidence_path).exists())

    def test_cache_state_must_be_ignored(self) -> None:
        (self.root / ".gitignore").write_text(".lake/\n")
        self.git("add", ".gitignore")
        self.git("commit", "-qm", "Remove ignored state")
        result = self.cache.run()
        self.assertEqual(result.exit_code, 3)
        self.assertIsNone(result.evidence_path)


if __name__ == "__main__":
    unittest.main()
