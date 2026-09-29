"""Source-bound reuse and fresh-checkpoint publication without running Lean."""
from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import verification_receipts as receipts


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.cleanup_temporary)
        self.base = Path(self.temporary.name)
        self.root = self.base / "repo"
        self.root.mkdir()
        self.phase_dir = self.base / "phases"
        self.phase_dir.mkdir()
        self.toolchain = self.base / "tools"
        (self.toolchain / "bin").mkdir(parents=True)
        for name in ("lean", "lake"):
            path = self.toolchain / "bin" / name
            path.write_text("#!/bin/sh\nprintf 'mock compiler\\n'\n")
            path.chmod(0o755)
        environment = {"POINCARE_PI_TOOLCHAIN_ROOT": str(self.toolchain)}
        self.environment = mock.patch.dict(os.environ, environment)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.git("init", "--quiet")
        self.git("config", "user.name", "Receipt Tests")
        self.git("config", "user.email", "receipt-tests@example.invalid")
        (self.root / ".gitignore").write_text(".lake/\nharness/v2/state/\nignored/\n")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.test\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({"version": "1.1.0", "packages": []}))
        (self.root / "lakefile.lean").write_text("import Lake\n")
        (self.root / "Poincare.lean").write_text("import Poincare.Statement\n")
        (self.root / "Poincare").mkdir()
        (self.root / "Poincare/Statement.lean").write_text("def statement := True\n")
        (self.root / "scripts").mkdir()
        (self.root / "scripts/axiom_audit.sh").write_text("#!/bin/sh\nexit 0\n")
        (self.root / "CURRENT_STATUS.md").write_text("old generated status\n")
        self.commit()

    def cleanup_temporary(self):
        for directory, subdirs, filenames in os.walk(self.base):
            Path(directory).chmod(0o700)
            for name in filenames:
                (Path(directory) / name).chmod(0o600)
        self.temporary.cleanup()

    def git(self, *args, root=None):
        return subprocess.run(["git", *args], cwd=root or self.root, check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self):
        self.git("add", "--all")
        self.git("commit", "--quiet", "-m", "Pin test inputs")

    def prepare(self, completion=1):
        before_path = self.phase_dir / "source-before.json"
        receipts.atomic_json(before_path, receipts.capture_identity(self.root))
        for label, argv in receipts.PHASES:
            code = completion if label == "completion" else 0
            (self.phase_dir / f"{label}.out").write_text(f"{label} complete output\n")
            (self.phase_dir / f"{label}.status").write_text(str(code) + "\n")
            receipts.atomic_json(self.phase_dir / f"{label}.timing.json", {
                "label": label, "argv": [v.replace("{phase_dir}", str(self.phase_dir)) for v in argv],
                "exit_code": code, "duration_seconds": 0.125,
                "started_at": "2026-09-29T17:00:00Z", "finished_at": "2026-09-29T17:00:01Z"})
        status = self.phase_dir / "CURRENT_STATUS.md"
        status.write_text("# Current status\n- Generated at: 2026-09-29T17:00:00Z\n"
                          f"- Completion: {'achieved' if completion == 0 else 'not achieved'}\n")
        return before_path, status

    def publish(self, completion=1):
        before, status = self.prepare(completion)
        return receipts.publish_receipt(self.root, before, status, self.phase_dir)

    def test_unchanged_reuse_binds_head_source_and_status_date(self):
        receipt = self.publish()
        checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "fresh", checked)
        self.assertEqual(checked["verified_head"], self.git("rev-parse", "HEAD"))
        self.assertEqual(checked["verified_source_sha256"], receipt["identity"]["source_sha256"])
        self.assertEqual(checked["status_date"], "2026-09-29T17:00:00Z")
        self.assertFalse(checked["completion_certified"])
        self.assertEqual(set(receipt["phases"]), {name for name, _ in receipts.PHASES})
        evidence = self.root / receipt["evidence_directory"]
        self.assertEqual((evidence / "completion.out").read_text(), "completion complete output\n")

    def test_completion_text_never_certifies_completion_from_cache(self):
        self.publish(completion=0)
        self.assertFalse(receipts.check_receipt(self.root)["completion_certified"])
        with contextlib.redirect_stdout(io.StringIO()) as output:
            code = receipts.main(["--root", str(self.root), "read"])
        self.assertEqual(code, 0)
        self.assertIn("Completion: not certified by cached evidence", output.getvalue())

    def test_lean_import_manifest_toolchain_gate_and_status_mutations_invalidate(self):
        self.publish()
        changes = {"Poincare/Statement.lean": "def statement := False\n",
                   "Poincare.lean": "import Poincare.Changed\n",
                   "lake-manifest.json": '{"packages": [], "version": "changed"}',
                   "lean-toolchain": "leanprover/lean4:v5\n",
                   "scripts/axiom_audit.sh": "#!/bin/sh\nexit 1\n",
                   "CURRENT_STATUS.md": "- Generated at: 2026-09-29T17:00:00Z\nchanged\n"}
        for name, changed in changes.items():
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_text(changed)
                checked = receipts.check_receipt(self.root)
                self.assertEqual(checked["freshness"], "stale", checked)
                path.write_bytes(original)
                self.assertEqual(receipts.check_receipt(self.root)["freshness"], "fresh")

    def test_untracked_and_ignored_lean_inputs_invalidate(self):
        self.publish()
        for name in ("Poincare/New.lean", "ignored/Hidden.lean"):
            with self.subTest(name=name):
                path = self.root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("def hidden := True\n")
                current = receipts.capture_identity(self.root)
                self.assertIn(name, current["files"])
                self.assertFalse(current["clean"])
                self.assertEqual(receipts.check_receipt(self.root)["freshness"], "stale")
                path.unlink()

    def test_generated_evidence_and_status_outputs_do_not_change_source_identity(self):
        before = receipts.capture_identity(self.root)
        (self.root / "harness/reports").mkdir(parents=True)
        (self.root / "harness/reports/new-report.md").write_text("generated report\n")
        (self.root / "CURRENT_STATUS.md").write_text("generated status changed\n")
        (self.root / "harness/v2/state").mkdir(parents=True)
        (self.root / "harness/v2/state/receipt.json").write_text("generated receipt\n")
        self.assertTrue(receipts.same_identity(before, receipts.capture_identity(self.root)))

    def test_dirty_checkpoint_records_source_but_cannot_reuse_as_clean_head(self):
        (self.root / "Poincare.lean").write_text("import Poincare.New\n")
        receipt = self.publish()
        self.assertFalse(receipt["identity"]["clean"])
        checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "stale")
        self.assertIn("source is dirty", " ".join(checked["reasons"]))

    def test_generated_only_or_empty_commit_preserves_original_verified_head(self):
        self.publish()
        verified_head = self.git("rev-parse", "HEAD")
        self.git("commit", "--allow-empty", "--quiet", "-m", "Advance HEAD")
        checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "fresh")
        self.assertEqual(checked["verified_head"], verified_head)
        self.assertTrue(checked["head_changed_since_verification"])
        self.assertEqual(checked["current_head"], self.git("rev-parse", "HEAD"))
        self.git("add", "CURRENT_STATUS.md")
        self.git("commit", "--quiet", "-m", "Record generated status")
        self.assertEqual(receipts.check_receipt(self.root)["freshness"], "fresh")

    def test_installed_compiler_mutation_invalidates(self):
        self.publish()
        (self.toolchain / "bin/lean").write_text("#!/bin/sh\nprintf 'different compiler\\n'\n")
        self.assertEqual(receipts.check_receipt(self.root)["freshness"], "stale")

    def test_same_size_compiler_library_mutation_invalidates(self):
        library = self.toolchain / "lib/lean/Init.olean"
        library.parent.mkdir(parents=True)
        library.write_bytes(b"original")
        self.publish()
        previous_stat = library.stat()
        library.write_bytes(b"modified")
        os.utime(library, ns=(previous_stat.st_atime_ns, previous_stat.st_mtime_ns))
        checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "stale", checked)

    def test_gate_policy_mutation_invalidates(self):
        self.publish()
        with mock.patch.dict(receipts.GATE_POLICY, {"version": 99}):
            checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "stale")
        self.assertIn("gate policy", " ".join(checked["reasons"]))

    def test_capture_detects_early_file_edit_during_later_reads(self):
        original = receipts.file_identity
        edited = False
        def racing(path):
            nonlocal edited
            result = original(path)
            if path.name == "lakefile.lean" and not edited:
                edited = True
                (self.root / "Poincare.lean").write_text("import Changed\n")
            return result
        with mock.patch.object(receipts, "file_identity", side_effect=racing):
            with self.assertRaisesRegex(receipts.VerificationError, "Source changed during identity capture"):
                receipts.capture_identity(self.root)

    def test_publication_race_retains_evidence_and_does_not_issue_receipt(self):
        before, status = self.prepare()
        original = receipts.capture_identity
        calls = 0
        def racing(root):
            nonlocal calls
            calls += 1
            if calls == 2:
                (self.root / "Poincare.lean").write_text("import Changed\n")
            return original(root)
        with mock.patch.object(receipts, "capture_identity", side_effect=racing):
            with self.assertRaisesRegex(receipts.VerificationError, "Source changed during status publication"):
                receipts.publish_receipt(self.root, before, status, self.phase_dir)
        self.assertFalse((self.root / receipts.DEFAULT_RECEIPT).exists())
        evidence = next((self.root / "harness/v2/state/verification/checkpoints").iterdir())
        self.assertTrue((evidence / "rejected.json").exists())

    def test_corrupt_receipts_and_invalid_shapes_fail_closed(self):
        self.publish()
        path = self.root / receipts.DEFAULT_RECEIPT
        original = path.read_bytes()
        values = ["not json", "[]", '{"schema_version": 900}',
                  original.decode().replace('"duration_seconds": 0.125', '"duration_seconds": 5')]
        for value in values:
            with self.subTest(value=value[:20]):
                path.write_text(value)
                self.assertEqual(receipts.check_receipt(self.root)["freshness"], "stale")
        receipt = json.loads(original)
        receipt["identity"] = []
        receipt["receipt_sha256"] = receipts.digest({k: v for k, v in receipt.items() if k != "receipt_sha256"})
        path.write_text(json.dumps(receipt))
        self.assertEqual(receipts.check_receipt(self.root)["freshness"], "stale")

    def test_source_change_during_gates_rejects_and_preserves_complete_outputs(self):
        before, status = self.prepare()
        (self.root / "Poincare/Statement.lean").write_text("def changed := True\n")
        previous_status = (self.root / "CURRENT_STATUS.md").read_bytes()
        with self.assertRaisesRegex(receipts.VerificationError, "Source changed during integration gates"):
            receipts.publish_receipt(self.root, before, status, self.phase_dir)
        self.assertFalse((self.root / receipts.DEFAULT_RECEIPT).exists())
        self.assertEqual((self.root / "CURRENT_STATUS.md").read_bytes(), previous_status)
        evidence = next((self.root / "harness/v2/state/verification/checkpoints").iterdir())
        self.assertTrue((evidence / "rejected.json").is_file())
        self.assertTrue((evidence / "completion.out").is_file())

    def test_source_change_during_read_rejects(self):
        self.publish()
        capture = receipts.capture_identity
        calls = 0
        def racing(root):
            nonlocal calls
            identity = capture(root)
            calls += 1
            if calls == 1:
                (self.root / "Poincare.lean").write_text("import Changed\n")
            return identity
        with mock.patch.object(receipts, "capture_identity", side_effect=racing):
            checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "stale")
        self.assertIn("Source changed while reading", " ".join(checked["reasons"]))

    def test_archived_evidence_mutations_fail_closed(self):
        receipt = self.publish()
        evidence = self.root / receipt["evidence_directory"]
        for name in ("build.out", "build.status", "build.timing.json", "receipt.json", "status.md", "source-before.json"):
            with self.subTest(name=name):
                path = evidence / name
                original = path.read_bytes()
                self.assertEqual(path.stat().st_mode & 0o222, 0)
                path.chmod(0o600)
                path.write_bytes(original + b"changed")
                checked = receipts.check_receipt(self.root)
                self.assertEqual(checked["freshness"], "stale", checked)
                path.write_bytes(original)
                path.chmod(0o400)
                self.assertEqual(receipts.check_receipt(self.root)["freshness"], "fresh")

    def test_phase_policy_and_exit_status_disagreement_reject(self):
        before, status = self.prepare()
        (self.phase_dir / "build.status").write_text("7\n")
        with self.assertRaisesRegex(receipts.VerificationError, "disagree"):
            receipts.publish_receipt(self.root, before, status, self.phase_dir)

    def test_dependency_revision_and_dirty_source_fail_closed(self):
        package = self.root / ".lake/packages/test"
        package.mkdir(parents=True)
        self.git("init", "--quiet", root=package)
        self.git("config", "user.name", "Package Test", root=package)
        self.git("config", "user.email", "package@example.invalid", root=package)
        (package / "Dependency.lean").write_text("def dependency := True\n")
        self.git("add", "--all", root=package)
        self.git("commit", "--quiet", "-m", "Pin package", root=package)
        revision = self.git("rev-parse", "HEAD", root=package)
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [{
            "name": "test", "type": "git", "rev": revision}], "packagesDir": ".lake/packages"}))
        self.commit()
        self.publish()
        (package / "Dependency.lean").write_text("def dependency := False\n")
        checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "stale")
        self.assertIn("Dependency has dirty source", " ".join(checked["reasons"]))
        self.git("add", "--all", root=package)
        self.git("commit", "--quiet", "-m", "Change dependency", root=package)
        self.assertIn("revision differs", " ".join(receipts.check_receipt(self.root)["reasons"]))

    def test_dependency_hidden_index_flags_and_preserved_mtime_fail_closed(self):
        package = self.root / ".lake/packages/test"
        package.mkdir(parents=True)
        self.git("init", "--quiet", root=package)
        self.git("config", "user.name", "Package Test", root=package)
        self.git("config", "user.email", "package@example.invalid", root=package)
        source = package / "Dependency.lean"
        source.write_bytes(b"original")
        self.git("add", "--all", root=package)
        self.git("commit", "--quiet", "-m", "Pin package", root=package)
        revision = self.git("rev-parse", "HEAD", root=package)
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [{
            "name": "test", "type": "git", "rev": revision}], "packagesDir": ".lake/packages"}))
        self.commit()
        self.publish()
        for flag, inverse in (("--assume-unchanged", "--no-assume-unchanged"),
                              ("--skip-worktree", "--no-skip-worktree")):
            with self.subTest(flag=flag):
                self.git("update-index", flag, "Dependency.lean", root=package)
                previous_stat = source.stat()
                source.write_bytes(b"modified")
                os.utime(source, ns=(previous_stat.st_atime_ns, previous_stat.st_mtime_ns))
                checked = receipts.check_receipt(self.root)
                self.assertEqual(checked["freshness"], "stale")
                self.assertIn("index flags", " ".join(checked["reasons"]))
                source.write_bytes(b"original")
                self.git("update-index", inverse, "Dependency.lean", root=package)
                self.assertEqual(receipts.check_receipt(self.root)["freshness"], "fresh")
        # The package record also binds actual file bytes, independently of Git
        # mtime shortcuts; restoring the timestamp cannot reuse old evidence.
        previous_stat = source.stat()
        source.write_bytes(b"modified")
        os.utime(source, ns=(previous_stat.st_atime_ns, previous_stat.st_mtime_ns))
        self.assertEqual(receipts.check_receipt(self.root)["freshness"], "stale")

    def test_project_hidden_index_flags_fail_closed(self):
        self.publish()
        self.git("update-index", "--assume-unchanged", "Poincare.lean")
        (self.root / "Poincare.lean").write_text("import Changed\n")
        checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "stale")
        self.assertIn("index flags", " ".join(checked["reasons"]))

    def test_read_does_not_invoke_compiler_or_lake(self):
        self.publish()
        original = subprocess.run
        def forbid_build(argv, **kwargs):
            self.assertNotIn(Path(argv[0]).name, {"lake", "lean"})
            return original(argv, **kwargs)
        with mock.patch.object(subprocess, "run", side_effect=forbid_build):
            self.assertEqual(receipts.check_receipt(self.root)["freshness"], "fresh")

    def test_writer_runs_fresh_gates_once_and_retains_timings(self):
        shutil.copyfile(SCRIPTS / "verification_receipts.py", self.root / "scripts/verification_receipts.py")
        shutil.copyfile(SCRIPTS / "write_status_summary.sh", self.root / "scripts/write_status_summary.sh")
        invocations = self.base / "invocations.log"
        (self.toolchain / "bin/lake").write_text(
            '#!/bin/sh\n'
            'test -z "${LAKE_OVERRIDE_LEAN:-}${LAKE_OVERRIDE_LAKE:-}${LEAN_SYSROOT:-}${LEAN:-}${LEAN_PATH:-}${LEAN_SRC_PATH:-}" || exit 87\n'
            'printf "build\\n" >> "$INVOCATIONS"\nprintf "mock build\\n"\n')
        for label, argv in receipts.PHASES:
            if label == "build":
                continue
            script = self.root / argv[-1]
            content = f'#!/bin/sh\nprintf "{label}\\n" >> "$INVOCATIONS"\nprintf "{label} sentinel\\n"\n'
            if label == "completion":
                content += 'test -f "$COMPLETION_AUDIT_GATE_RESULTS_DIR/build.status" || exit 8\nprintf "COMPLETION: not achieved\\n"\nexit 1\n'
            script.write_text(content)
        self.commit()
        wrapper_bin = self.base / "ambient-wrapper"
        wrapper_bin.mkdir()
        wrapper = wrapper_bin / "lake"
        wrapper.write_text('#!/bin/sh\nprintf "wrong ambient compiler\\n" >> "$INVOCATIONS"\nexit 88\n')
        wrapper.chmod(0o755)
        env = {**os.environ, "PATH": str(wrapper_bin) + os.pathsep + os.environ["PATH"],
               "INVOCATIONS": str(invocations), "LAKE_OVERRIDE_LEAN": "true",
               "LAKE_OVERRIDE_LAKE": "true", "LEAN_SYSROOT": "/different/compiler",
               "LEAN": "/different/compiler/bin/lean", "LEAN_PATH": "/external/imports",
               "LEAN_SRC_PATH": "/external/sources"}
        result = subprocess.run(["sh", "scripts/write_status_summary.sh"], cwd=self.root,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(invocations.read_text().splitlines(), [label for label, _ in receipts.PHASES])
        checked = receipts.check_receipt(self.root)
        self.assertEqual(checked["freshness"], "fresh", checked)
        self.assertIn("## Phase Durations", (self.root / "CURRENT_STATUS.md").read_text())
        receipt = json.loads((self.root / receipts.DEFAULT_RECEIPT).read_text())
        self.assertEqual(receipt["phases"]["completion"]["exit_code"], 1)
        self.assertTrue(all(phase["duration_seconds"] >= 0 for phase in receipt["phases"].values()))


if __name__ == "__main__":
    unittest.main()
