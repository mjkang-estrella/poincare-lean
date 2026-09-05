from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from harness.v2.runtime import ConflictError, HarnessError, LeaseError
from harness.v2.runtime.store import _declaration_probe_source, _validate_gate_document
from harness.v2.runtime.validation import (
    RecordValidationError,
    axiom_probe_source,
    statement_contract_probe_source,
    statement_contract_snapshot,
    validate_statement_contract,
    validate_statement_readback,
    validate_task,
)
from harness.v2.tests import test_runtime as fixture

ROOT = Path(__file__).resolve().parents[3]


def contract_fixture() -> tuple[dict, bytes]:
    contract = {
        "imports": ["Lean"],
        "declarations": [
            {"name": "Nat.succ_ne_zero", "lean_type": "∀ (n : Nat), Nat.succ n ≠ 0"},
            {"name": "Nat.zero_ne_one", "lean_type": "(0 : Nat) ≠ 1"},
        ],
        "definition_files": [{"path": "README", "sha256": hashlib.sha256(b"fixture\n").hexdigest()}],
        "author": "statement-author",
    }
    review = {
        "reviewer": "independent-reviewer", "method": "blind-readback",
        "snapshot_sha256": statement_contract_snapshot(contract),
        "report_path": "review.json", "report_sha256": "0" * 64, "verdict": "approved",
    }
    contract["review"] = review
    report = {
        "schema_version": "1.0",
        **{key: review[key] for key in ("reviewer", "method", "snapshot_sha256", "verdict")},
        "readback": [
            {"name": "Nat.succ_ne_zero", "mathematical_statement": "The successor of every natural number is nonzero."},
            {"name": "Nat.zero_ne_one", "mathematical_statement": "Zero and one are distinct natural numbers."},
        ],
        "findings": [],
    }
    raw = (json.dumps(report, ensure_ascii=False, sort_keys=True) + "\n").encode()
    review["report_sha256"] = hashlib.sha256(raw).hexdigest()
    return contract, raw


def strict_task() -> tuple[dict, bytes]:
    task = fixture.task_record("strict-task")
    task["schema_version"] = "2.1"
    del task["objective"]["frozen_lean_type"]
    contract, report = contract_fixture()
    task["statement_contract"] = contract
    task["context"]["files"] = ["README", "review.json"]
    task["acceptance"]["required_declarations"] = [entry["name"] for entry in contract["declarations"]]
    return task, report


class StatementValidationTests(unittest.TestCase):
    def test_focused_review_uses_the_same_strict_and_legacy_probe(self):
        from harness.v2.deploy.focused_review import _declaration_source

        task, _ = strict_task()
        for index, name in enumerate(task["acceptance"]["required_declarations"]):
            self.assertEqual(_declaration_source(task, index, name),
                             _declaration_probe_source(task, index, name))
        legacy = fixture.task_record("legacy-focused-task")
        self.assertEqual(_declaration_source(legacy, 0, "ExampleTarget"),
                         _declaration_probe_source(legacy, 0, "ExampleTarget"))

    def test_legacy_contract_bytes_and_first_probe_remain_unchanged(self):
        task = fixture.task_record("legacy-task")
        before = copy.deepcopy(task)
        validate_task(task)
        self.assertEqual(task, before)
        self.assertEqual(_declaration_probe_source(task, 0, "ExampleTarget"),
                         "import Poincare\n#check ExampleTarget\n#check (ExampleTarget : Prop)\n")

    def test_valid_strict_contract_and_complete_secondary_probe(self):
        task, raw = strict_task()
        validate_task(task)
        validate_statement_readback(task["statement_contract"], raw)
        probe = _declaration_probe_source(task, 1, "Nat.zero_ne_one")
        self.assertIn("(0 : Nat) ≠ 1", probe)
        self.assertIn("isDefEq actual expected", probe)
        self.assertIn("collectAxioms name", probe)

    def test_changed_secondary_deliverable_invalidates_review(self):
        task, _ = strict_task()
        task["statement_contract"]["declarations"][1]["lean_type"] = "True"
        with self.assertRaisesRegex(RecordValidationError, "every frozen statement"):
            validate_task(task)

    def test_every_required_declaration_must_have_exact_type(self):
        task, _ = strict_task()
        task["acceptance"]["required_declarations"].append("Nat.one_ne_zero")
        with self.assertRaisesRegex(RecordValidationError, "every frozen declaration"):
            validate_task(task)

    def test_missing_review_duplicate_declarations_and_self_review_rejected(self):
        for change in ("missing", "duplicate", "self", "false", "method"):
            with self.subTest(change=change):
                task, _ = strict_task()
                contract = task["statement_contract"]
                if change == "missing":
                    del contract["review"]
                elif change == "duplicate":
                    contract["declarations"].append(contract["declarations"][0])
                elif change == "self":
                    contract["review"]["reviewer"] = contract["author"]
                elif change == "false":
                    contract["review"]["verdict"] = False
                else:
                    contract["review"]["method"] = "read-intended-statement"
                with self.assertRaises(RecordValidationError):
                    validate_task(task)

    def test_definition_sources_cannot_be_worker_writable_or_omitted(self):
        task, _ = strict_task()
        task["scope"]["allowed_paths"].append("README")
        with self.assertRaisesRegex(RecordValidationError, "frozen context"):
            validate_task(task)
        task, _ = strict_task()
        task["context"]["files"] = []
        with self.assertRaisesRegex(RecordValidationError, "pinned review report"):
            validate_task(task)

    def test_tampered_and_false_readback_even_with_recomputed_hash(self):
        contract, raw = contract_fixture()
        with self.assertRaisesRegex(RecordValidationError, "report hash"):
            validate_statement_readback(contract, raw + b" ")
        for field, value in (("verdict", False), ("snapshot_sha256", "0" * 64),
                             ("reviewer", "different-reviewer"), ("readback", []),
                             ("findings", ["statement changed"])):
            with self.subTest(field=field):
                altered = json.loads(raw)
                altered[field] = value
                changed = json.dumps(altered).encode()
                contract["review"]["report_sha256"] = hashlib.sha256(changed).hexdigest()
                with self.assertRaises(RecordValidationError):
                    validate_statement_readback(contract, changed)


class StatementDispatchTests(unittest.TestCase):
    setUp = fixture.RuntimeTestCase.setUp
    create_worktree = fixture.RuntimeTestCase.create_worktree
    job_record = fixture.RuntimeTestCase.job_record

    def prepare(self, *, report_transform=None, definition_bytes=None, narrow_context=False):
        task, raw = strict_task()
        if definition_bytes is not None:
            (self.integration_root / "README").write_bytes(definition_bytes)
            contract = task["statement_contract"]
            contract["definition_files"][0]["sha256"] = hashlib.sha256(definition_bytes).hexdigest()
            contract["review"]["snapshot_sha256"] = statement_contract_snapshot(contract)
            report = json.loads(raw)
            report["snapshot_sha256"] = contract["review"]["snapshot_sha256"]
            raw = json.dumps(report).encode()
            contract["review"]["report_sha256"] = hashlib.sha256(raw).hexdigest()
        if narrow_context:
            task["context"]["files"] = ["review.json"]
        if report_transform:
            data = json.loads(raw)
            report_transform(data)
            raw = json.dumps(data).encode()
            task["statement_contract"]["review"]["report_sha256"] = hashlib.sha256(raw).hexdigest()
        (self.integration_root / "review.json").write_bytes(raw)
        subprocess.run(["git", "-C", str(self.integration_root), "add", "README", "review.json"], check=True)
        subprocess.run(["git", "-C", str(self.integration_root), "-c", "user.name=Harness Test",
                        "-c", "user.email=harness@example.invalid", "commit", "--quiet", "-m", "review"], check=True)
        self.base_commit = subprocess.check_output(["git", "-C", str(self.integration_root), "rev-parse", "HEAD"], text=True).strip()
        task["base_commit"] = self.base_commit
        self.store.import_task(task)
        self.store.transition_task(task["id"], "ready")
        job = self.job_record(task["id"])
        self.create_worktree(job)
        return task, job

    def test_reviewed_strict_task_dispatches(self):
        _, job = self.prepare()
        self.store.enqueue_job(job)
        result = self.store.claim_job(job_id=job["id"], owner="worker", lease_seconds=60)
        self.assertEqual(result["job"]["state"], "preparing")

    def test_missing_report_prevents_enqueue(self):
        _, job = self.prepare()
        (Path(job["workspace"]["worktree"]) / "review.json").unlink()
        with self.assertRaises(HarnessError):
            self.store.enqueue_job(job)

    def test_false_approved_report_prevents_enqueue_even_if_pinned(self):
        _, job = self.prepare(report_transform=lambda report: report.update(verdict=False))
        with self.assertRaisesRegex(ConflictError, "frozen review"):
            self.store.enqueue_job(job)

    def test_definition_drift_and_report_tamper_prevent_claim(self):
        _, job = self.prepare()
        self.store.enqueue_job(job)
        for path, changed in (("README", b"different definition"), ("review.json", b"{}")):
            with self.subTest(path=path):
                target = Path(job["workspace"]["worktree"]) / path
                original = target.read_bytes()
                target.write_bytes(changed)
                with self.assertRaisesRegex(LeaseError, "frozen statement context changed"):
                    self.store.claim_job(job_id=job["id"], owner="worker", lease_seconds=60)
                target.write_bytes(original)

    def test_rehashed_definition_cannot_replace_trusted_git_base(self):
        task, job = self.prepare()
        worktree = Path(job["workspace"]["worktree"])
        (worktree / "README").write_bytes(b"altered definition\n")
        contract = task["statement_contract"]
        contract["definition_files"][0]["sha256"] = hashlib.sha256(b"altered definition\n").hexdigest()
        contract["review"]["snapshot_sha256"] = statement_contract_snapshot(contract)
        with self.assertRaisesRegex(ConflictError, "not pinned at Task base"):
            self.store._validate_statement_context(task, worktree)

    def test_review_tamper_after_claim_prevents_running_transition(self):
        _, job = self.prepare()
        self.store.enqueue_job(job)
        claimed = self.store.claim_job(job_id=job["id"], owner="worker", lease_seconds=60)
        (Path(job["workspace"]["worktree"]) / "review.json").write_text("{}")
        with self.assertRaisesRegex(ConflictError, "frozen statement context changed"):
            self.store.heartbeat_job(job["id"], owner="worker", lease_token=claimed["runtime"]["lease_token"],
                                     lease_seconds=60, to_state="running")

    def test_strict_pi_and_fallback_snapshots_bind_full_contract(self):
        from harness.v2.pi.snapshot import build_snapshot, SnapshotError as PiSnapshotError
        from harness.v2.worker.snapshot import compute_prompt_snapshot, SnapshotError as WorkerSnapshotError
        task, job = self.prepare()
        worktree = Path(job["workspace"]["worktree"])
        for snapshot in (build_snapshot(task, worktree), compute_prompt_snapshot(task=task, repo_root=worktree)):
            self.assertIn("Nat.zero_ne_one", snapshot.prompt)
            self.assertIn("(0 : Nat) ≠ 1", snapshot.prompt)
            self.assertIn(task["statement_contract"]["review"]["snapshot_sha256"], snapshot.prompt)
        (worktree / "review.json").write_bytes(b"{}")
        with self.assertRaises(PiSnapshotError):
            build_snapshot(task, worktree)
        with self.assertRaises(WorkerSnapshotError):
            compute_prompt_snapshot(task=task, repo_root=worktree)

    def test_large_pinned_definition_is_verified_without_entering_worker_context(self):
        from harness.v2.pi.snapshot import build_snapshot, SnapshotError as PiSnapshotError
        from harness.v2.worker.snapshot import compute_prompt_snapshot, SnapshotError as WorkerSnapshotError
        marker = b"DEFINITION_BYTES_MUST_NOT_ENTER_PROMPT"
        large = marker + b"x" * (2 * 1024 * 1024)
        task, job = self.prepare(definition_bytes=large, narrow_context=True)
        worktree = Path(job["workspace"]["worktree"])
        self.store.enqueue_job(job)
        pi = build_snapshot(task, worktree)
        fallback = compute_prompt_snapshot(task=task, repo_root=worktree)
        for snapshot in (pi, fallback):
            self.assertNotIn(marker.decode(), snapshot.prompt)
            self.assertLess(len(snapshot.prompt), 20000)
        self.assertEqual([entry.path for entry in pi.entries], ["review.json"])
        self.assertEqual([entry.path for entry in fallback.context_entries], ["review.json"])
        # Explicitly requesting the large file as context still hits the legacy cap.
        wide_task = copy.deepcopy(task)
        wide_task["context"]["files"].append("README")
        with self.assertRaisesRegex(PiSnapshotError, "context file exceeds"):
            build_snapshot(wide_task, worktree)
        with self.assertRaisesRegex(WorkerSnapshotError, "exceeds"):
            compute_prompt_snapshot(task=wide_task, repo_root=worktree)
        (worktree / "README").write_bytes(b"tampered excluded source")
        with self.assertRaisesRegex(PiSnapshotError, "changed source"):
            build_snapshot(task, worktree)
        with self.assertRaises(WorkerSnapshotError):
            compute_prompt_snapshot(task=task, repo_root=worktree)

    def test_excluded_pinned_sources_keep_size_and_symlink_boundaries(self):
        from harness.v2.runtime.validation import validate_statement_pinned_sources
        task, job = self.prepare(narrow_context=True)
        worktree = Path(job["workspace"]["worktree"])
        source = worktree / "README"
        source.write_bytes(b"x" * (8 * 1024 * 1024 + 1))
        with self.assertRaisesRegex(RecordValidationError, "no larger than"):
            validate_statement_pinned_sources(task["statement_contract"], worktree)
        source.unlink()
        source.symlink_to(self.integration_root / "README")
        with self.assertRaisesRegex(RecordValidationError, "cannot safely read"):
            validate_statement_pinned_sources(task["statement_contract"], worktree)


class StatementGateTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.artifacts = Path(self.temporary.name)
        self.task, _ = strict_task()
        self.document = {
            "schema_version": "2.0", "status": "passed", "accepted_commit": "a" * 40,
            "accepted_tree": "b" * 40,
            "commands": [{"argv": ["git", "diff", "--check"], "exit_code": 0, "status": "passed"}],
            "declarations": [],
        }
        for index, name in enumerate(self.task["acceptance"]["required_declarations"]):
            source = _declaration_probe_source(self.task, index, name)
            stdout = f"AXIOM_CONTRACT_OK: {name}\nFROZEN_CONTRACT_OK: {name}\n".encode()
            (self.artifacts / f"{index}.stdout").write_bytes(stdout)
            (self.artifacts / f"{index}.stderr").write_bytes(b"")
            self.document["declarations"].append({
                "symbol": name, "source": source, "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "argv": fixture.DECLARATION_PROBE_ARGV, "status": "passed", "exit_code": 0,
                "stdout_path": f"{index}.stdout", "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                "stderr_path": f"{index}.stderr", "stderr_sha256": hashlib.sha256(b"").hexdigest(),
            })

    def validate(self):
        return _validate_gate_document(self.document, task=self.task, expected_status="passed",
                                       accepted_commit="a" * 40, accepted_tree="b" * 40,
                                       artifact_dir=self.artifacts)

    def test_valid_complete_probe_evidence(self):
        self.validate()

    def test_untyped_secondary_probe_cannot_satisfy_gate(self):
        second = self.document["declarations"][1]
        second["source"] = "import Lean\n#check Nat.zero_ne_one\n"
        second["source_sha256"] = hashlib.sha256(second["source"].encode()).hexdigest()
        with self.assertRaisesRegex(HarnessError, "canonical Task-bound probe"):
            self.validate()

    def test_zero_exit_without_checked_type_evidence_fails(self):
        second = self.document["declarations"][1]
        (self.artifacts / second["stdout_path"]).write_bytes(b"")
        second["stdout_sha256"] = hashlib.sha256(b"").hexdigest()
        with self.assertRaisesRegex(HarnessError, "success marker"):
            self.validate()


@unittest.skipUnless(shutil.which("lake"), "Lean toolchain is required for executable contract probes")
class ExecutableStatementTests(unittest.TestCase):
    def run_probe(self, source):
        return subprocess.run(["lake", "env", "lean", "--stdin"], input=source, text=True,
                              cwd=ROOT, capture_output=True, timeout=60)

    def test_all_declarations_compile_and_secondary_type_drift_fails(self):
        contract, _ = contract_fixture()
        good = self.run_probe(statement_contract_probe_source(contract))
        self.assertEqual(good.returncode, 0, good.stdout + good.stderr)
        contract["declarations"][1]["lean_type"] = "(0 : Nat) ≠ 2"
        bad = self.run_probe(statement_contract_probe_source(contract))
        self.assertNotEqual(bad.returncode, 0)
        self.assertIn("frozen type mismatch", bad.stdout)

    def test_coercions_cannot_disguise_changed_types(self):
        contract = {"imports": ["Lean"], "declarations": [{"name": "Nat.zero", "lean_type": "Int"}]}
        result = self.run_probe(statement_contract_probe_source(contract))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("frozen type mismatch", result.stdout)

    def test_universe_arity_and_unresolved_placeholder_are_rejected(self):
        contract = {"imports": ["Lean"], "declarations": [
            {"name": "id", "lean_type": "∀ {α : Sort u}, α → α", "universes": ["u"]}]}
        result = self.run_probe(statement_contract_probe_source(contract))
        self.assertEqual(result.returncode, 0, result.stdout)
        contract["declarations"][0] = {"name": "id", "lean_type": "Nat → Nat"}
        self.assertIn("universe arity mismatch", self.run_probe(statement_contract_probe_source(contract)).stdout)
        contract["declarations"][0] = {"name": "Nat.zero", "lean_type": "_"}
        self.assertIn("unresolved metavariables", self.run_probe(statement_contract_probe_source(contract)).stdout)

    def test_missing_declaration_and_forbidden_axiom_fail_closed(self):
        missing = self.run_probe(axiom_probe_source(["Poincare.poincare_conjecture"], ["Lean"]))
        self.assertNotEqual(missing.returncode, 0)
        self.assertNotIn("AXIOM_CONTRACT_OK:", missing.stdout)
        source = axiom_probe_source(["forbiddenFixture"], ["Lean"])
        source = source.replace("run_cmd do", "axiom forbiddenFixture : True\nrun_cmd do", 1)
        bad = self.run_probe(source)
        self.assertNotEqual(bad.returncode, 0)
        self.assertIn("forbidden axiom forbiddenFixture", bad.stdout)

    def test_unsafe_proof_typed_definition_is_not_a_checked_proof(self):
        source = axiom_probe_source(["unsafeFixture"], ["Lean"])
        source = source.replace("run_cmd do", "unsafe def unsafeFixture : True := True.intro\nrun_cmd do", 1)
        result = self.run_probe(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unsafe or partial declaration unsafeFixture", result.stdout)

    def test_unicode_declaration_names_compile(self):
        contract, _ = contract_fixture()
        contract["declarations"] = [{"name": "Fixture.identity₃", "lean_type": "Nat → Nat"}]
        contract["review"]["snapshot_sha256"] = statement_contract_snapshot(contract)
        validate_statement_contract(contract)
        source = statement_contract_probe_source(contract)
        source = source.replace("open Lean", "def Fixture.identity₃ (n : Nat) : Nat := n\nopen Lean", 1)
        result = self.run_probe(source)
        self.assertEqual(result.returncode, 0, result.stdout)


if __name__ == "__main__":
    unittest.main()
