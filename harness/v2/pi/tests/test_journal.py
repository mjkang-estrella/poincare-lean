from __future__ import annotations

import hashlib
import json
import os
import stat
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from harness.v2.pi.journal import (
    BLOB_DIRECTORY,
    JOURNAL_NAME,
    LOCK_NAME,
    SEAL_NAME,
    CommittedPatch,
    PatchIntent,
    PatchJournal,
    PatchJournalError,
    ReplayObservation,
    replay_committed_patches,
    verify_patch_journal,
)
from harness.v2.pi.quota import SharedArtifactQuota


JOB = "automatic-scalar-derivative-constructor-a01"
SESSION = "session-00000001"
PATH_A = "Poincare/Global/A.lean"
PATH_B = "Poincare/Global/B.lean"
PATCH_A = b"diff --git a/Poincare/Global/A.lean b/Poincare/Global/A.lean\n"
PATCH_B = b"diff --git a/Poincare/Global/B.lean b/Poincare/Global/B.lean\n"


def _digest(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _hashes(paths: tuple[str, ...], prefix: str) -> dict[str, str]:
    return {path: _digest(f"{prefix}:{path}") for path in paths}


class _RecordingQuota:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.delegate = SharedArtifactQuota(root, 4 * 1024 * 1024)
        self.operations: list[tuple[str, str]] = []

    def append(self, relative: str, data: bytes) -> object:
        self.operations.append(("append", relative))
        return self.delegate.append(relative, data)

    def write_once(
        self,
        relative: str,
        data: bytes,
        *,
        emergency: bool = False,
        mode: int = 0o600,
        allow_identical_existing: bool = False,
    ) -> object:
        self.operations.append(("write_once", relative))
        return self.delegate.write_once(
            relative,
            data,
            emergency=emergency,
            mode=mode,
            allow_identical_existing=allow_identical_existing,
        )


class PatchJournalHappyPathTest(unittest.TestCase):
    def test_commit_abort_seal_verify_and_replay_in_order(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            quota = _RecordingQuota(root)
            journal = PatchJournal.create(root, JOB, SESSION, quota=quota)

            first = journal.record_intent("call-1", (PATH_A,), PATCH_A)
            before_a = _hashes(first.paths, "before-a")
            after_a = _hashes(first.paths, "after-a")
            journal.commit(first, before_a, after_a)

            aborted = journal.record_intent("call-2", (PATH_B,), PATCH_B)
            journal.abort(aborted)

            third = journal.record_intent("call-3", (PATH_A, PATH_B), PATCH_A + PATCH_B)
            before_both = _hashes(third.paths, "before-both")
            after_both = _hashes(third.paths, "after-both")
            journal.commit(third, before_both, after_both)
            journal.close()
            journal.dispose()

            committed = verify_patch_journal(root, JOB, SESSION)
            self.assertEqual([item.tool_call_id for item in committed], ["call-1", "call-3"])
            self.assertEqual(
                [(item.intent_sequence, item.commit_sequence) for item in committed],
                [(1, 2), (5, 6)],
            )
            self.assertEqual(committed[0].patch, PATCH_A)
            self.assertEqual(committed[1].patch, PATCH_A + PATCH_B)

            observed: list[str] = []

            def apply(record: CommittedPatch) -> ReplayObservation:
                observed.append(record.tool_call_id)
                return ReplayObservation(record.before_sha256, record.after_sha256)

            self.assertEqual(replay_committed_patches(committed, apply), committed)
            self.assertEqual(observed, ["call-1", "call-3"])
            self.assertIn(("write_once", JOURNAL_NAME), quota.operations)
            self.assertIn(("write_once", SEAL_NAME), quota.operations)
            self.assertEqual(
                sum(operation == "append" for operation, _path in quota.operations),
                6,
            )

            journal_lines = (root / JOURNAL_NAME).read_bytes().splitlines()
            self.assertEqual(len(journal_lines), 6)
            for sequence, line in enumerate(journal_lines, start=1):
                entry = json.loads(line)
                self.assertEqual(entry["sequence"], sequence)
                self.assertEqual(entry["job_id"], JOB)
                self.assertEqual(entry["session_id"], SESSION)
                self.assertIn("entry_sha256", entry)
                if entry["state"] == "commit":
                    self.assertIn("before_sha256", entry)
                    self.assertIn("after_sha256", entry)
                else:
                    self.assertNotIn("before_sha256", entry)
                    self.assertNotIn("after_sha256", entry)
            self.assertEqual(stat.S_IMODE((root / JOURNAL_NAME).stat().st_mode), 0o400)
            for blob in (root / BLOB_DIRECTORY).iterdir():
                self.assertEqual(stat.S_IMODE(blob.stat().st_mode), 0o400)

    def test_empty_journal_can_be_closed_and_verified(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            journal = PatchJournal.create(root, JOB, SESSION)
            journal.close()
            journal.dispose()
            self.assertEqual(verify_patch_journal(root, JOB, SESSION), ())

    def test_reopen_resolves_an_incomplete_intent(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            journal = PatchJournal.create(root, JOB, SESSION)
            intent = journal.record_intent("call-recover", (PATH_A,), PATCH_A)
            journal.dispose()

            recovered = PatchJournal.open_existing(root, JOB, SESSION)
            recovered.abort(intent)
            recovered.close()
            recovered.dispose()
            self.assertEqual(verify_patch_journal(root, JOB, SESSION), ())


class PatchJournalStateMachineTest(unittest.TestCase):
    def test_intent_must_be_resolved_exactly_once_and_serially(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            journal = PatchJournal.create(root, JOB, SESSION)
            intent = journal.record_intent("call-1", (PATH_A,), PATCH_A)
            with self.assertRaisesRegex(PatchJournalError, "prior patch intent"):
                journal.record_intent("call-2", (PATH_B,), PATCH_B)
            with self.assertRaisesRegex(PatchJournalError, "unresolved patch intent"):
                journal.close()

            forged = replace(intent, patch_sha256=_digest("forged"))
            with self.assertRaisesRegex(PatchJournalError, "does not match"):
                journal.abort(forged)
            journal.abort(intent)
            with self.assertRaisesRegex(PatchJournalError, "does not match"):
                journal.abort(intent)
            with self.assertRaisesRegex(PatchJournalError, "already has an intent"):
                journal.record_intent("call-1", (PATH_A,), PATCH_A)
            journal.close()
            with self.assertRaisesRegex(PatchJournalError, "closed"):
                journal.record_intent("call-3", (PATH_A,), PATCH_A)
            journal.dispose()
            with self.assertRaisesRegex(PatchJournalError, "already closed"):
                PatchJournal.open_existing(root, JOB, SESSION)

    def test_commit_requires_exact_path_hash_maps(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            journal = PatchJournal.create(root, JOB, SESSION)
            intent = journal.record_intent("call-1", (PATH_A, PATH_B), PATCH_A + PATCH_B)
            good_before = _hashes(intent.paths, "before")
            good_after = _hashes(intent.paths, "after")
            with self.assertRaisesRegex(PatchJournalError, "exactly"):
                journal.commit(intent, {PATH_A: good_before[PATH_A]}, good_after)
            with self.assertRaisesRegex(PatchJournalError, "lowercase SHA"):
                journal.commit(intent, good_before, {**good_after, PATH_B: "F" * 64})
            journal.commit(intent, good_before, good_after)
            journal.close()
            journal.dispose()

    def test_invalid_inputs_are_rejected_before_writing(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            journal = PatchJournal.create(root, JOB, SESSION)
            invalid = (
                ("", (PATH_A,), PATCH_A),
                ("call", ("../escape",), PATCH_A),
                ("call", (PATH_A, PATH_A), PATCH_A),
                ("call", (PATH_A,), b""),
            )
            for tool_call_id, paths, patch in invalid:
                with self.subTest(tool_call_id=tool_call_id, paths=paths, patch=patch):
                    with self.assertRaises(PatchJournalError):
                        journal.record_intent(tool_call_id, paths, patch)
            journal.close()
            journal.dispose()
            self.assertEqual(verify_patch_journal(root, JOB, SESSION), ())

    def test_create_is_exclusive_and_artifact_root_cannot_be_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            parent = Path(raw)
            root = parent / "artifacts"
            root.mkdir()
            journal = PatchJournal.create(root, JOB, SESSION)
            with self.assertRaises(PatchJournalError):
                PatchJournal.create(root, JOB, SESSION)
            journal.dispose()

            linked = parent / "linked"
            linked.symlink_to(root, target_is_directory=True)
            with self.assertRaisesRegex(PatchJournalError, "real directory"):
                PatchJournal.open_existing(linked, JOB, SESSION)


class PatchJournalTamperTest(unittest.TestCase):
    def _closed_one_patch(self, root: Path) -> tuple[CommittedPatch, Path]:
        journal = PatchJournal.create(root, JOB, SESSION)
        intent = journal.record_intent("call-1", (PATH_A,), PATCH_A)
        journal.commit(intent, _hashes(intent.paths, "before"), _hashes(intent.paths, "after"))
        journal.close()
        journal.dispose()
        committed = verify_patch_journal(root, JOB, SESSION)[0]
        blob = next((root / BLOB_DIRECTORY).iterdir())
        return committed, blob

    def test_journal_tamper_and_complete_line_truncation_fail_seal(self) -> None:
        for mutation in ("tamper", "truncate"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                self._closed_one_patch(root)
                journal_path = root / JOURNAL_NAME
                journal_path.chmod(0o600)
                data = journal_path.read_bytes()
                if mutation == "tamper":
                    data = data.replace(b'"state":"commit"', b'"state":"abort"', 1)
                else:
                    data = data.splitlines(keepends=True)[0]
                journal_path.write_bytes(data)
                with self.assertRaises(PatchJournalError):
                    verify_patch_journal(root, JOB, SESSION)

    def test_noncanonical_unknown_key_sequence_gap_and_partial_line_fail(self) -> None:
        mutations = {
            "noncanonical": lambda line: b" " + line,
            "unknown": lambda line: line[:-2] + b',"unknown":true}\n',
            "gap": lambda line: line.replace(b'"sequence":1', b'"sequence":2', 1),
            "partial": lambda line: line[:-1],
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                journal = PatchJournal.create(root, JOB, SESSION)
                journal.record_intent("call-1", (PATH_A,), PATCH_A)
                journal.dispose()
                path = root / JOURNAL_NAME
                path.write_bytes(mutate(path.read_bytes()))
                with self.assertRaises(PatchJournalError):
                    verify_patch_journal(root, JOB, SESSION, require_closed=False)

    def test_blob_tamper_unexpected_blob_symlink_hardlink_and_fifo_fail(self) -> None:
        mutations = ("tamper", "writable", "unexpected", "symlink", "hardlink", "fifo")
        for mutation in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                _committed, blob = self._closed_one_patch(root)
                blob_directory = root / BLOB_DIRECTORY
                if mutation == "tamper":
                    blob.chmod(0o600)
                    blob.write_bytes(blob.read_bytes() + b"tamper")
                elif mutation == "writable":
                    blob.chmod(0o600)
                elif mutation == "unexpected":
                    (blob_directory / "unexpected.patch").write_bytes(b"x")
                elif mutation == "symlink":
                    (blob_directory / "unexpected.patch").symlink_to(blob)
                elif mutation == "hardlink":
                    os.link(blob, root / "external-hardlink")
                else:
                    os.mkfifo(blob_directory / "unexpected.pipe")
                with self.assertRaises(PatchJournalError):
                    verify_patch_journal(root, JOB, SESSION)

    def test_journal_lock_and_seal_hardlinks_fail(self) -> None:
        for name in (JOURNAL_NAME, LOCK_NAME, SEAL_NAME):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                self._closed_one_patch(root)
                os.link(root / name, root / f"outside-{name}")
                with self.assertRaises(PatchJournalError):
                    verify_patch_journal(root, JOB, SESSION)

    def test_symlink_or_special_journal_files_fail(self) -> None:
        replacements = ("symlink", "fifo")
        for replacement in replacements:
            with self.subTest(replacement=replacement), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                target = root / "target"
                target.write_bytes(b"")
                (root / BLOB_DIRECTORY).mkdir()
                lock = root / LOCK_NAME
                lock.write_bytes(b"")
                journal_path = root / JOURNAL_NAME
                if replacement == "symlink":
                    journal_path.symlink_to(target)
                else:
                    os.mkfifo(journal_path)
                with self.assertRaises(PatchJournalError):
                    verify_patch_journal(root, JOB, SESSION, require_closed=False)


class PatchJournalReplayTest(unittest.TestCase):
    def _record(self) -> CommittedPatch:
        paths = (PATH_A,)
        return CommittedPatch(
            intent_sequence=1,
            commit_sequence=2,
            tool_call_id="call-1",
            paths=paths,
            patch_sha256=hashlib.sha256(PATCH_A).hexdigest(),
            before_sha256=_hashes(paths, "before"),
            after_sha256=_hashes(paths, "after"),
            patch=PATCH_A,
        )

    def test_replay_rejects_hash_disagreement_bad_callback_and_patch_tamper(self) -> None:
        record = self._record()
        wrong = ReplayObservation(record.before_sha256, _hashes(record.paths, "wrong"))
        with self.assertRaisesRegex(PatchJournalError, "hashes disagree"):
            replay_committed_patches((record,), lambda _record: wrong)
        with self.assertRaisesRegex(PatchJournalError, "must return"):
            replay_committed_patches((record,), lambda _record: None)  # type: ignore[arg-type,return-value]
        with self.assertRaisesRegex(PatchJournalError, "order or identity"):
            replay_committed_patches((replace(record, patch=PATCH_B),), lambda _record: wrong)

    def test_replay_wraps_callback_failure_and_rejects_bad_order(self) -> None:
        record = self._record()

        def fail(_record: CommittedPatch) -> ReplayObservation:
            raise OSError("synthetic replay failure")

        with self.assertRaisesRegex(PatchJournalError, "callback failed"):
            replay_committed_patches((record,), fail)
        out_of_order = replace(record, intent_sequence=3, commit_sequence=9)
        with self.assertRaisesRegex(PatchJournalError, "order or identity"):
            replay_committed_patches((out_of_order,), lambda _record: ReplayObservation({}, {}))

    def test_fabricated_intent_from_another_session_cannot_resolve(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            journal = PatchJournal.create(root, JOB, SESSION)
            intent = journal.record_intent("call-1", (PATH_A,), PATCH_A)
            forged = PatchIntent(
                job_id=JOB,
                session_id="other-session",
                sequence=intent.sequence,
                tool_call_id=intent.tool_call_id,
                paths=intent.paths,
                patch_sha256=intent.patch_sha256,
            )
            with self.assertRaises(PatchJournalError):
                journal.abort(forged)
            journal.abort(intent)
            journal.close()
            journal.dispose()


if __name__ == "__main__":
    unittest.main()
