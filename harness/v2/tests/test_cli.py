from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from harness.v2.tests.test_runtime import DECLARATION_PROBE_ARGV, job_record, task_record


class CliTest(unittest.TestCase):
    def run_cli(self, state_dir: str | Path, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                "-m",
                "harness.v2.runtime",
                "--state-dir",
                str(state_dir),
                *arguments,
            ],
            check=False,
            cwd=Path(__file__).resolve().parents[3],
            text=True,
            capture_output=True,
        )

    @staticmethod
    def roots(temporary: str) -> tuple[Path, Path, Path, Path, str, str]:
        base = Path(temporary).resolve()
        integration = base / "integration"
        worktrees = base / "worktrees"
        integration.mkdir()
        worktrees.mkdir()
        subprocess.run(["git", "init", "--quiet", str(integration)], check=True)
        (integration / "README").write_text("fixture\n", encoding="utf-8")
        subprocess.run(["git", "-C", str(integration), "add", "README"], check=True)
        subprocess.run(
            [
                "git",
                "-C",
                str(integration),
                "-c",
                "user.name=Harness Test",
                "-c",
                "user.email=harness@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "fixture",
            ],
            check=True,
        )
        commit = subprocess.run(
            ["git", "-C", str(integration), "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        tree = subprocess.run(
            ["git", "-C", str(integration), "rev-parse", "HEAD^{tree}"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        state = integration / "harness" / "v2" / "state"
        return base, integration, worktrees, state, commit, tree

    def initialize(self, state: Path, integration: Path, worktrees: Path) -> dict:
        result = self.run_cli(
            state,
            "--worktree-root",
            str(worktrees),
            "--integration-root",
            str(integration),
            "init",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def test_cli_init_import_list_show_and_transition(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base, integration, worktrees, state, commit, _ = self.roots(temporary)
            initialized = self.initialize(state, integration, worktrees)
            self.assertEqual(initialized["schema_version"], 5)
            self.assertEqual(initialized["worktree_root"], str(worktrees))

            task_path = base / "cli-task.json"
            task_path.write_text(
                json.dumps(task_record("cli-task", base_commit=commit)), encoding="utf-8"
            )
            imported = self.run_cli(state, "task", "import", str(task_path))
            self.assertEqual(imported.returncode, 0, imported.stderr)
            transitioned = self.run_cli(
                state, "task", "transition", "cli-task", "ready"
            )
            self.assertEqual(transitioned.returncode, 0, transitioned.stderr)
            self.assertEqual(json.loads(transitioned.stdout)["task"]["status"], "ready")
            listed = self.run_cli(state, "task", "list", "--state", "ready")
            self.assertEqual(listed.returncode, 0, listed.stderr)
            self.assertEqual(len(json.loads(listed.stdout)), 1)
            shown = self.run_cli(state, "task", "show", "cli-task")
            self.assertEqual(shown.returncode, 0, shown.stderr)
            self.assertEqual(json.loads(shown.stdout)["task"]["id"], "cli-task")

    def test_cli_independent_review_and_task_acceptance(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base, integration, worktrees, state, commit, tree = self.roots(temporary)
            self.initialize(state, integration, worktrees)
            task = task_record("cli-review", base_commit=commit)
            task_path = base / "task.json"
            task_path.write_text(json.dumps(task), encoding="utf-8")
            self.assertEqual(
                self.run_cli(state, "task", "import", str(task_path)).returncode, 0
            )
            self.assertEqual(
                self.run_cli(
                    state, "task", "transition", "cli-review", "ready"
                ).returncode,
                0,
            )
            job = job_record("cli-review", worktrees, base_commit=commit)
            job_path = base / "job.json"
            job_path.write_text(json.dumps(job), encoding="utf-8")
            enqueued = self.run_cli(state, "job", "enqueue", str(job_path))
            self.assertEqual(enqueued.returncode, 0, enqueued.stderr)
            dispatch = self.run_cli(
                state,
                "dispatch",
                "set",
                "running",
                "--actor",
                "cli-test",
            )
            self.assertEqual(dispatch.returncode, 0, dispatch.stderr)
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(integration),
                    "worktree",
                    "add",
                    "--quiet",
                    "--detach",
                    job["workspace"]["worktree"],
                    commit,
                ],
                check=True,
            )
            claimed = self.run_cli(
                state,
                "job",
                "claim",
                "--owner",
                "worker-cli",
                "--lease-seconds",
                "300",
                "--job-id",
                job["id"],
            )
            self.assertEqual(claimed.returncode, 0, claimed.stderr)
            token = str(json.loads(claimed.stdout)["runtime"]["lease_token"])
            for job_state in ("running", "reviewing"):
                heartbeat = self.run_cli(
                    state,
                    "job",
                    "heartbeat",
                    job["id"],
                    "--owner",
                    "worker-cli",
                    "--lease-token",
                    token,
                    "--lease-seconds",
                    "300",
                    "--state",
                    job_state,
                )
                self.assertEqual(heartbeat.returncode, 0, heartbeat.stderr)
                payload = json.loads(heartbeat.stdout)

            artifact_dir = Path(payload["runtime"]["artifact_directory"])
            output_dir = artifact_dir / "declaration-probes"
            output_dir.mkdir()
            stdout = output_dir / "0.stdout"
            stderr = output_dir / "0.stderr"
            stdout_bytes = b"ExampleTarget checked\n"
            stderr_bytes = b""
            stdout.write_bytes(stdout_bytes)
            stderr.write_bytes(stderr_bytes)
            source = "import Poincare\n#check ExampleTarget\n#check (ExampleTarget : Prop)\n"
            gate = {
                "schema_version": "2.0",
                "status": "passed",
                "accepted_commit": commit,
                "accepted_tree": tree,
                "commands": [
                    {
                        "argv": command,
                        "status": "passed",
                        "exit_code": 0,
                    }
                    for command in task["acceptance"]["commands"]
                ],
                "declarations": [
                    {
                        "symbol": "ExampleTarget",
                        "source": source,
                        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                        "argv": DECLARATION_PROBE_ARGV,
                        "status": "passed",
                        "exit_code": 0,
                        "stdout_path": stdout.relative_to(artifact_dir).as_posix(),
                        "stdout_sha256": hashlib.sha256(stdout_bytes).hexdigest(),
                        "stderr_path": stderr.relative_to(artifact_dir).as_posix(),
                        "stderr_sha256": hashlib.sha256(stderr_bytes).hexdigest(),
                    }
                ],
            }
            (artifact_dir / "gate.json").write_text(
                json.dumps(gate) + "\n", encoding="utf-8"
            )
            reviewed = self.run_cli(
                state,
                "job",
                "review",
                job["id"],
                "--reviewer",
                "codex-cli",
                "--state",
                "passed",
                "--exit-reason",
                "independent review passed",
                "--gate-status",
                "passed",
                "--gate-result",
                "gate.json",
                "--accepted-commit",
                commit,
            )
            self.assertEqual(reviewed.returncode, 0, reviewed.stderr)
            reviewed_payload = json.loads(reviewed.stdout)
            self.assertEqual(reviewed_payload["job"]["gate"]["result_path"], "gate.json")
            self.assertEqual(reviewed_payload["runtime"]["reviewer_identity"], "codex-cli")

            accepted = self.run_cli(
                state,
                "task",
                "transition",
                "cli-review",
                "accepted",
                "--accepted-commit",
                commit,
                "--gate-job",
                job["id"],
            )
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            self.assertEqual(json.loads(accepted.stdout)["task"]["status"], "accepted")

            self_promote = self.run_cli(
                state,
                "job",
                "finish",
                job["id"],
                "--owner",
                "worker-cli",
                "--lease-token",
                token,
                "--state",
                "passed",
                "--exit-reason",
                "not allowed",
            )
            self.assertNotEqual(self_promote.returncode, 0)

    def test_cli_reports_expected_errors_without_traceback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary).resolve() / "state"
            result = self.run_cli(state, "task", "show", "missing-task")
            self.assertEqual(result.returncode, 2)
            self.assertIn("run init first", result.stderr)
            self.assertNotIn("Traceback", result.stderr)


if __name__ == "__main__":
    unittest.main()
