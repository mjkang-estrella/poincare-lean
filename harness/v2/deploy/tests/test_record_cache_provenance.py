from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]


def _run(
    *argv: str | Path,
    cwd: Path | None = None,
    check: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(item) for item in argv],
        cwd=cwd,
        check=check,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def _canonical_json(path: Path, value: object, mode: int = 0o400) -> bytes:
    raw = (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    path.chmod(mode)
    return raw


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


class CacheProvenanceRecorderFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="poincare-provenance-recorder-")
        self.root = Path(self.temporary.name).resolve()
        self.repo = self.root / "repo"
        self.worktrees = self.root / "worktrees"
        self.cache_root = self.root / "cache"
        self.toolchain = self.root / "toolchain"
        self.fake_bin = self.root / "bin"
        for directory in (
            self.repo,
            self.worktrees,
            self.cache_root,
            self.toolchain,
            self.fake_bin,
        ):
            directory.mkdir()

        self.lake_log = self.root / "lake.log"
        self.shadow_python_marker = self.root / "shadow-python-ran"
        self.shadow_lean_marker = self.root / "shadow-lean-ran"
        self._write_fake_tools()
        self._copy_control_surface()
        (self.repo / ".gitignore").write_text(
            ".lake/\nharness/v2/state/\n__pycache__/\n",
            encoding="utf-8",
        )
        (self.repo / "lean-toolchain").write_text(
            "leanprover/lean4:v4.30.0-rc2\n", encoding="utf-8"
        )
        (self.repo / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
        (self.repo / "Poincare.lean").write_text(
            "def rootFixture : True := True.intro\n", encoding="utf-8"
        )
        (self.repo / "Module.lean").write_text(
            "def moduleFixture : True := True.intro\n", encoding="utf-8"
        )
        for directory in (
            self.repo / ".lake/packages",
            self.repo / ".lake/build",
            self.repo / ".lake/config",
        ):
            directory.mkdir(parents=True, exist_ok=True)
        (self.repo / ".lake/build/fixture.olean").write_bytes(b"compiled fixture\n")

        _run("git", "init", "-b", "main", cwd=self.repo)
        _run("git", "config", "user.name", "Provenance Test", cwd=self.repo)
        _run("git", "config", "user.email", "provenance@example.test", cwd=self.repo)
        _run("git", "add", ".", cwd=self.repo)
        _run("git", "commit", "-m", "fixture", cwd=self.repo)
        self.base_commit = _run("git", "rev-parse", "HEAD", cwd=self.repo).stdout.strip()
        self.base_tree = _run("git", "rev-parse", "HEAD^{tree}", cwd=self.repo).stdout.strip()

        self.task = self.root / "task.json"
        self.task_document = self._task_document()
        self.task_bytes = _canonical_json(self.task, self.task_document)

        self.pi_install_manifest = self.root / "pi-install.json"
        self.pi_dependency_graph = self.root / "npm-ls.json"
        _canonical_json(self.pi_install_manifest, {})
        _canonical_json(self.pi_dependency_graph, {})
        self.config = self.root / "fixture.env"
        self.config.write_text(
            "\n".join(
                [
                    f"POINCARE_REPO_ROOT={self.repo}",
                    f"POINCARE_WORKTREE_ROOT={self.worktrees}",
                    "POINCARE_CODEX_BIN=/bin/true",
                    "POINCARE_GIT_BIN=/usr/bin/git",
                    "POINCARE_TMUX_BIN=/usr/bin/true",
                    f"POINCARE_PI_INSTALL_MANIFEST={self.pi_install_manifest}",
                    f"POINCARE_PI_DEPENDENCY_GRAPH={self.pi_dependency_graph}",
                    f"POINCARE_PI_LAKE_CACHE_ROOT={self.cache_root}",
                    f"POINCARE_PI_TOOLCHAIN_ROOT={self.toolchain}",
                    f"POINCARE_EXTRA_PATH={self.fake_bin}:{Path(sys.executable).parent}:/usr/local/bin:/usr/bin:/bin",
                    "POINCARE_INTEGRATION_BRANCH=main",
                    "POINCARE_LEANSTRAL_BASE_URL=http://127.0.0.1:9/v1",
                    "POINCARE_LEANSTRAL_SERVED_MODEL=leanstral-1.5",
                    "POINCARE_LEANSTRAL_ARTIFACT=mistralai/Leanstral-1.5-119B-A6B",
                    f"POINCARE_LEANSTRAL_REVISION={'1' * 40}",
                    "POINCARE_MIN_FREE_GIB=1",
                    "",
                ]
            ),
            encoding="utf-8",
        )
        self.config.chmod(0o600)
        self.recorder = self.repo / "harness/v2/deploy/record-lean-cache-provenance.sh"

    def tearDown(self) -> None:
        for directory, directories, files in os.walk(self.root):
            for name in directories:
                path = Path(directory, name)
                if not path.is_symlink():
                    path.chmod(path.stat().st_mode | stat.S_IWUSR)
            for name in files:
                path = Path(directory, name)
                if not path.is_symlink():
                    path.chmod(path.stat().st_mode | stat.S_IWUSR)
        self.temporary.cleanup()

    def _copy_control_surface(self) -> None:
        relative_paths = [
            "harness/__init__.py",
            "harness/v2/__init__.py",
            "harness/v2/runtime/__init__.py",
            "harness/v2/runtime/validation.py",
            "harness/v2/pi/__init__.py",
            "harness/v2/pi/install.py",
            "harness/v2/pi/security.py",
            "harness/v2/deploy/common.sh",
            "harness/v2/deploy/publish-lean-cache.sh",
            "harness/v2/deploy/verify-lean-cache.sh",
            "harness/v2/deploy/cache-sandbox-smoke.sh",
            "harness/v2/deploy/record-lean-cache-provenance.sh",
        ]
        for relative in relative_paths:
            source = ROOT / relative
            destination = self.repo / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
            if relative == "harness/v2/deploy/common.sh" and sys.platform == "darwin":
                contents = destination.read_text(encoding="utf-8")
                start = contents.index('if [[ "$(/usr/bin/uname -s)" == Linux ]]; then\n')
                marker = "export HARNESS_PI_PYTHON HARNESS_PI_FLOCK\n"
                end = contents.index(marker, start) + len(marker)
                contents = (
                    contents[:start]
                    + f"readonly HARNESS_PI_PYTHON={Path(sys.executable).resolve()}\n"
                    + f"readonly HARNESS_PI_FLOCK={self.fake_bin / 'flock'}\n"
                    + marker
                    + contents[end:]
                )
                destination.write_text(contents, encoding="utf-8")

    def _write_fake_tools(self) -> None:
        (self.toolchain / "bin").mkdir()
        (self.toolchain / "lib/lean").mkdir(parents=True)
        (self.toolchain / "lib/lean/compiler.dat").write_bytes(b"lean compiler fixture\n")
        lake = self.toolchain / "bin/lake"
        lake.write_text(
            "#!/bin/sh\n"
            "printf '%s\\n' \"$*\" >> \"$FAKE_LAKE_LOG\"\n"
            "printf 'lake stdout: %s\\n' \"$*\"\n"
            "printf 'lake stderr: %s\\n' \"$*\" >&2\n"
            "if [ \"${1:-}\" = env ] && [ \"${2:-}\" != \"$FAKE_EXPECTED_LEAN\" ]; then\n"
            "  printf 'unexpected Lean executable: %s\\n' \"${2:-}\" >&2\n"
            "  exit 98\n"
            "fi\n"
            "if [ -n \"${FAKE_TOOLCHAIN_DRIFT_MATCH:-}\" ]; then\n"
            "  case \"$*\" in\n"
            "    *\"$FAKE_TOOLCHAIN_DRIFT_MATCH\"*)\n"
            "      printf 'drift\\n' >> \"$FAKE_TOOLCHAIN_DRIFT_PATH\"\n"
            "      ;;\n"
            "  esac\n"
            "fi\n"
            "if [ -n \"${FAKE_LAKE_FAIL_MATCH:-}\" ]; then\n"
            "  case \"$*\" in *\"$FAKE_LAKE_FAIL_MATCH\"*) exit 17 ;; esac\n"
            "fi\n"
            "exit 0\n",
            encoding="utf-8",
        )
        lean = self.toolchain / "bin/lean"
        lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        shadow_lake = self.fake_bin / "lake"
        shadow_lake.write_text(
            "#!/bin/sh\nprintf 'untrusted PATH lake ran\\n' >&2\nexit 99\n",
            encoding="utf-8",
        )
        shadow_lean = self.fake_bin / "lean"
        shadow_lean.write_text(
            f"#!/bin/sh\nprintf ran > {self.shadow_lean_marker}\nexit 97\n",
            encoding="utf-8",
        )
        shadow_python = self.fake_bin / "python3"
        shadow_python.write_text(
            f"#!/bin/sh\nprintf ran > {self.shadow_python_marker}\nexit 96\n",
            encoding="utf-8",
        )
        flock = self.fake_bin / "flock"
        flock.write_text(
            "#!/bin/sh\n"
            "for arg in \"$@\"; do\n"
            "  case \"$arg\" in\n"
            "    --exclusive|--shared|--nonblock|--close) ;;\n"
            "    [0-9]*) exit 0 ;;\n"
            "    *) exit 64 ;;\n"
            "  esac\n"
            "done\n"
            "exit 64\n",
            encoding="utf-8",
        )
        rsync = self.fake_bin / "rsync"
        rsync.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        for path in (
            lake,
            lean,
            shadow_lake,
            shadow_lean,
            shadow_python,
            flock,
            rsync,
        ):
            path.chmod(0o755)

    def _task_document(self) -> dict[str, object]:
        return {
            "schema_version": "2.0",
            "id": "fixture-cache-task",
            "revision": 1,
            "status": "ready",
            "base_commit": self.base_commit,
            "objective": {
                "title": "Fixture module",
                "statement": "Verify one exact module gate after the root build.",
                "deliverables": ["Checked fixture module"],
            },
            "scope": {
                "allowed_paths": ["Module.lean"],
                "forbidden_paths": ["Poincare/Statement.lean", "harness/**"],
            },
            "context": {
                "files": ["Module.lean"],
                "symbols": ["moduleFixture"],
                "depends_on": [],
            },
            "acceptance": {
                "commands": [
                    [
                        "env",
                        "LEAN_NUM_THREADS=1",
                        "lake",
                        "env",
                        "lean",
                        "Module.lean",
                    ],
                    ["env", "LEAN_NUM_THREADS=1", "lake", "build", "Module"],
                    ["git", "diff", "--check"],
                ],
                "forbidden_added_tokens": ["sorry", "admit"],
            },
            "stop_conditions": ["The fixture module does not elaborate"],
            "budget": {
                "max_attempts": 1,
                "wall_clock_minutes": 10,
                "max_output_tokens": 1000,
                "disk_mb": 1024,
            },
        }

    def run_recorder(
        self,
        *,
        command_index: int = 0,
        task: Path | None = None,
        extra_env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment["FAKE_LAKE_LOG"] = str(self.lake_log)
        environment["FAKE_EXPECTED_LEAN"] = str(self.toolchain / "bin/lean")
        if extra_env:
            environment.update(extra_env)
        return _run(
            self.recorder,
            "--task",
            task or self.task,
            "--command-index",
            str(command_index),
            self.config,
            cwd=self.repo,
            check=False,
            env=environment,
        )

    def bundles(self) -> list[Path]:
        root = self.repo / f"harness/v2/state/cache-provenance/{self.base_commit}"
        return sorted(path for path in root.iterdir() if path.is_dir()) if root.exists() else []


class CacheProvenanceRecorderTest(CacheProvenanceRecorderFixture):
    def test_records_publisher_compatible_append_only_provenance(self) -> None:
        result = self.run_recorder()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Recorded immutable cache provenance:", result.stdout)
        self.assertEqual(
            self.lake_log.read_text(encoding="utf-8").splitlines(),
            [
                "build",
                f"env {self.toolchain / 'bin/lean'} Poincare.lean",
                f"env {self.toolchain / 'bin/lean'} Module.lean",
            ],
        )
        self.assertFalse(self.shadow_python_marker.exists())
        self.assertFalse(self.shadow_lean_marker.exists())

        [bundle] = self.bundles()
        self.assertEqual(stat.S_IMODE(bundle.stat().st_mode), 0o500)
        self.assertEqual((bundle / "task.json").read_bytes(), self.task_bytes)
        provenance_path = bundle / "provenance.json"
        provenance_raw = provenance_path.read_bytes()
        provenance = json.loads(provenance_raw)
        self.assertEqual(
            provenance_raw,
            (
                json.dumps(
                    provenance,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=True,
                )
                + "\n"
            ).encode("ascii"),
        )
        self.assertEqual(provenance["schema_version"], "poincare.cache-provenance.v1")
        self.assertEqual(provenance["base_commit"], self.base_commit)
        self.assertEqual(provenance["base_tree"], self.base_tree)
        self.assertEqual(
            provenance["root_build"]["commands"][0]["argv"],
            ["env", "LEAN_NUM_THREADS=1", "lake", "build"],
        )
        self.assertEqual(
            provenance["root_build"]["commands"][1]["argv"],
            ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "Poincare.lean"],
        )
        self.assertEqual(
            provenance["module_gate"]["argv"],
            self.task_document["acceptance"]["commands"][0],
        )
        self.assertEqual(provenance["module_gate"]["command_index"], 0)
        self.assertEqual(
            set(provenance["executables"]),
            {"git", "lake", "lean"},
        )
        self.assertEqual(
            provenance["executables"]["lean"]["path"],
            str(self.toolchain / "bin/lean"),
        )
        self.assertEqual(
            provenance["lean_toolchain"]["root"],
            str(self.toolchain),
        )
        self.assertEqual(
            provenance["lean_toolchain"]["compiler_lib"]["path"],
            str(self.toolchain / "lib/lean"),
        )
        self.assertRegex(
            provenance["lean_toolchain"]["compiler_lib"]["tree_sha256"],
            r"^[0-9a-f]{64}$",
        )
        self.assertGreater(
            provenance["lean_toolchain"]["compiler_lib"]["entry_count"],
            0,
        )
        self.assertRegex(provenance["source_cache_projection_sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(
            provenance["selected_task"]["source"],
            {"path": "task.json", "sha256": _sha256(bundle / "task.json")},
        )
        for path in bundle.iterdir():
            self.assertTrue(path.is_file())
            self.assertEqual(stat.S_IMODE(path.stat().st_mode), 0o400, path.name)
        self.assertFalse((bundle / "failure.json").exists())

    def test_selected_lake_build_gate_is_accepted_and_bundles_do_not_overwrite(self) -> None:
        first = self.run_recorder(command_index=1)
        second = self.run_recorder(command_index=1)
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(second.returncode, 0, second.stderr)
        bundles = self.bundles()
        self.assertEqual(len(bundles), 2)
        for bundle in bundles:
            provenance = json.loads((bundle / "provenance.json").read_text())
            self.assertEqual(provenance["module_gate"]["command_index"], 1)
            self.assertEqual(
                provenance["module_gate"]["argv"],
                ["env", "LEAN_NUM_THREADS=1", "lake", "build", "Module"],
            )

    def test_failed_gate_preserves_sealed_evidence_without_provenance(self) -> None:
        result = self.run_recorder(extra_env={"FAKE_LAKE_FAIL_MATCH": "Module.lean"})
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("module-gate failed with exit code 17", result.stderr)
        [bundle] = self.bundles()
        self.assertFalse((bundle / "provenance.json").exists())
        failure = json.loads((bundle / "failure.json").read_text())
        self.assertEqual(failure["status"], "failed")
        self.assertEqual(len(failure["commands"]), 3)
        self.assertEqual(failure["commands"][-1]["exit_code"], 17)
        self.assertIn("lake stdout", (bundle / "module-gate.stdout").read_text())
        self.assertIn("lake stderr", (bundle / "module-gate.stderr").read_text())
        self.assertEqual(stat.S_IMODE(bundle.stat().st_mode), 0o500)
        for path in bundle.iterdir():
            self.assertEqual(stat.S_IMODE(path.stat().st_mode), 0o400)

    def test_rejects_non_lean_command_and_symlink_task(self) -> None:
        command_result = self.run_recorder(command_index=2)
        self.assertNotEqual(command_result.returncode, 0)
        self.assertIn("single-threaded Lean source or Lake module build", command_result.stderr)
        self.assertEqual(self.bundles(), [])

        task_link = self.root / "task-link.json"
        task_link.symlink_to(self.task)
        link_result = self.run_recorder(task=task_link)
        self.assertNotEqual(link_result.returncode, 0)
        self.assertIn("must not traverse a symbolic link", link_result.stderr)
        self.assertEqual(self.bundles(), [])

    def test_rejects_gate_outside_task_scope_and_context(self) -> None:
        outside = self.repo / "Outside.lean"
        outside.write_text("def outsideFixture : True := True.intro\n", encoding="utf-8")
        _run("git", "add", "Outside.lean", cwd=self.repo)
        _run("git", "commit", "-m", "outside fixture", cwd=self.repo)
        self.base_commit = _run("git", "rev-parse", "HEAD", cwd=self.repo).stdout.strip()
        self.base_tree = _run("git", "rev-parse", "HEAD^{tree}", cwd=self.repo).stdout.strip()
        task = self._task_document()
        task["acceptance"]["commands"][0][-1] = "Outside.lean"
        self.task.chmod(0o600)
        _canonical_json(self.task, task)
        result = self.run_recorder()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("outside its allowed/context source scope", result.stderr)
        self.assertEqual(self.bundles(), [])

    def test_rejects_mutable_task_and_dirty_exact_base(self) -> None:
        self.task.chmod(0o600)
        mutable = self.run_recorder()
        self.assertNotEqual(mutable.returncode, 0)
        self.assertIn("Task source must be immutable", mutable.stderr)
        self.assertEqual(self.bundles(), [])

        self.task.chmod(0o400)
        (self.repo / "Module.lean").write_text(
            "def moduleFixture : True := by trivial\n", encoding="utf-8"
        )
        dirty = self.run_recorder()
        self.assertNotEqual(dirty.returncode, 0)
        self.assertIn("requires a clean exact-base source", dirty.stderr)
        self.assertEqual(self.bundles(), [])

    def test_shared_build_job_lock_is_nonblocking_and_failure_is_retained(self) -> None:
        state = self.repo / "harness/v2/state"
        state.mkdir(parents=True)
        lock_path = state / "build-job.lock"
        descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = self.run_recorder()
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("holds the shared build/Job lock", result.stderr)
        [bundle] = self.bundles()
        self.assertFalse((bundle / "provenance.json").exists())
        self.assertTrue((bundle / "failure.json").is_file())

    def test_compiler_library_drift_during_recording_fails_closed(self) -> None:
        result = self.run_recorder(
            extra_env={
                "FAKE_TOOLCHAIN_DRIFT_MATCH": "Module.lean",
                "FAKE_TOOLCHAIN_DRIFT_PATH": str(
                    self.toolchain / "lib/lean/compiler.dat"
                ),
            }
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "Lean toolchain closure changed during provenance recording",
            result.stderr,
        )
        [bundle] = self.bundles()
        self.assertFalse((bundle / "provenance.json").exists())
        self.assertTrue((bundle / "failure.json").is_file())


if __name__ == "__main__":
    unittest.main()
