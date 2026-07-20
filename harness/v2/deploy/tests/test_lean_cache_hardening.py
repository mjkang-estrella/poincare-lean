from __future__ import annotations

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

from harness.v2.pi.security import _sealed_tree_attestation


ROOT = Path(__file__).resolve().parents[4]
DEPLOY = ROOT / "harness/v2/deploy"


def _run(*argv: str | Path, cwd: Path | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(item) for item in argv],
        cwd=cwd,
        check=check,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _canonical_json(path: Path, value: object, mode: int = 0o400) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode(
        "ascii"
    )
    path.write_bytes(raw)
    path.chmod(mode)


class LeanCacheHardeningFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="poincare-cache-hardening-")
        self.root = Path(self.temporary.name).resolve()
        self.repo = self.root / "repo"
        self.cache_root = self.root / "cache"
        self.worktrees = self.root / "worktrees"
        self.toolchain = self.root / "toolchain"
        self.fake_bin = self.root / "bin"
        self.shadow_python_marker = self.root / "shadow-python-ran"
        for path in (
            self.repo,
            self.cache_root,
            self.worktrees,
            self.toolchain,
            self.fake_bin,
        ):
            path.mkdir()

        self._write_fake_tools()
        self._copy_control_surface()
        (self.repo / ".gitignore").write_text(
            ".lake/\nharness/v2/state/\n__pycache__/\n",
            encoding="utf-8",
        )
        (self.repo / "lean-toolchain").write_text("leanprover/lean4:v4.30.0-rc2\n", encoding="utf-8")
        (self.repo / "Poincare.lean").write_text("def rootFixture : True := True.intro\n", encoding="utf-8")
        (self.repo / "Module.lean").write_text("def moduleFixture : True := True.intro\n", encoding="utf-8")

        package = self.repo / ".lake/packages/dep"
        package.mkdir(parents=True)
        _run("git", "init", "-b", "main", cwd=package)
        _run("git", "config", "user.name", "Cache Test", cwd=package)
        _run("git", "config", "user.email", "cache@example.test", cwd=package)
        (package / "pkg.txt").write_text("verified dependency\n", encoding="utf-8")
        _run("git", "add", "pkg.txt", cwd=package)
        _run("git", "commit", "-m", "fixture package", cwd=package)
        self.package_commit = _run("git", "rev-parse", "HEAD", cwd=package).stdout.strip()
        self.package_tree = _run("git", "rev-parse", "HEAD^{tree}", cwd=package).stdout.strip()
        self.package_url = "https://example.test/dep.git"
        _run("git", "remote", "add", "origin", self.package_url, cwd=package)

        for path in (self.repo / ".lake/build", self.repo / ".lake/config"):
            path.mkdir(parents=True)
        manifest = {
            "version": "1.1.0",
            "packagesDir": ".lake/packages",
            "lakeDir": ".lake",
            "packages": [
                {
                    "name": "dep",
                    "scope": "fixture",
                    "type": "git",
                    "url": self.package_url,
                    "rev": self.package_commit,
                    "inherited": False,
                    "configFile": "lakefile.toml",
                    "manifestFile": "lake-manifest.json",
                }
            ],
        }
        _canonical_json(self.repo / "lake-manifest.json", manifest, mode=0o644)

        _run("git", "init", "-b", "main", cwd=self.repo)
        _run("git", "config", "user.name", "Cache Test", cwd=self.repo)
        _run("git", "config", "user.email", "cache@example.test", cwd=self.repo)
        _run("git", "add", ".", cwd=self.repo)
        _run("git", "commit", "-m", "fixture control and source", cwd=self.repo)
        self.base_commit = _run("git", "rev-parse", "HEAD", cwd=self.repo).stdout.strip()
        self.base_tree = _run("git", "rev-parse", "HEAD^{tree}", cwd=self.repo).stdout.strip()

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
        self.publisher = self.repo / "harness/v2/deploy/publish-lean-cache.sh"
        self.verifier = self.repo / "harness/v2/deploy/verify-lean-cache.sh"

    def tearDown(self) -> None:
        # Successful publication intentionally freezes every directory. Restore
        # owner write permission only so TemporaryDirectory can remove its own
        # fixture tree.
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

    def _write_fake_tools(self) -> None:
        toolchain_bin = self.toolchain / "bin"
        toolchain_bin.mkdir()
        compiler_lib = self.toolchain / "lib/lean"
        compiler_lib.mkdir(parents=True)
        (compiler_lib / "compiler.dat").write_bytes(b"lean compiler fixture\n")
        lake = toolchain_bin / "lake"
        lake.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        lean = toolchain_bin / "lean"
        lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        git = self.fake_bin / "git"
        git.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
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
        move = self.fake_bin / "mv"
        move.write_text(
            "#!/bin/sh\n"
            "while [ \"$#\" -gt 0 ]; do\n"
            "  case \"$1\" in -T|-n|--) shift ;; *) break ;; esac\n"
            "done\n"
            "[ \"$#\" -eq 2 ] || exit 64\n"
            "[ ! -e \"$2\" ] || exit 0\n"
            "exec /bin/mv \"$1\" \"$2\"\n",
            encoding="utf-8",
        )
        chmod = self.fake_bin / "chmod"
        chmod.write_text(
            "#!/bin/sh\n"
            "args=\n"
            "for arg in \"$@\"; do\n"
            "  [ \"$arg\" = -- ] && continue\n"
            "  args=\"$args '$arg'\"\n"
            "done\n"
            "eval \"exec /bin/chmod $args\"\n",
            encoding="utf-8",
        )
        shadow_python = self.fake_bin / "python3"
        shadow_python.write_text(
            f"#!/bin/sh\nprintf ran > {self.shadow_python_marker}\nexit 96\n",
            encoding="utf-8",
        )
        lake.chmod(0o755)
        lean.chmod(0o755)
        git.chmod(0o755)
        flock.chmod(0o755)
        move.chmod(0o755)
        chmod.chmod(0o755)
        shadow_python.chmod(0o755)

    def _copy_control_surface(self) -> None:
        paths = [
            "harness/__init__.py",
            "harness/v2/__init__.py",
            "harness/v2/pi/__init__.py",
            "harness/v2/pi/install.py",
            "harness/v2/pi/security.py",
            "harness/v2/deploy/common.sh",
            "harness/v2/deploy/record-lean-cache-provenance.sh",
            "harness/v2/deploy/publish-lean-cache.sh",
            "harness/v2/deploy/verify-lean-cache.sh",
            "harness/v2/deploy/cache-sandbox-smoke.sh",
        ]
        for relative in paths:
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

    def source_projection(self) -> str:
        result = _run(
            self.publisher,
            "--source-root",
            self.repo,
            "--print-source-projection",
            self.config,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        projection = result.stdout.strip()
        self.assertRegex(projection, r"^[0-9a-f]{64}$")
        return projection

    def make_provenance(self, projection: str) -> Path:
        bundle = (
            self.repo
            / "harness/v2/state/cache-provenance"
            / self.base_commit
            / "fixture-publication"
        )
        bundle.mkdir(parents=True)
        task_path = bundle / "task.json"
        root_build_stdout = bundle / "root-build.stdout"
        root_build_stderr = bundle / "root-build.stderr"
        root_lean_stdout = bundle / "root-lean.stdout"
        root_lean_stderr = bundle / "root-lean.stderr"
        gate_stdout = bundle / "module-gate.stdout"
        gate_stderr = bundle / "module-gate.stderr"
        gate_argv = ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "Module.lean"]
        task = {
            "schema_version": "2.0",
            "id": "fixture-task",
            "revision": 1,
            "status": "proposed",
            "base_commit": self.base_commit,
            "acceptance": {"commands": [gate_argv]},
        }
        _canonical_json(task_path, task)
        for path, content in (
            (root_build_stdout, b"root build passed\n"),
            (root_build_stderr, b""),
            (root_lean_stdout, b"root elaboration passed\n"),
            (root_lean_stderr, b""),
            (gate_stdout, b"module gate passed\n"),
            (gate_stderr, b""),
        ):
            path.write_bytes(content)
            path.chmod(0o400)

        def reference(path: Path) -> dict[str, str]:
            return {"path": path.name, "sha256": _sha256(path)}

        def executable_record(path: Path) -> dict[str, object]:
            info = path.stat()
            return {
                "path": str(path.resolve()),
                "sha256": _sha256(path),
                "size_bytes": info.st_size,
                "mode": stat.S_IMODE(info.st_mode),
            }

        compiler_lib = self.toolchain / "lib/lean"
        compiler_digest, compiler_count, _ = _sealed_tree_attestation(
            compiler_lib,
            "fixture Lean compiler library",
            require_sealed=False,
            allow_internal_symlinks=True,
        )

        def step(
            argv: list[str], started: str, completed: str, stdout: Path, stderr: Path
        ) -> dict[str, object]:
            return {
                "argv": argv,
                "status": "passed",
                "exit_code": 0,
                "started_at": started,
                "completed_at": completed,
                "stdout": reference(stdout),
                "stderr": reference(stderr),
            }

        provenance = {
            "schema_version": "poincare.cache-provenance.v1",
            "base_commit": self.base_commit,
            "base_tree": self.base_tree,
            "source_root": str(self.repo),
            "source_cache_projection_sha256": projection,
            "exclusion_lock": str(self.repo / "harness/v2/state/build-job.lock"),
            "executables": {
                "git": executable_record(Path("/usr/bin/git")),
                "lake": executable_record(self.toolchain / "bin/lake"),
                "lean": executable_record(self.toolchain / "bin/lean"),
            },
            "lean_toolchain": {
                "root": str(self.toolchain),
                "compiler_lib": {
                    "path": str(compiler_lib),
                    "tree_sha256": compiler_digest,
                    "entry_count": compiler_count,
                },
            },
            "root_build": {
                "commands": [
                    step(
                        ["env", "LEAN_NUM_THREADS=1", "lake", "build"],
                        "2026-07-19T18:00:00Z",
                        "2026-07-19T18:01:00Z",
                        root_build_stdout,
                        root_build_stderr,
                    ),
                    step(
                        ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "Poincare.lean"],
                        "2026-07-19T18:01:00Z",
                        "2026-07-19T18:02:00Z",
                        root_lean_stdout,
                        root_lean_stderr,
                    ),
                ]
            },
            "selected_task": {
                "id": "fixture-task",
                "revision": 1,
                "base_commit": self.base_commit,
                "source": reference(task_path),
            },
            "module_gate": {
                **step(
                    gate_argv,
                    "2026-07-19T18:02:00Z",
                    "2026-07-19T18:03:00Z",
                    gate_stdout,
                    gate_stderr,
                ),
                "command_index": 0,
            },
        }
        record = bundle / "provenance.json"
        _canonical_json(record, provenance)
        return record

    def publish(self, provenance: Path) -> subprocess.CompletedProcess[str]:
        return _run(
            self.publisher,
            "--source-root",
            self.repo,
            "--provenance",
            provenance,
            self.config,
            check=False,
        )


class LeanCacheHardeningTest(LeanCacheHardeningFixture):
    def test_cache_authority_scripts_do_not_resolve_python_from_path(self) -> None:
        for name in (
            "record-lean-cache-provenance.sh",
            "publish-lean-cache.sh",
            "verify-lean-cache.sh",
            "cache-sandbox-smoke.sh",
        ):
            source = (DEPLOY / name).read_text(encoding="utf-8")
            self.assertNotIn("python3", source, name)
            self.assertIn('"$HARNESS_PI_PYTHON"', source, name)

    def test_publish_binds_dependency_and_provenance_and_verify_rehashes(self) -> None:
        provenance = self.make_provenance(self.source_projection())
        result = self.publish(provenance)
        audits = list((self.repo / "harness/v2/state/deploy").glob("cache-copy-*.txt"))
        diagnostics = "\n".join(path.read_text(encoding="utf-8") for path in audits)
        self.assertEqual(result.returncode, 0, f"{result.stderr}\n{diagnostics}")
        self.assertFalse(self.shadow_python_marker.exists())
        cache = self.cache_root / self.base_commit
        identities = json.loads((cache / ".harness-package-identities.json").read_text())
        self.assertEqual(
            identities["packages"],
            [
                {
                    "name": "dep",
                    "manifest_url": self.package_url,
                    "manifest_rev": self.package_commit,
                    "checkout_head": self.package_commit,
                    "expected_tree": self.package_tree,
                    "checkout_tree": self.package_tree,
                }
            ],
        )
        self.assertEqual(
            (cache / ".harness-cache-provenance.json").read_bytes(),
            provenance.read_bytes(),
        )
        recovered = self.publish(provenance)
        self.assertEqual(recovered.returncode, 0, recovered.stderr)
        self.assertIn("Recovered the verified immutable Lake cache publication", recovered.stdout)

        cached_package = cache / "packages/dep/pkg.txt"
        original_mode = stat.S_IMODE(cached_package.stat().st_mode)
        cached_package.chmod(original_mode | stat.S_IWUSR)
        cached_package.write_text("tampered dependency\n", encoding="utf-8")
        cached_package.chmod(original_mode)
        verified = _run(
            self.verifier,
            "--source-root",
            self.repo,
            self.config,
            check=False,
        )
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("content digest mismatch", verified.stderr)

    def test_dirty_manifest_dependency_is_rejected_and_staging_is_preserved(self) -> None:
        package = self.repo / ".lake/packages/dep"
        (package / "untracked.txt").write_text("not attested\n", encoding="utf-8")
        provenance = self.make_provenance(self.source_projection())
        result = self.publish(provenance)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("dependency package is dirty: dep", result.stderr)
        self.assertFalse((self.cache_root / self.base_commit).exists())
        self.assertEqual(len(list(self.cache_root.glob(f".staging.{self.base_commit}.*"))), 1)

    def test_mutable_provenance_is_rejected_before_staging(self) -> None:
        provenance = self.make_provenance(self.source_projection())
        provenance.chmod(0o600)
        result = self.publish(provenance)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cache provenance must be owner-controlled and immutable", result.stderr)
        self.assertFalse(any(self.cache_root.glob(".staging.*")))

    def test_publish_rejects_pinned_lean_executable_drift_before_staging(self) -> None:
        provenance = self.make_provenance(self.source_projection())
        lean = self.toolchain / "bin/lean"
        lean.write_text("#!/bin/sh\nexit 19\n", encoding="utf-8")
        result = self.publish(provenance)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("pinned Git/Lake/Lean", result.stderr)
        self.assertFalse(any(self.cache_root.glob(".staging.*")))

    def test_publish_rejects_compiler_library_drift_before_staging(self) -> None:
        provenance = self.make_provenance(self.source_projection())
        (self.toolchain / "lib/lean/compiler.dat").write_bytes(b"drifted compiler\n")
        result = self.publish(provenance)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Lean toolchain closure identity changed", result.stderr)
        self.assertFalse(any(self.cache_root.glob(".staging.*")))

    def test_verify_rejects_compiler_library_drift_after_publication(self) -> None:
        provenance = self.make_provenance(self.source_projection())
        result = self.publish(provenance)
        self.assertEqual(result.returncode, 0, result.stderr)
        (self.toolchain / "lib/lean/compiler.dat").write_bytes(b"later drift\n")
        verified = _run(
            self.verifier,
            "--source-root",
            self.repo,
            self.config,
            check=False,
        )
        self.assertNotEqual(verified.returncode, 0)
        self.assertIn("Lean toolchain closure identity changed", verified.stderr)


if __name__ == "__main__":
    unittest.main()
