from __future__ import annotations

import hashlib
import fcntl
import json
import os
import shutil
import socket
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from harness.v2.pi import security
from harness.v2.pi.install import PI_MINIMUM_NODE_VERSION
from harness.v2.pi.security import (
    ProcessResourceLimits,
    SecurityError,
    acquire_build_job_lock,
    audit_pi_bubblewrap,
    audit_sparse_lean_bubblewrap,
    bubblewrap_pi_argv,
    bubblewrap_sparse_lean_argv,
    build_sparse_lean_snapshot,
    canonical_package_overrides,
    lake_cache_tree_digest,
    pi_distribution_tree_digest,
    remove_sparse_lean_snapshot,
    run_limited,
    sparse_lean_process_limits,
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _node_attestation(path: Path) -> dict[str, object]:
    metadata = path.stat(follow_symlinks=False)
    return {
        "path": str(path),
        "sha256": _sha256(path),
        "size_bytes": metadata.st_size,
        "mode": stat.S_IMODE(metadata.st_mode),
        "minimum_version": PI_MINIMUM_NODE_VERSION,
        "version": "22.22.1",
    }


def _seal_tree(root: Path) -> None:
    for directory, _, files in os.walk(root, topdown=False):
        base = Path(directory)
        for name in files:
            path = base / name
            if not path.is_symlink():
                path.chmod(0o444)
        base.chmod(0o555)


def _unseal_tree(root: Path) -> None:
    if not root.exists() or root.is_symlink():
        return
    for directory, child_directories, files in os.walk(root, topdown=False):
        base = Path(directory)
        for name in files:
            path = base / name
            if not path.is_symlink() and not path.is_socket():
                try:
                    path.chmod(0o600)
                except OSError:
                    pass
        for name in child_directories:
            try:
                (base / name).chmod(0o700)
            except OSError:
                pass
        try:
            base.chmod(0o700)
        except OSError:
            pass


class SecurityProfileTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="psp-", dir="/tmp")
        self.root = Path(self.temporary.name).resolve()

    def tearDown(self) -> None:
        _unseal_tree(self.root)
        self.temporary.cleanup()

    def _elf(self, path: Path) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"\x7fELF" + path.name.encode("ascii"))
        path.chmod(0o555)
        return path

    def _sealed_input(self, name: str, data: bytes) -> Path:
        path = self.root / "inputs" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        path.chmod(0o444)
        return path

    def test_pi_runtime_mounts_exact_externalized_node_builtins(self) -> None:
        external = self.root / "system/acorn.js"
        external.parent.mkdir(parents=True)
        external.write_bytes(b"externalized builtin\n")
        external.chmod(0o444)
        libraries = [
            {
                "source": "/lib/libnode.so",
                "destination": "/lib/libnode.so",
                "sha256": "0" * 64,
            }
        ]
        with (
            patch.object(
                security,
                "_runtime_library_mounts",
                return_value=(libraries, []),
            ),
            patch.object(
                security,
                "_NODE_EXTERNALIZED_BUILTIN_PATHS",
                (external,),
            ),
        ):
            mounts, symlinks = security._pi_runtime_mounts(
                Path("/usr/bin/node"), ()
            )
        self.assertEqual(symlinks, [])
        self.assertEqual(
            mounts,
            [
                libraries[0],
                {
                    "source": str(external),
                    "destination": str(external),
                    "sha256": _sha256(external),
                },
            ],
        )

    def test_pi_profile_uses_canonical_install_digest_and_bounded_tmpfs(self) -> None:
        bwrap = self._elf(self.root / "tools/bwrap")
        node = self._elf(self.root / "tools/node")
        runtime_library = self.root / "tools/libnode-runtime.so"
        runtime_library.write_bytes(b"runtime library")
        runtime_library.chmod(0o444)
        runtime_mounts = [
            {
                "source": str(runtime_library),
                "destination": "/lib/libnode-runtime.so",
                "sha256": _sha256(runtime_library),
            }
        ]

        install = self.root / "pi-install"
        cli = install / "dist/cli.js"
        cli.parent.mkdir(parents=True)
        cli.write_bytes(b"console.log('pi')\n")
        _seal_tree(install)
        entries = [
            {"kind": "directory", "mode": 0o555, "path": "dist"},
            {
                "kind": "file",
                "mode": 0o444,
                "path": "dist/cli.js",
                "sha256": _sha256(cli),
                "size_bytes": cli.stat().st_size,
            },
        ]
        canonical = json.dumps(
            {"entries": entries, "root_mode": 0o555},
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        expected_tree = hashlib.sha256(
            b"poincare-harness-v2-pi-install-tree-v1\0" + canonical
        ).hexdigest()
        self.assertEqual(pi_distribution_tree_digest(install), expected_tree)

        extension = self._sealed_input("extension.ts", b"export default {}\n")
        public_config = self._sealed_input("public-config.json", b"{}\n")
        system_prompt = self._sealed_input("system-prompt.md", b"prove it\n")
        settings = self._sealed_input("settings.json", b"{}\n")
        forbidden = []
        for name in ("worktree", "control", "state", "artifacts"):
            path = self.root / name
            path.mkdir(mode=0o700)
            forbidden.append(path)
        broker_dir = self.root / "broker"
        broker_dir.mkdir(mode=0o700)
        broker_socket = broker_dir / "broker.sock"
        endpoint = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        endpoint.bind(str(broker_socket))
        broker_socket.chmod(0o600)
        try:
            with (
                patch.object(security.sys, "platform", "linux"),
                patch.object(
                    security,
                    "_runtime_library_mounts",
                    return_value=(runtime_mounts, []),
                ) as runtime_probe,
            ):
                def audit(node_attestation: dict[str, object]) -> dict[str, object]:
                    return audit_pi_bubblewrap(
                        configured_path=str(bwrap),
                        expected_node_attestation=node_attestation,
                        install_root=install,
                        cli_relative="dist/cli.js",
                        expected_install_tree_sha256=expected_tree,
                        extension_path=extension,
                        extension_sha256=_sha256(extension),
                        public_config_path=public_config,
                        public_config_sha256=_sha256(public_config),
                        system_prompt_path=system_prompt,
                        system_prompt_sha256=_sha256(system_prompt),
                        settings_path=settings,
                        settings_sha256=_sha256(settings),
                        broker_socket=broker_socket,
                        forbidden_paths=forbidden,
                        runtime_tmpfs_bytes=8 * 1024 * 1024,
                        tmp_tmpfs_bytes=4 * 1024 * 1024,
                        run_tmpfs_bytes=1024 * 1024,
                    )

                expected_node = _node_attestation(node)
                original_node = node.with_name("node-attested-original")
                node.rename(original_node)
                node.write_bytes(b"\x7fELFreplacement-node")
                node.chmod(0o555)
                with self.assertRaisesRegex(
                    SecurityError, "differs from the sealed install manifest"
                ):
                    audit(expected_node)
                runtime_probe.assert_not_called()
                node.unlink()
                original_node.rename(node)
                spec = audit(expected_node)
                self.assertEqual(
                    {
                        "path": spec["node"]["source"],
                        "sha256": spec["node"]["sha256"],
                        "size_bytes": spec["node"]["size_bytes"],
                        "mode": spec["node"]["mode"],
                        "minimum_version": spec["node"]["minimum_version"],
                        "version": spec["node"]["version"],
                    },
                    expected_node,
                )
                self.assertEqual(
                    spec["inputs"]["settings"]["destination"],
                    "/sealed/agent/settings.json",
                )
                self.assertEqual(
                    spec["inputs"]["settings"]["sha256"], _sha256(settings)
                )
                for field, replacement in (
                    ("sha256", "0" * 64),
                    ("size_bytes", expected_node["size_bytes"] + 1),
                    ("mode", 0o500),
                ):
                    with self.subTest(node_manifest_drift=field):
                        drifted_node = dict(expected_node)
                        drifted_node[field] = replacement
                        with self.assertRaisesRegex(
                            SecurityError, "differs from the sealed install manifest"
                        ):
                            audit(drifted_node)
                        runtime_probe.assert_called_once()
                argv = list(
                    bubblewrap_pi_argv(
                        spec=spec,
                        pi_arguments=("--json", "--no-session"),
                        broker_token="t" * 32,
                    )
                )
                self.assertEqual(argv.index("--share-net"), argv.index("--unshare-all") + 1)
                self.assertIn("--unshare-user", argv)
                self.assertNotIn("--bind", argv)
                self.assertIn(
                    ["--size", str(8 * 1024 * 1024), "--tmpfs", "/runtime"],
                    [argv[index : index + 4] for index in range(len(argv) - 3)],
                )
                self.assertIn(
                    ["--setenv", "HARNESS_PI_BROKER_TOKEN", "t" * 32],
                    [argv[index : index + 3] for index in range(len(argv) - 2)],
                )
                self.assertIn(
                    ["--setenv", "PI_CODING_AGENT_DIR", "/sealed/agent"],
                    [argv[index : index + 3] for index in range(len(argv) - 2)],
                )
                self.assertIn(
                    ["--ro-bind", str(settings), "/sealed/agent/settings.json"],
                    [argv[index : index + 3] for index in range(len(argv) - 2)],
                )
                self.assertEqual(
                    argv[-4:],
                    [
                        "/opt/pi-node/node",
                        "/opt/pi-install/dist/cli.js",
                        "--json",
                        "--no-session",
                    ],
                )
                for path in forbidden:
                    self.assertNotIn(str(path), argv)
                for forbidden_program in (
                    "/bin/sh",
                    "/bin/bash",
                    "/usr/bin/git",
                    "/usr/bin/python",
                    "/usr/bin/python3",
                ):
                    self.assertNotIn(forbidden_program, argv)
                for index, item in enumerate(argv[:-2]):
                    if item == "--ro-bind":
                        self.assertFalse(argv[index + 2].startswith(str(self.root)))

                settings.chmod(0o600)
                settings.write_bytes(b'{"compaction":{"enabled":true}}')
                settings.chmod(0o444)
                with self.assertRaisesRegex(SecurityError, "settings digest mismatch"):
                    bubblewrap_pi_argv(
                        spec=spec,
                        pi_arguments=("--json",),
                        broker_token="t" * 32,
                    )
                settings.chmod(0o600)
                settings.write_bytes(b"{}\n")
                settings.chmod(0o444)

                node.chmod(0o500)
                with self.assertRaisesRegex(SecurityError, "Node changed"):
                    bubblewrap_pi_argv(
                        spec=spec,
                        pi_arguments=("--json",),
                        broker_token="t" * 32,
                    )
                node.chmod(0o555)

                install.chmod(0o755)
                drift = install / "unrelated.js"
                drift.write_bytes(b"drift")
                drift.chmod(0o444)
                install.chmod(0o555)
                with self.assertRaisesRegex(SecurityError, "installation changed"):
                    bubblewrap_pi_argv(
                        spec=spec,
                        pi_arguments=("--json",),
                        broker_token="t" * 32,
                    )
        finally:
            endpoint.close()

    def test_pi_distribution_rejects_every_install_write_bit(self) -> None:
        targets = {
            "root": lambda install, _file: install,
            "directory": lambda _install, file: file.parent,
            "file": lambda _install, file: file,
        }
        case = 0
        for label, select in targets.items():
            for write_bit in (stat.S_IWUSR, stat.S_IWGRP, stat.S_IWOTH):
                case += 1
                with self.subTest(target=label, write_bit=oct(write_bit)):
                    install = self.root / f"pi-install-mode-{case}"
                    file = install / "dist/cli.js"
                    file.parent.mkdir(parents=True)
                    file.write_bytes(b"console.log('pi')\n")
                    _seal_tree(install)
                    target = select(install, file)
                    target.chmod(stat.S_IMODE(target.stat().st_mode) | write_bit)
                    with self.assertRaisesRegex(SecurityError, "writable mode bit"):
                        pi_distribution_tree_digest(install)
                    _unseal_tree(install)

    def _git_worktree(self) -> tuple[Path, Path]:
        git = Path("/usr/bin/git")
        if not git.is_file() or git.is_symlink():
            self.skipTest("tests require fixed non-symlink /usr/bin/git")
        worktree = self.root / "worktree"
        (worktree / "Poincare").mkdir(parents=True)
        (worktree / "Poincare/Target.lean").write_text(
            "theorem target : True := by trivial\n", encoding="utf-8"
        )
        (worktree / "Poincare/Unrelated.lean").write_text(
            "theorem unrelated : True := by trivial\n", encoding="utf-8"
        )
        (worktree / "lakefile.lean").write_text("package Poincare\n", encoding="utf-8")
        (worktree / "lake-manifest.json").write_text(
            json.dumps(
                {
                    "version": "1.1.0",
                    "packagesDir": ".lake/packages",
                    "lakeDir": ".lake",
                    "packages": [
                        {
                            "type": "git",
                            "name": "mathlib",
                            "scope": "",
                            "inherited": False,
                            "configFile": "lakefile.lean",
                            "manifestFile": "lake-manifest.json",
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        (worktree / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n", encoding="utf-8")
        subprocess.run((str(git), "init", "-q", str(worktree)), check=True)
        subprocess.run((str(git), "-C", str(worktree), "add", "."), check=True)
        return worktree, git

    def test_sparse_snapshot_is_exact_rejects_unsafe_sources_and_cleans_up(self) -> None:
        worktree, git = self._git_worktree()
        checks_root = self.root / "lean-checks"
        check_dir = checks_root / "check-1"
        check_dir.mkdir(parents=True, mode=0o700)
        checks_root.chmod(0o700)
        snapshot = build_sparse_lean_snapshot(
            worktree=worktree,
            acceptance_commands=(("lake", "env", "lean", "Poincare/Target.lean"),),
            output_dir=check_dir / "source",
            git_path=git,
        )
        self.assertEqual(
            [item["path"] for item in snapshot["files"]],
            [
                "Poincare/Target.lean",
                "lake-manifest.json",
                "lakefile.lean",
                "lean-toolchain",
            ],
        )
        self.assertTrue((Path(snapshot["root"]) / ".lake").is_dir())
        self.assertEqual(stat.S_IMODE((Path(snapshot["root"]) / ".lake").stat().st_mode), 0o555)
        self.assertFalse((Path(snapshot["root"]) / "Poincare/Unrelated.lean").exists())

        ignored = worktree / "Poincare/Ignored.lean"
        ignored.write_text("theorem ignored : True := by trivial\n", encoding="utf-8")
        (worktree / ".gitignore").write_text("Poincare/Ignored.lean\n", encoding="utf-8")
        subprocess.run(
            (str(git), "-C", str(worktree), "add", ".gitignore"), check=True
        )
        subprocess.run(
            (str(git), "-C", str(worktree), "add", "-f", "Poincare/Ignored.lean"),
            check=True,
        )
        with self.assertRaisesRegex(SecurityError, "ignored"):
            build_sparse_lean_snapshot(
                worktree=worktree,
                acceptance_commands=(("lake", "env", "lean", "Poincare/Ignored.lean"),),
                output_dir=check_dir / "ignored-source",
                git_path=git,
            )

        linked = worktree / "Poincare/Linked.lean"
        linked.symlink_to("Target.lean")
        subprocess.run(
            (str(git), "-C", str(worktree), "add", "Poincare/Linked.lean"), check=True
        )
        with self.assertRaisesRegex(SecurityError, "symbolic link"):
            build_sparse_lean_snapshot(
                worktree=worktree,
                acceptance_commands=(("lake", "env", "lean", "Poincare/Linked.lean"),),
                output_dir=check_dir / "linked-source",
                git_path=git,
            )

        target = worktree / "Poincare/Target.lean"
        original_ismount = os.path.ismount
        with (
            patch.object(
                security.os.path,
                "ismount",
                side_effect=lambda path: Path(path) == target or original_ismount(path),
            ),
            self.assertRaisesRegex(SecurityError, "mountpoint"),
        ):
            build_sparse_lean_snapshot(
                worktree=worktree,
                acceptance_commands=(("lake", "env", "lean", "Poincare/Target.lean"),),
                output_dir=check_dir / "mount-source",
                git_path=git,
            )

        remove_sparse_lean_snapshot(sparse_snapshot=snapshot, checks_root=checks_root)
        self.assertFalse(Path(snapshot["root"]).exists())

    def test_sparse_profile_rehashes_cache_and_sets_cgroup_and_rlimits(self) -> None:
        worktree, git = self._git_worktree()
        checks_root = self.root / "lean-checks"
        check_dir = checks_root / "check-2"
        check_dir.mkdir(parents=True, mode=0o700)
        checks_root.chmod(0o700)
        snapshot = build_sparse_lean_snapshot(
            worktree=worktree,
            acceptance_commands=(("lake", "env", "lean", "Poincare/Target.lean"),),
            output_dir=check_dir / "source",
            git_path=git,
        )
        snapshot_root = Path(snapshot["root"])
        base_commit = "a" * 40
        base_tree = "b" * 40
        cache = self.root / "cache" / base_commit
        (cache / "packages/mathlib").mkdir(parents=True)
        (cache / "build").mkdir()
        (cache / "config").mkdir()
        overrides = cache / security.PACKAGE_OVERRIDES_NAME
        overrides.write_bytes(canonical_package_overrides(snapshot_root))
        overrides.chmod(0o444)
        _seal_tree(cache)
        tree_sha = lake_cache_tree_digest(cache)
        cache.chmod(0o755)
        manifest = cache / security.CACHE_MANIFEST_NAME
        manifest.write_text(
            json.dumps(
                {
                    "schema_version": security.CACHE_MANIFEST_VERSION,
                    "base_commit": base_commit,
                    "base_tree": base_tree,
                    "cache_tree_sha256": tree_sha,
                    "package_overrides_sha256": _sha256(overrides),
                    "lean_toolchain_sha256": _sha256(snapshot_root / "lean-toolchain"),
                    "lake_manifest_sha256": _sha256(snapshot_root / "lake-manifest.json"),
                }
            )
            + "\n",
            encoding="utf-8",
        )
        manifest.chmod(0o444)
        cache.chmod(0o555)

        bwrap = self._elf(self.root / "tools/bwrap")
        systemd_run = self._elf(self.root / "tools/systemd-run")
        toolchain = self.root / "toolchain"
        lake = self._elf(toolchain / "bin/lake")
        lean = self._elf(toolchain / "bin/lean")
        compiler_file = toolchain / "lib/lean/Init.olean"
        compiler_file.parent.mkdir(parents=True)
        compiler_file.write_bytes(b"compiled library")
        compiler_file.chmod(0o444)
        runtime_library = self.root / "tools/liblean-runtime.so"
        runtime_library.write_bytes(b"runtime library")
        runtime_library.chmod(0o444)
        runtime_mounts = [
            {
                "source": str(runtime_library),
                "destination": "/lib/liblean-runtime.so",
                "sha256": _sha256(runtime_library),
            }
        ]
        forbidden = []
        for name in ("control", "state", "artifacts"):
            path = self.root / name
            path.mkdir(mode=0o700)
            forbidden.append(path)
        forbidden.append(worktree)
        limits = ProcessResourceLimits(
            address_space_bytes=2 * 1024 * 1024 * 1024,
            processes=256,
            open_files=256,
            file_size_bytes=64 * 1024 * 1024,
            core_bytes=0,
            cpu_seconds=60,
        )
        with (
            patch.object(security.sys, "platform", "linux"),
            patch.object(
                security,
                "_runtime_library_mounts",
                return_value=(runtime_mounts, []),
            ),
        ):
            spec = audit_sparse_lean_bubblewrap(
                configured_path=str(bwrap),
                systemd_run_path=systemd_run,
                sparse_snapshot=snapshot,
                immutable_lake_cache=cache,
                extra_toolchain_roots=str(toolchain),
                forbidden_paths=forbidden,
                base_commit=base_commit,
                base_tree=base_tree,
                memory_max_bytes=1024 * 1024 * 1024,
                tasks_max=128,
                cpu_quota_percent=150,
                process_limits=limits,
            )
            argv = list(
                bubblewrap_sparse_lean_argv(
                    spec=spec,
                    command=("lake", "env", "lean", "Poincare/Target.lean"),
                )
            )
            self.assertEqual(sparse_lean_process_limits(spec), limits)
            self.assertEqual(argv[:4], [str(systemd_run), "--user", "--scope", "--quiet"])
            self.assertNotIn("--wait", argv)
            self.assertNotIn("--pipe", argv)
            for setting in (
                "--property=MemoryMax=1073741824",
                "--property=MemorySwapMax=0",
                "--property=TasksMax=128",
                "--property=CPUQuota=150%",
            ):
                self.assertIn(setting, argv)
            self.assertNotIn("--share-net", argv)
            self.assertNotIn(str(worktree), argv)
            self.assertNotIn(str(worktree / "Poincare/Unrelated.lean"), argv)
            self.assertIn(
                ["--ro-bind", str(snapshot_root), "/work"],
                [argv[index : index + 3] for index in range(len(argv) - 2)],
            )
            self.assertIn(
                ["--ro-bind", str(lake), "/opt/lean/bin/lake"],
                [argv[index : index + 3] for index in range(len(argv) - 2)],
            )
            self.assertNotIn(str(toolchain), argv)
            self.assertEqual(argv[-1], "/work/Poincare/Target.lean")

            build_dir = cache / "build"
            build_dir.chmod(0o755)
            drift = build_dir / "drift.olean"
            drift.write_bytes(b"drift")
            drift.chmod(0o444)
            build_dir.chmod(0o555)
            with self.assertRaisesRegex(SecurityError, "cache content changed"):
                bubblewrap_sparse_lean_argv(
                    spec=spec,
                    command=("lake", "env", "lean", "Poincare/Target.lean"),
                )
        remove_sparse_lean_snapshot(sparse_snapshot=snapshot, checks_root=checks_root)

    def test_process_limits_and_bounded_build_lock(self) -> None:
        limits = ProcessResourceLimits(
            address_space_bytes=2 * 1024 * 1024 * 1024,
            processes=512,
            open_files=128,
            file_size_bytes=1024 * 1024,
            core_bytes=0,
            cpu_seconds=30,
        )
        script = (
            "import json,resource; "
            "print(json.dumps([resource.getrlimit(resource.RLIMIT_AS)[0],"
            "resource.getrlimit(resource.RLIMIT_NPROC)[0],"
            "resource.getrlimit(resource.RLIMIT_NOFILE)[0],"
            "resource.getrlimit(resource.RLIMIT_FSIZE)[0],"
            "resource.getrlimit(resource.RLIMIT_CORE)[0],"
            "resource.getrlimit(resource.RLIMIT_CPU)[0]]))"
        )
        if sys.platform == "linux":
            result = run_limited(
                (sys.executable, "-c", script),
                cwd=self.root,
                env={"LANG": "C"},
                timeout_seconds=10,
                output_limit_bytes=4096,
                supervise_parent=True,
                resource_limits=limits,
            )
            self.assertEqual(result.returncode, 0, result.stderr.decode("utf-8", "replace"))
            self.assertEqual(json.loads(result.stdout), list(limits.as_dict().values()))

        state = self.root / "state"
        state.mkdir(mode=0o700)
        first = acquire_build_job_lock(state, timeout_seconds=0)
        try:
            with acquire_build_job_lock(state, timeout_seconds=0) as second_reader:
                publisher = os.open(second_reader.path, os.O_RDONLY)
                try:
                    with self.assertRaises(BlockingIOError):
                        fcntl.flock(publisher, fcntl.LOCK_EX | fcntl.LOCK_NB)
                finally:
                    os.close(publisher)
        finally:
            first.release()
        with acquire_build_job_lock(state, timeout_seconds=0) as second:
            self.assertEqual(second.path, state / "build-job.lock")
            self.assertEqual(second.path.stat().st_mode & 0o777, 0o600)
            self.assertEqual(second.path.stat().st_size, 0)


if __name__ == "__main__":
    unittest.main()
