from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from harness.v2.pi.install import (
    MANIFEST_SCHEMA,
    PI_MINIMUM_NODE_VERSION,
    PI_NODE_ENGINE,
    PI_PACKAGE_NAME,
    PI_PACKAGE_VERSION,
    PiInstallError,
    build_install_manifest,
    canonical_manifest_bytes,
    install_manifest_sha256,
    probe_node_version,
    verify_install_manifest,
    verify_sealed_install_files,
)


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


class _Fixture:
    def __init__(self, parent: Path) -> None:
        self.root = (parent / "install").resolve()
        self.node = (parent / "node-real").resolve()
        self.package = self.root / "node_modules/@earendil-works/pi-coding-agent"
        self.cli = self.package / "dist/cli.js"
        self.node_version = "22.22.1"
        self.graph = {
            "name": "poincare-harness-pi-extension",
            "dependencies": {
                PI_PACKAGE_NAME: {
                    "version": PI_PACKAGE_VERSION,
                    "dependencies": {"typebox": {"version": "1.1.38"}},
                }
            },
        }

        self.node.write_bytes(b"#!/bin/sh\nprintf 'v22.22.1\\n'\n")
        self.node.chmod(0o755)
        (self.package / "dist").mkdir(parents=True)
        (self.root / "node_modules/.bin").mkdir(parents=True)
        self.cli.write_bytes(b"#!/usr/bin/env node\nconsole.log('pi');\n")
        self.cli.chmod(0o755)
        (self.package / "alternate.js").write_bytes(b"alternate\n")
        (self.root / "node_modules/.bin/pi").symlink_to(
            "../@earendil-works/pi-coding-agent/dist/cli.js"
        )

        root_package = {
            "name": "poincare-harness-pi-extension",
            "private": True,
            "dependencies": {
                PI_PACKAGE_NAME: PI_PACKAGE_VERSION,
                "typebox": "1.1.38",
            },
        }
        installed_package = {
            "name": PI_PACKAGE_NAME,
            "version": PI_PACKAGE_VERSION,
            "bin": {"pi": "dist/cli.js"},
            "engines": {"node": PI_NODE_ENGINE},
        }
        lock = {
            "name": "poincare-harness-pi-extension",
            "lockfileVersion": 3,
            "requires": True,
            "packages": {
                "": {
                    "name": "poincare-harness-pi-extension",
                    "dependencies": {
                        PI_PACKAGE_NAME: PI_PACKAGE_VERSION,
                        "typebox": "1.1.38",
                    },
                },
                f"node_modules/{PI_PACKAGE_NAME}": {
                    "version": PI_PACKAGE_VERSION,
                    "bin": {"pi": "dist/cli.js"},
                    "engines": {"node": PI_NODE_ENGINE},
                },
            },
        }
        (self.root / "package.json").write_bytes(_json_bytes(root_package))
        (self.package / "package.json").write_bytes(_json_bytes(installed_package))
        self.lock_bytes = _json_bytes(lock)
        (self.root / "package-lock.json").write_bytes(self.lock_bytes)
        self.lock_sha256 = hashlib.sha256(self.lock_bytes).hexdigest()

    def attest(
        self, *, graph: object | None = None, node_version: str | None = None
    ) -> dict[str, object]:
        return build_install_manifest(
            node_executable=self.node,
            node_version=node_version or self.node_version,
            install_root=self.root,
            cli_js_path=self.cli,
            npm_dependency_graph=self.graph if graph is None else graph,
            expected_package_lock_sha256=self.lock_sha256,
        )

    def verify(self, manifest: dict[str, object], *, graph: object | None = None) -> None:
        verify_install_manifest(
            manifest,
            node_executable=self.node,
            install_root=self.root,
            cli_js_path=self.cli,
            npm_dependency_graph=self.graph if graph is None else graph,
            expected_package_lock_sha256=self.lock_sha256,
        )

    def seal_install(self) -> None:
        for directory, _, files in os.walk(self.root, topdown=False):
            base = Path(directory)
            for name in files:
                path = base / name
                if path.is_symlink():
                    continue
                executable = bool(stat.S_IMODE(path.stat().st_mode) & 0o111)
                path.chmod(0o555 if executable else 0o444)
            base.chmod(0o555)


class PiInstallAttestationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.parent = Path(self.temporary.name).resolve()
        self.fixture = _Fixture(self.parent)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_manifest_is_deterministic_complete_and_sealable(self) -> None:
        first = self.fixture.attest()
        second = self.fixture.attest(graph=json.dumps(self.fixture.graph, indent=2))
        self.assertEqual(first, second)
        self.assertEqual(first["schema_version"], MANIFEST_SCHEMA)
        self.assertEqual(
            first["package"],
            {
                "name": PI_PACKAGE_NAME,
                "node_engine": PI_NODE_ENGINE,
                "version": PI_PACKAGE_VERSION,
            },
        )
        self.assertEqual(first["package_lock_sha256"], self.fixture.lock_sha256)
        self.assertEqual(first["cli_js"]["path"], str(self.fixture.cli))
        self.assertEqual(
            first["node"],
            {
                "minimum_version": PI_MINIMUM_NODE_VERSION,
                "mode": stat.S_IMODE(self.fixture.node.stat().st_mode),
                "path": str(self.fixture.node),
                "sha256": hashlib.sha256(self.fixture.node.read_bytes()).hexdigest(),
                "size_bytes": self.fixture.node.stat().st_size,
                "version": self.fixture.node_version,
            },
        )
        paths = [entry["path"] for entry in first["tree"]["entries"]]
        self.assertEqual(paths, sorted(paths, key=lambda value: value.encode("utf-8")))
        self.assertIn("node_modules/.bin/pi", paths)
        self.assertEqual(first["tree"]["entry_count"], len(paths))
        canonical = canonical_manifest_bytes(first)
        self.assertNotIn(b" ", canonical)
        self.assertEqual(install_manifest_sha256(first), hashlib.sha256(canonical).hexdigest())
        self.fixture.verify(json.loads(canonical))

    def test_public_sealed_file_verifier_rechecks_the_complete_distribution(self) -> None:
        self.fixture.seal_install()
        manifest = self.fixture.attest()
        manifest_path = self.parent / "pi-install-manifest.json"
        graph_path = self.parent / "pi-dependency-graph.json"
        manifest_path.write_bytes(canonical_manifest_bytes(manifest))
        graph_path.write_bytes(
            json.dumps(
                self.fixture.graph,
                ensure_ascii=False,
                allow_nan=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        )
        manifest_path.chmod(0o400)
        graph_path.chmod(0o400)
        verified = verify_sealed_install_files(
            manifest_path,
            graph_path,
            expected_node_executable=self.fixture.node,
            expected_package_lock_sha256=self.fixture.lock_sha256,
        )
        self.assertEqual(verified, manifest)
        with self.assertRaisesRegex(PiInstallError, "unexpected Node executable"):
            verify_sealed_install_files(
                manifest_path,
                graph_path,
                expected_node_executable=self.parent / "another-node",
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )
        graph_path.chmod(0o600)
        with self.assertRaisesRegex(PiInstallError, "sealed"):
            verify_sealed_install_files(
                manifest_path,
                graph_path,
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )
        graph_path.chmod(0o400)
        (self.fixture.package / "alternate.js").chmod(0o644)
        with self.assertRaisesRegex(PiInstallError, "drifted"):
            verify_sealed_install_files(
                manifest_path,
                graph_path,
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )

    def test_sealed_verifier_rejects_every_install_write_bit(self) -> None:
        targets = {
            "root": lambda fixture: fixture.root,
            "directory": lambda fixture: fixture.package / "dist",
            "file": lambda fixture: fixture.package / "alternate.js",
        }
        for label, select in targets.items():
            for write_bit in (stat.S_IWUSR, stat.S_IWGRP, stat.S_IWOTH):
                with self.subTest(target=label, write_bit=oct(write_bit)):
                    with tempfile.TemporaryDirectory() as temporary:
                        parent = Path(temporary).resolve()
                        fixture = _Fixture(parent)
                        fixture.seal_install()
                        target = select(fixture)
                        target.chmod(stat.S_IMODE(target.stat().st_mode) | write_bit)
                        manifest = fixture.attest()
                        manifest_path = parent / "pi-install-manifest.json"
                        graph_path = parent / "pi-dependency-graph.json"
                        manifest_path.write_bytes(canonical_manifest_bytes(manifest))
                        graph_path.write_bytes(
                            json.dumps(
                                fixture.graph,
                                ensure_ascii=False,
                                allow_nan=False,
                                sort_keys=True,
                                separators=(",", ":"),
                            ).encode("utf-8")
                        )
                        manifest_path.chmod(0o400)
                        graph_path.chmod(0o400)
                        with self.assertRaisesRegex(PiInstallError, "writable mode bit"):
                            verify_sealed_install_files(
                                manifest_path,
                                graph_path,
                                expected_package_lock_sha256=fixture.lock_sha256,
                            )

    def test_verifier_rejects_content_add_delete_and_mode_drift(self) -> None:
        mutations = (
            lambda fixture: fixture.cli.write_bytes(b"changed but sealed?\n"),
            lambda fixture: (fixture.root / "added.txt").write_text("new", encoding="utf-8"),
            lambda fixture: (fixture.package / "alternate.js").unlink(),
            lambda fixture: fixture.cli.chmod(0o700),
            lambda fixture: fixture.node.write_bytes(b"#!/bin/sh\nexit 7\n"),
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                with tempfile.TemporaryDirectory() as temporary:
                    fixture = _Fixture(Path(temporary).resolve())
                    manifest = fixture.attest()
                    mutation(fixture)
                    with self.assertRaises(PiInstallError):
                        fixture.verify(manifest)

    def test_verifier_rejects_symlink_target_or_type_drift(self) -> None:
        link = self.fixture.root / "node_modules/.bin/pi"
        manifest = self.fixture.attest()
        link.unlink()
        link.symlink_to("../@earendil-works/pi-coding-agent/alternate.js")
        with self.assertRaises(PiInstallError):
            self.fixture.verify(manifest)

        link.unlink()
        link.write_text("not a link", encoding="utf-8")
        with self.assertRaises(PiInstallError):
            self.fixture.verify(manifest)

    def test_rejects_absolute_escaping_dangling_and_cyclic_symlinks(self) -> None:
        link = self.fixture.root / "node_modules/.bin/pi"
        bad_targets = (
            "/etc/passwd",
            "../../../../outside",
            "../@earendil-works/pi-coding-agent/missing.js",
            "pi",
        )
        for target in bad_targets:
            with self.subTest(target=target):
                link.unlink()
                link.symlink_to(target)
                with self.assertRaises(PiInstallError):
                    self.fixture.attest()

    def test_rejects_special_file_in_install(self) -> None:
        if not hasattr(os, "mkfifo"):
            self.skipTest("FIFO creation is unavailable")
        os.mkfifo(self.fixture.root / "forbidden.fifo")
        with self.assertRaises(PiInstallError):
            self.fixture.attest()

    def test_requires_absolute_real_node_root_and_cli_paths(self) -> None:
        with self.assertRaisesRegex(PiInstallError, "absolute"):
            build_install_manifest(
                node_executable="node",
                node_version=self.fixture.node_version,
                install_root=self.fixture.root,
                cli_js_path=self.fixture.cli,
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )

        node_link = self.parent / "node-link"
        node_link.symlink_to(self.fixture.node)
        with self.assertRaises(PiInstallError):
            build_install_manifest(
                node_executable=node_link,
                node_version=self.fixture.node_version,
                install_root=self.fixture.root,
                cli_js_path=self.fixture.cli,
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )

        root_link = self.parent / "install-link"
        root_link.symlink_to(self.fixture.root, target_is_directory=True)
        with self.assertRaises(PiInstallError):
            build_install_manifest(
                node_executable=self.fixture.node,
                node_version=self.fixture.node_version,
                install_root=root_link,
                cli_js_path=root_link / self.fixture.cli.relative_to(self.fixture.root),
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )

        with self.assertRaisesRegex(PiInstallError, "contained"):
            build_install_manifest(
                node_executable=self.fixture.node,
                node_version=self.fixture.node_version,
                install_root=self.fixture.root,
                cli_js_path=self.fixture.node,
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )

    def test_requires_exact_lock_package_identity_and_resolved_cli(self) -> None:
        with self.assertRaisesRegex(PiInstallError, "trusted pin"):
            build_install_manifest(
                node_executable=self.fixture.node,
                node_version=self.fixture.node_version,
                install_root=self.fixture.root,
                cli_js_path=self.fixture.cli,
                expected_package_lock_sha256="0" * 64,
            )

        installed_path = self.fixture.package / "package.json"
        installed = json.loads(installed_path.read_text())
        installed["version"] = "0.80.11"
        installed_path.write_bytes(_json_bytes(installed))
        with self.assertRaisesRegex(PiInstallError, "name or version"):
            self.fixture.attest()

        installed["version"] = PI_PACKAGE_VERSION
        installed_path.write_bytes(_json_bytes(installed))
        with self.assertRaisesRegex(PiInstallError, "does not match"):
            build_install_manifest(
                node_executable=self.fixture.node,
                node_version=self.fixture.node_version,
                install_root=self.fixture.root,
                cli_js_path=self.fixture.package / "alternate.js",
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )

    def test_rejects_incompatible_or_mismatched_exact_node_runtime(self) -> None:
        with self.assertRaisesRegex(PiInstallError, "requires Node >=22.19.0"):
            self.fixture.attest(node_version="22.18.0")

        self.fixture.node.write_bytes(b"#!/bin/sh\nprintf 'v22.18.0\\n'\n")
        self.fixture.node.chmod(0o755)
        manifest = self.fixture.attest(node_version=self.fixture.node_version)
        with self.assertRaisesRegex(PiInstallError, "requires Node >=22.19.0"):
            self.fixture.verify(manifest)

    def test_node_probe_uses_only_the_exact_absolute_attested_executable(self) -> None:
        completed = subprocess.CompletedProcess(
            args=(str(self.fixture.node), "--version"),
            returncode=0,
            stdout=b"v22.22.1\n",
            stderr=b"",
        )
        with patch(
            "harness.v2.pi.install.subprocess.run", return_value=completed
        ) as run:
            self.assertEqual(probe_node_version(self.fixture.node), "22.22.1")
        args, kwargs = run.call_args
        self.assertEqual(args, ((str(self.fixture.node), "--version"),))
        self.assertEqual(kwargs["env"], {"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"})
        self.assertNotIn("shell", kwargs)

    def test_dependency_graph_is_canonical_and_reverified(self) -> None:
        manifest = self.fixture.attest()
        graph_bytes = json.dumps(self.fixture.graph, indent=4).encode()
        verify_install_manifest(
            manifest,
            node_executable=self.fixture.node,
            install_root=self.fixture.root,
            cli_js_path=self.fixture.cli,
            npm_dependency_graph=graph_bytes,
            expected_package_lock_sha256=self.fixture.lock_sha256,
        )
        changed = json.loads(json.dumps(self.fixture.graph))
        changed["dependencies"][PI_PACKAGE_NAME]["dependencies"]["typebox"]["version"] = "9"
        with self.assertRaisesRegex(PiInstallError, "drifted"):
            self.fixture.verify(manifest, graph=changed)
        with self.assertRaises(PiInstallError):
            verify_install_manifest(
                manifest,
                node_executable=self.fixture.node,
                install_root=self.fixture.root,
                cli_js_path=self.fixture.cli,
                npm_dependency_graph=None,
                expected_package_lock_sha256=self.fixture.lock_sha256,
            )

    def test_manifest_tampering_and_extra_fields_are_rejected(self) -> None:
        manifest = self.fixture.attest()
        manifest["tree"]["entries"][0]["mode"] ^= stat.S_IXUSR
        with self.assertRaisesRegex(PiInstallError, "drifted"):
            self.fixture.verify(manifest)
        manifest = self.fixture.attest()
        manifest["unsealed_override"] = True
        with self.assertRaisesRegex(PiInstallError, "drifted"):
            self.fixture.verify(manifest)


if __name__ == "__main__":
    unittest.main()
