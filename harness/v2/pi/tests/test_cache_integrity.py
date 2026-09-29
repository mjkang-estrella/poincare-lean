from __future__ import annotations

import hashlib
import os
import stat
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import Mock, patch

from harness.v2.pi import cache_integrity, security
from harness.v2.pi.cache_integrity import (
    CacheProtectionError,
    ProtectedCacheAttestation,
    _parse_mountinfo,
    attest_protected_cache,
    revalidate_protected_cache,
)


class ProtectedCacheTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="cache-integrity-")
        self.root = Path(self.temporary.name).resolve()
        self.cache = self.root / ("a" * 40)
        self.cache.mkdir()
        self.olean = self.cache / "Target.olean"
        self.olean.write_bytes(b"olean-a")
        for name in (security.CACHE_MANIFEST_NAME, security.PACKAGE_OVERRIDES_NAME):
            (self.cache / name).write_bytes(b"sealed configuration")
        for child in self.cache.iterdir():
            child.chmod(0o444)
        self.cache.chmod(0o555)
        self.digest = security._cache_entries(self.cache, include_content=True)[0]
        self.spec = {
            "lake_cache": {
                "source": str(self.cache),
                "manifest_sha256": self._sha(self.cache / security.CACHE_MANIFEST_NAME),
                "package_overrides_sha256": self._sha(self.cache / security.PACKAGE_OVERRIDES_NAME),
                "tree_sha256": self.digest,
                "base_commit": "a" * 40,
                "base_tree": "b" * 40,
            },
            "toolchain": {"lean": {"sha256": "c" * 64}},
        }
        self.binding = security._sparse_cache_binding(self.spec)

    def tearDown(self) -> None:
        self.cache.chmod(0o755)
        for child in self.cache.iterdir():
            child.chmod(0o644)
        self.temporary.cleanup()

    @staticmethod
    def _sha(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def _receipt(self, generation: tuple[object, ...] = ("protected-mount",)) -> ProtectedCacheAttestation:
        with patch.object(cache_integrity, "_protection_generation", return_value=generation):
            return attest_protected_cache(
                root=self.cache, binding=self.binding, tree_sha256=self.digest,
                hash_content=lambda: security._cache_entries(self.cache, include_content=True)[0],
            )

    def test_default_rehash_detects_same_size_same_mtime_content_mutation(self) -> None:
        timings: dict[str, float] = {}
        with patch.object(security, "_cache_entries", wraps=security._cache_entries) as hashes:
            security._validate_sparse_cache(self.spec, cache_attestation=None, timings=timings)
            metadata = self.olean.stat()
            self.olean.chmod(0o644)
            self.olean.write_bytes(b"olean-b")
            self.olean.chmod(0o444)
            os.utime(self.olean, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
            with self.assertRaisesRegex(security.SecurityError, "cache content changed"):
                security._validate_sparse_cache(self.spec, cache_attestation=None, timings=timings)
            self.assertEqual(hashes.call_count, 2)
            self.assertTrue(all(call.kwargs["include_content"] for call in hashes.call_args_list))
        self.assertGreaterEqual(timings["cache_integrity_seconds"], 0)

    def test_chmod_tree_never_issues_a_protected_receipt(self) -> None:
        # A sealed same-user directory is not an immutability primitive.
        with self.assertRaises(CacheProtectionError):
            attest_protected_cache(
                root=self.cache, binding=self.binding, tree_sha256=self.digest,
                hash_content=lambda: self.digest,
            )

    def test_protected_receipt_hashes_once_then_rechecks_generation(self) -> None:
        full_hash = Mock(return_value=self.digest)
        with patch.object(cache_integrity, "_protection_generation", return_value=("mount-v1",)) as protection:
            receipt = attest_protected_cache(
                root=self.cache, binding=self.binding, tree_sha256=self.digest,
                hash_content=full_hash,
            )
            with patch.object(security, "_cache_entries", side_effect=AssertionError("unexpected full rehash")):
                security._validate_sparse_cache(self.spec, cache_attestation=receipt, timings={})
            self.assertEqual(full_hash.call_count, 1)
            self.assertEqual(protection.call_count, 3)

    def test_tampered_mount_generation_rejected_without_hash_fallback(self) -> None:
        receipt = self._receipt()
        with (
            patch.object(cache_integrity, "_protection_generation", return_value=("replacement-mount",)),
            patch.object(security, "_cache_entries", side_effect=AssertionError("must fail closed")),
            self.assertRaisesRegex(security.SecurityError, "generation changed"),
        ):
            security._validate_sparse_cache(self.spec, cache_attestation=receipt, timings=None)

    def test_manifest_mutation_rejected_even_with_receipt(self) -> None:
        receipt = self._receipt()
        manifest = self.cache / security.CACHE_MANIFEST_NAME
        manifest.chmod(0o644)
        manifest.write_bytes(b"changed configuration")
        manifest.chmod(0o444)
        with self.assertRaisesRegex(security.SecurityError, "manifest changed"):
            security._validate_sparse_cache(self.spec, cache_attestation=receipt, timings=None)

    def test_receipt_bound_to_base_compiler_and_content_digest(self) -> None:
        receipt = self._receipt()
        for field, value in (("base_tree", "d" * 40), ("base_commit", "e" * 40),
                             ("tree_sha256", "f" * 64)):
            spec = {**self.spec, "lake_cache": {**self.spec["lake_cache"], field: value}}
            with self.assertRaisesRegex(security.SecurityError, "binding changed"):
                security._validate_sparse_cache(spec, cache_attestation=receipt, timings=None)
        spec = {**self.spec, "toolchain": {"lean": {"sha256": "e" * 64}}}
        with self.assertRaisesRegex(security.SecurityError, "binding changed"):
            security._validate_sparse_cache(spec, cache_attestation=receipt, timings=None)

    def test_forged_receipt_and_rebound_path_rejected(self) -> None:
        receipt = self._receipt()
        with self.assertRaisesRegex(CacheProtectionError, "binding changed"):
            revalidate_protected_cache(
                attestation=replace(receipt, _issuer=object()), root=self.cache,
                binding=self.binding, tree_sha256=self.digest,
            )
        with self.assertRaisesRegex(CacheProtectionError, "binding changed"):
            revalidate_protected_cache(
                attestation=receipt, root=self.root, binding=self.binding,
                tree_sha256=self.digest,
            )

    def test_generation_change_while_first_hashing_rejected(self) -> None:
        with patch.object(cache_integrity, "_protection_generation", side_effect=[("old",), ("new",)]):
            with self.assertRaisesRegex(CacheProtectionError, "changed while hashing"):
                attest_protected_cache(root=self.cache, binding=self.binding,
                                       tree_sha256=self.digest, hash_content=lambda: self.digest)

    def _mount(self, *, point: Path | None = None, mount_id: int = 10,
               device: str | None = None, options: str = "ro", super_options: str = "ro") -> str:
        if device is None:
            dev = self.cache.stat().st_dev
            device = f"{os.major(dev)}:{os.minor(dev)}"
        return f"{mount_id} 1 {device} / {point or self.cache} {options} - ext4 /dev/test {super_options}\n"

    def _generation(self, raw: str) -> tuple[object, ...]:
        with (
            patch.object(cache_integrity, "_process_protection", return_value=("unprivileged",)),
            patch.object(cache_integrity, "_read_mountinfo", return_value=_parse_mountinfo(raw)),
            patch.object(cache_integrity, "_block_protection", return_value=("protected-physical-device",)),
            patch.object(cache_integrity, "_root_protected_path", return_value=("root-owned-parents",)),
        ):
            return cache_integrity._protection_generation(self.cache)

    def test_read_only_bind_over_writable_superblock_rejected(self) -> None:
        with self.assertRaisesRegex(CacheProtectionError, "read-only filesystem"):
            self._generation(self._mount(options="ro", super_options="rw"))

    def test_recursive_child_mounts_must_be_read_only(self) -> None:
        self.cache.chmod(0o755)
        child = self.cache / "child"
        child.mkdir(mode=0o555)
        self.cache.chmod(0o555)
        for changed in ("mount", "superblock"):
            raw = self._mount() + self._mount(
                point=child, mount_id=11,
                options="rw" if changed == "mount" else "ro",
                super_options="rw" if changed == "superblock" else "ro",
            )
            with self.assertRaisesRegex(CacheProtectionError, "read-only filesystem"):
                self._generation(raw)
        self.assertTrue(self._generation(self._mount() + self._mount(point=child, mount_id=11)))
        self.cache.chmod(0o755)
        child.rmdir()
        self.cache.chmod(0o555)

    def test_writable_alias_and_changed_mount_id_rejected(self) -> None:
        alias = self.root / "alias"
        alias.mkdir()
        with self.assertRaisesRegex(CacheProtectionError, "writable alias"):
            self._generation(self._mount() + self._mount(point=alias, mount_id=11, super_options="rw"))
        self.assertNotEqual(self._generation(self._mount(mount_id=10)),
                            self._generation(self._mount(mount_id=12)))

    def test_cache_inode_replacement_changes_protected_generation(self) -> None:
        before = self._generation(self._mount())
        moved = self.root / "old-cache"
        self.cache.rename(moved)
        self.cache.mkdir(mode=0o555)
        after = self._generation(self._mount())
        self.assertNotEqual(before, after)
        self.cache.rmdir()
        moved.rename(self.cache)

    def test_symlink_cache_path_rejected(self) -> None:
        link = self.root / "cache-link"
        link.symlink_to(self.cache, target_is_directory=True)
        with (
            patch.object(cache_integrity, "_process_protection", return_value=("unprivileged",)),
            self.assertRaisesRegex(CacheProtectionError, "canonical absolute"),
        ):
            cache_integrity._protection_generation(link)

    def test_unsupported_filesystem_and_ambiguous_stacked_mount_rejected(self) -> None:
        with self.assertRaisesRegex(CacheProtectionError, "supported protection"):
            self._generation(self._mount().replace(" ext4 ", " overlay "))
        with self.assertRaisesRegex(CacheProtectionError, "stacked cache mounts"):
            self._generation(self._mount() + self._mount(mount_id=11))

    def test_process_protection_rejects_root_and_capabilities(self) -> None:
        with (
            patch.object(cache_integrity.sys, "platform", "linux"),
            patch.object(cache_integrity.os, "geteuid", return_value=0),
            self.assertRaisesRegex(CacheProtectionError, "unprivileged"),
        ):
            cache_integrity._process_protection()
        status = "CapInh:\t0\nCapPrm:\t200000\nCapEff:\t0\nCapAmb:\t0\n"
        with (
            patch.object(cache_integrity.sys, "platform", "linux"),
            patch.object(cache_integrity.os, "geteuid", return_value=1000),
            patch.object(cache_integrity.os, "getuid", return_value=1000),
            patch.object(Path, "read_text", return_value=status),
            self.assertRaisesRegex(CacheProtectionError, "no capabilities"),
        ):
            cache_integrity._process_protection()

    def test_mountinfo_parser_accepts_escapes_and_rejects_ambiguous_input(self) -> None:
        records = _parse_mountinfo("10 1 8:1 / /cache\\040dir ro shared:2 - ext4 /dev/sda1 ro\n")
        self.assertEqual(records[0].point, "/cache dir")
        for raw in ("bad table", "10 1 8:1 / /cache\\777 ro - ext4 /dev/sda1 ro",
                    "10 1 8:1 / /cache ro - ext4 /dev/sda1 ro\n" * 2):
            with self.assertRaises(CacheProtectionError):
                _parse_mountinfo(raw)


class LeanServerCapabilityTest(unittest.TestCase):
    def setUp(self) -> None:
        self.spec = {
            "bwrap": {"source": "/usr/bin/bwrap"},
            "systemd_run": {"source": "/usr/bin/systemd-run"},
            "snapshot": {"root": "/sealed/sparse", "targets": ["Poincare/Target.lean"]},
            "lake_cache": {"source": "/sealed/cache"},
            "runtime_mounts": [],
            "toolchain": {
                "lake": {"source": "/sealed/toolchain/lake", "destination": "/opt/lean/bin/lake"},
                "lean": {"source": "/sealed/toolchain/lean", "destination": "/opt/lean/bin/lean"},
                "compiler_lib": {"source": "/sealed/toolchain/lib", "destination": "/opt/lean/lib/lean"},
            },
            "resources": {"memory_max_bytes": 1024, "memory_swap_max_bytes": 0,
                          "tasks_max": 2, "cpu_quota_percent": 50,
                          "rlimits": {"address_space_bytes": 1024, "processes": 2,
                                      "open_files": 8, "file_size_bytes": 1024,
                                      "core_bytes": 0, "cpu_seconds": 1}},
        }

    def test_server_launch_preserves_all_mount_network_and_resource_boundaries(self) -> None:
        timings: dict[str, float] = {}
        with (
            patch.object(security, "_validate_sparse_lean_bwrap_spec", return_value=self.spec),
            patch.object(security, "validate_sparse_lean_session", return_value=self.spec) as validate,
        ):
            focused = security.bubblewrap_sparse_lean_argv(
                spec=self.spec, command=("lake", "env", "lean", "Poincare/Target.lean"),
            )
            server = security.bubblewrap_sparse_lean_server_argv(
                spec=self.spec, command=("lake", "env", "lean", "Poincare/Target.lean"),
                timings=timings,
            )
            self.assertEqual(validate.call_count, 2)
            self.assertIs(validate.call_args.kwargs["timings"], timings)
        self.assertEqual(server[:-1], focused[:-1])
        self.assertEqual(server[-1], "--server")
        self.assertEqual(server[-5:-1], ("/opt/lean/bin/lake", "--packages=/work/.lake/.harness-package-overrides.json",
                                          "env", "/opt/lean/bin/lean"))
        self.assertIn("--unshare-all", server)
        self.assertNotIn("--share-net", server)
        self.assertIn("--property=MemoryMax=1024", server)
        self.assertIn("--property=CPUQuota=50%", server)
        self.assertNotIn("--bind", server)

    def test_server_rejects_nonrecorded_target_and_additional_arguments(self) -> None:
        with patch.object(security, "_validate_sparse_lean_bwrap_spec", return_value=self.spec):
            for command in (("lake", "env", "lean", "Poincare/Other.lean"),
                            ("lake", "env", "lean", "Poincare/Target.lean", "--server"),
                            ("lake", "env", "lean", "--server")):
                with self.assertRaises(security.SecurityError):
                    security.bubblewrap_sparse_lean_server_argv(spec=self.spec, command=command)


if __name__ == "__main__":
    unittest.main()
