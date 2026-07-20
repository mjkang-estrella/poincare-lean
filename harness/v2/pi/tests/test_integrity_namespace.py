from __future__ import annotations

import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest.mock import patch

from harness.v2.pi.integrity import (
    TRUSTED_CODE_PATHS,
    IntegrityError,
    _verify_loaded_origins,
    attest_trusted_code,
    verify_trusted_code,
)


EXPECTED_TRUSTED_CODE_PATHS = (
    "harness/__init__.py",
    "harness/v2/__init__.py",
    "harness/v2/pi/__init__.py",
    "harness/v2/pi/__main__.py",
    "harness/v2/pi/broker.py",
    "harness/v2/pi/cli.py",
    "harness/v2/pi/engine.py",
    "harness/v2/pi/extension.ts",
    "harness/v2/pi/install.py",
    "harness/v2/pi/integrity.py",
    "harness/v2/pi/journal.py",
    "harness/v2/pi/quota.py",
    "harness/v2/pi/rpc.py",
    "harness/v2/pi/security.py",
    "harness/v2/pi/snapshot.py",
    "harness/v2/runtime/__init__.py",
    "harness/v2/runtime/migrations.py",
    "harness/v2/runtime/store.py",
    "harness/v2/runtime/validation.py",
    "harness/v2/worker/__init__.py",
    "harness/v2/worker/artifacts.py",
    "harness/v2/worker/binding.py",
    "harness/v2/worker/client.py",
    "harness/v2/worker/secrets.py",
    "harness/v2/worker/snapshot.py",
)


def _run(
    *argv: str, cwd: Path, env: dict[str, str] | None = None
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        argv,
        cwd=cwd,
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
        text=True,
    )


class TrustedCodeFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.source_root = Path(__file__).resolve().parents[4]
        self.control = self.root / "control"
        self.control.mkdir()
        for relative in TRUSTED_CODE_PATHS:
            destination = self.control / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(self.source_root / relative, destination)
        _run("git", "init", "-b", "integrity-test", cwd=self.control)
        _run("git", "config", "user.name", "Harness Test", cwd=self.control)
        _run(
            "git",
            "config",
            "user.email",
            "harness@example.invalid",
            cwd=self.control,
        )
        _run("git", "add", ".", cwd=self.control)
        _run("git", "commit", "-m", "trusted closure", cwd=self.control)


class TrustedCodeManifestTest(TrustedCodeFixture):
    def test_manifest_is_the_exact_ordered_tracked_byte_closure(self) -> None:
        self.assertEqual(TRUSTED_CODE_PATHS, EXPECTED_TRUSTED_CODE_PATHS)
        manifest = attest_trusted_code(self.control, check_loaded_origins=False)
        self.assertEqual(
            [entry["path"] for entry in manifest["files"]],
            list(EXPECTED_TRUSTED_CODE_PATHS),
        )
        for entry in manifest["files"]:
            committed = subprocess.run(
                ["git", "show", f"HEAD:{entry['path']}"],
                cwd=self.control,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=True,
            ).stdout
            self.assertEqual(entry["size_bytes"], len(committed))
            self.assertEqual(entry["sha256"], hashlib.sha256(committed).hexdigest())

    def test_typescript_extension_has_only_the_sealed_rpc_boundary(self) -> None:
        extension = (self.source_root / "harness/v2/pi/extension.ts").read_text(
            encoding="utf-8"
        )
        self.assertNotIn("node:child_process", extension)
        self.assertNotIn("HARNESS_PI_CAPABILITY", extension)
        self.assertNotIn("HARNESS_PI_PYTHON", extension)
        self.assertIn('"/sealed/public-config.json"', extension)
        self.assertIn('"/sealed/system-prompt.md"', extension)
        self.assertIn('"HARNESS_PI_BROKER_SOCKET"', extension)
        self.assertIn('"HARNESS_PI_BROKER_TOKEN"', extension)

    def test_fresh_pi_entrypoint_imports_exactly_the_manifest_python_sources(self) -> None:
        script = (
            "import json, sys\n"
            "from pathlib import Path\n"
            "import harness.v2.pi.__main__\n"
            f"root = Path({str(self.control)!r}).resolve()\n"
            "loaded = set()\n"
            "for module in tuple(sys.modules.values()):\n"
            "    raw = getattr(module, '__file__', None)\n"
            "    if not isinstance(raw, str):\n"
            "        continue\n"
            "    path = Path(raw).resolve()\n"
            "    try:\n"
            "        relative = path.relative_to(root).as_posix()\n"
            "    except ValueError:\n"
            "        continue\n"
            "    if relative.startswith('harness/') and relative.endswith('.py'):\n"
            "        loaded.add(relative)\n"
            "print(json.dumps(sorted(loaded)))\n"
        )
        env = {
            "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
            "LANG": os.environ.get("LANG", "C.UTF-8"),
            "PYTHONPATH": str(self.control),
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
        result = _run(
            sys.executable,
            "-S",
            "-P",
            "-B",
            "-c",
            script,
            cwd=self.root,
            env=env,
        )
        self.assertEqual(
            json.loads(result.stdout),
            [
                relative
                for relative in EXPECTED_TRUSTED_CODE_PATHS
                if relative.endswith(".py")
            ],
        )

    def test_manifest_rejects_reordered_paths(self) -> None:
        manifest = attest_trusted_code(self.control, check_loaded_origins=False)
        reordered = copy.deepcopy(manifest)
        reordered["files"][0], reordered["files"][1] = (
            reordered["files"][1],
            reordered["files"][0],
        )
        with self.assertRaisesRegex(IntegrityError, "exact file closure"):
            verify_trusted_code(self.control, reordered)

    def test_manifest_rejects_worktree_bytes_hidden_from_status(self) -> None:
        relative = "harness/__init__.py"
        _run("git", "update-index", "--assume-unchanged", relative, cwd=self.control)
        trusted = self.control / relative
        trusted.write_bytes(trusted.read_bytes() + b"\n# hidden drift\n")
        self.assertEqual(
            _run("git", "status", "--porcelain=v1", cwd=self.control).stdout,
            "",
        )
        with self.assertRaisesRegex(IntegrityError, "differs from control checkout HEAD"):
            attest_trusted_code(self.control, check_loaded_origins=False)


class TrustedCodeOriginTest(TrustedCodeFixture):
    def test_trusted_harness_initializer_prevents_later_package_preemption(self) -> None:
        shadow = self.root / "later-shadow"
        shadow_harness = shadow / "harness"
        shadow_harness.mkdir(parents=True)
        harness_marker = self.root / "shadow-harness-executed"
        (shadow_harness / "__init__.py").write_text(
            f"open({str(harness_marker)!r}, 'w').write('executed')\n"
            f"__path__ = [{str(self.control / 'harness')!r}]\n",
            encoding="utf-8",
        )
        script = (
            "from pathlib import Path\n"
            "import harness\n"
            "from harness.v2.pi.integrity import attest_trusted_code\n"
            f"attest_trusted_code(Path({str(self.control)!r}))\n"
            "print(harness.__file__)\n"
        )
        env = {
            "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
            "LANG": os.environ.get("LANG", "C.UTF-8"),
            "PYTHONPATH": os.pathsep.join((str(self.control), str(shadow))),
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
        result = _run(
            sys.executable,
            "-S",
            "-P",
            "-B",
            "-c",
            script,
            cwd=self.root,
            env=env,
        )
        self.assertFalse(harness_marker.exists())
        self.assertEqual(
            result.stdout.splitlines(),
            [str(self.control / "harness/__init__.py")],
        )

    def test_trusted_v2_initializer_prevents_later_package_preemption(self) -> None:
        shadow_harness = self.root / "later-v2-shadow/harness"
        shadow_v2 = shadow_harness / "v2"
        shadow_v2.mkdir(parents=True)
        marker = self.root / "shadow-v2-executed"
        (shadow_v2 / "__init__.py").write_text(
            f"open({str(marker)!r}, 'w').write('executed')\n"
            f"__path__ = [{str(self.control / 'harness/v2')!r}]\n",
            encoding="utf-8",
        )
        script = (
            "import harness\n"
            "from pathlib import Path\n"
            f"harness.__path__[:] = [{str(self.control / 'harness')!r}, "
            f"{str(shadow_harness)!r}]\n"
            "import harness.v2.pi.integrity\n"
            "print(Path(harness.v2.__file__).resolve())\n"
        )
        env = {
            "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
            "LANG": os.environ.get("LANG", "C.UTF-8"),
            "PYTHONPATH": str(self.control),
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
        result = _run(
            sys.executable,
            "-S",
            "-P",
            "-B",
            "-c",
            script,
            cwd=self.root,
            env=env,
        )
        self.assertFalse(marker.exists())
        self.assertEqual(
            result.stdout.strip(),
            str(self.control / "harness/v2/__init__.py"),
        )

    def test_shadow_package_preemption_is_rejected_after_real_submodules_load(self) -> None:
        shadow = self.root / "shadow"
        shadow_package = shadow / "harness"
        shadow_package.mkdir(parents=True)
        (shadow_package / "__init__.py").write_text(
            f"__path__ = [{str(self.control / 'harness')!r}]\n",
            encoding="utf-8",
        )
        script = (
            "from pathlib import Path\n"
            "from harness.v2.pi.integrity import IntegrityError, attest_trusted_code\n"
            "try:\n"
            f"    attest_trusted_code(Path({str(self.control)!r}))\n"
            "except IntegrityError as exc:\n"
            "    print(exc)\n"
            "else:\n"
            "    raise SystemExit('shadow package was accepted')\n"
        )
        env = {
            "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
            "LANG": os.environ.get("LANG", "C.UTF-8"),
            "PYTHONPATH": os.pathsep.join((str(shadow), str(self.control))),
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
        result = _run(
            sys.executable,
            "-S",
            "-P",
            "-B",
            "-c",
            script,
            cwd=self.root,
            env=env,
        )
        self.assertRegex(result.stdout, "trusted module loaded outside.*harness")

    def test_v2_search_path_preemption_is_rejected(self) -> None:
        shadow_v2 = self.root / "shadow-v2"
        shadow_v2.mkdir()
        canonical = sys.modules["harness.v2"]
        preempted = types.ModuleType("harness.v2")
        preempted.__file__ = canonical.__file__
        preempted.__path__ = [str(shadow_v2), str(self.source_root / "harness/v2")]
        with patch.dict(sys.modules, {"harness.v2": preempted}):
            with self.assertRaisesRegex(
                IntegrityError,
                "namespace search path escaped.*harness.v2",
            ):
                _verify_loaded_origins(self.source_root)


if __name__ == "__main__":
    unittest.main()
