"""Trusted-code attestation for the live Pi capability boundary.

The TypeScript extension independently verifies the same manifest before it
spawns the Python broker.  The Python checks here additionally require a clean
Git checkout and, at engine launch, verify that already-imported Harness
modules came from that checkout.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import Any


class IntegrityError(RuntimeError):
    """Raised when executable Harness code is dirty, redirected, or changed."""


TRUSTED_CODE_PATHS = (
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

_MANIFEST_SCHEMA = "poincare.pi-trusted-code.v1"
_AGGREGATE_DOMAIN = b"poincare-harness-v2-trusted-code-v1\0"

_MODULE_PATHS = {
    "harness": "harness/__init__.py",
    "harness.v2": "harness/v2/__init__.py",
    "harness.v2.pi": "harness/v2/pi/__init__.py",
    "harness.v2.pi.__main__": "harness/v2/pi/__main__.py",
    "harness.v2.pi.broker": "harness/v2/pi/broker.py",
    "harness.v2.pi.cli": "harness/v2/pi/cli.py",
    "harness.v2.pi.engine": "harness/v2/pi/engine.py",
    "harness.v2.pi.install": "harness/v2/pi/install.py",
    "harness.v2.pi.integrity": "harness/v2/pi/integrity.py",
    "harness.v2.pi.journal": "harness/v2/pi/journal.py",
    "harness.v2.pi.quota": "harness/v2/pi/quota.py",
    "harness.v2.pi.rpc": "harness/v2/pi/rpc.py",
    "harness.v2.pi.security": "harness/v2/pi/security.py",
    "harness.v2.pi.snapshot": "harness/v2/pi/snapshot.py",
    "harness.v2.runtime": "harness/v2/runtime/__init__.py",
    "harness.v2.runtime.migrations": "harness/v2/runtime/migrations.py",
    "harness.v2.runtime.store": "harness/v2/runtime/store.py",
    "harness.v2.runtime.validation": "harness/v2/runtime/validation.py",
    "harness.v2.worker": "harness/v2/worker/__init__.py",
    "harness.v2.worker.artifacts": "harness/v2/worker/artifacts.py",
    "harness.v2.worker.binding": "harness/v2/worker/binding.py",
    "harness.v2.worker.client": "harness/v2/worker/client.py",
    "harness.v2.worker.secrets": "harness/v2/worker/secrets.py",
    "harness.v2.worker.snapshot": "harness/v2/worker/snapshot.py",
}

if tuple(sorted(set(TRUSTED_CODE_PATHS))) != TRUSTED_CODE_PATHS:
    raise RuntimeError("trusted-code closure must be unique and sorted")
if tuple(sorted((*_MODULE_PATHS.values(), "harness/v2/pi/extension.ts"))) != TRUSTED_CODE_PATHS:
    raise RuntimeError("trusted-code module-origin map does not match its exact closure")


def _read_regular_file(path: Path, relative: str) -> bytes:
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise IntegrityError(f"cannot open trusted code safely: {relative}") from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise IntegrityError(f"trusted code is not a regular file: {relative}")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
        if total != metadata.st_size:
            raise IntegrityError(f"trusted code changed while being read: {relative}")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _git(control_root: Path, *arguments: str) -> bytes:
    env = {
        "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
        "HOME": os.environ.get("HOME", str(control_root)),
        "LANG": os.environ.get("LANG", "C.UTF-8"),
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_PAGER": "cat",
        "PAGER": "cat",
        "GIT_EXTERNAL_DIFF": "",
    }
    try:
        result = subprocess.run(
            (
                "git",
                "-c",
                "core.fsmonitor=false",
                "-c",
                f"core.hooksPath={os.devnull}",
                "-c",
                "diff.external=",
                *arguments,
            ),
            cwd=control_root,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=20,
            check=False,
            shell=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise IntegrityError(f"trusted-code Git audit failed: {exc}") from exc
    if result.returncode != 0:
        error = result.stderr.decode("utf-8", "replace").strip()
        raise IntegrityError(f"trusted-code Git audit failed: {error or result.returncode}")
    return result.stdout


def _clean_commit(control_root: Path) -> str:
    top = Path(_git(control_root, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    if top != control_root:
        raise IntegrityError("control root is not the top of its Git checkout")
    commit = _git(control_root, "rev-parse", "HEAD").decode().strip()
    if re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        raise IntegrityError("control checkout HEAD is not a full commit ID")
    status = _git(
        control_root,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--",
        ".",
        ":(exclude)harness/v2/state",
        ":(exclude)harness/v2/state/**",
    )
    if status:
        raise IntegrityError(
            "control checkout is dirty outside excluded Harness runtime state"
        )
    return commit


def _verify_tracked_closure(control_root: Path, commit: str) -> None:
    raw = _git(
        control_root,
        "ls-tree",
        "-r",
        "-z",
        "--full-tree",
        commit,
        "--",
        *TRUSTED_CODE_PATHS,
    )
    records = raw.split(b"\0")
    if not records or records[-1] != b"":
        raise IntegrityError("trusted-code Git tree returned an invalid record stream")

    tracked: list[str] = []
    for record in records[:-1]:
        try:
            metadata, encoded_path = record.split(b"\t", 1)
            mode, kind, _object_id = metadata.split(b" ", 2)
            relative = encoded_path.decode("utf-8", "strict")
        except (UnicodeDecodeError, ValueError) as exc:
            raise IntegrityError("trusted-code Git tree returned an invalid record") from exc
        if kind != b"blob" or mode not in {b"100644", b"100755"}:
            raise IntegrityError(f"trusted code is not a tracked regular file: {relative}")
        tracked.append(relative)

    if tuple(tracked) != TRUSTED_CODE_PATHS:
        raise IntegrityError(
            "trusted-code Git tree does not contain the exact ordered file closure"
        )


def _manifest(control_root: Path, commit: str) -> tuple[list[dict[str, Any]], str]:
    _verify_tracked_closure(control_root, commit)
    entries: list[dict[str, Any]] = []
    aggregate = hashlib.sha256()
    aggregate.update(_AGGREGATE_DOMAIN)
    for relative in TRUSTED_CODE_PATHS:
        parsed = PurePosixPath(relative)
        candidate = control_root / Path(*parsed.parts)
        if candidate.is_symlink() or not candidate.is_file():
            raise IntegrityError(f"trusted code is missing or redirected: {relative}")
        resolved = candidate.resolve(strict=True)
        if resolved != candidate.absolute():
            raise IntegrityError(f"trusted code has a redirected ancestor: {relative}")
        try:
            resolved.relative_to(control_root)
        except ValueError as exc:
            raise IntegrityError(f"trusted code escaped the control checkout: {relative}") from exc
        data = _read_regular_file(resolved, relative)
        committed = _git(control_root, "show", f"{commit}:{relative}")
        if data != committed:
            raise IntegrityError(f"trusted code differs from control checkout HEAD: {relative}")
        size = len(data)
        digest = hashlib.sha256(data).hexdigest()
        entries.append({"path": relative, "sha256": digest, "size_bytes": size})
        aggregate.update(relative.encode("utf-8"))
        aggregate.update(b"\0")
        aggregate.update(digest.encode("ascii"))
        aggregate.update(b"\0")
        aggregate.update(str(size).encode("ascii"))
        aggregate.update(b"\n")
    return entries, aggregate.hexdigest()


def _verify_loaded_origins(control_root: Path) -> None:
    namespace_expectations = {
        "harness": control_root / "harness",
        "harness.v2": control_root / "harness/v2",
    }
    for module_name, expected_path in namespace_expectations.items():
        module = sys.modules.get(module_name)
        search_path = getattr(module, "__path__", None) if module is not None else None
        if search_path is None:
            raise IntegrityError(f"trusted namespace is not loaded: {module_name}")
        try:
            entries = [Path(entry).resolve(strict=True) for entry in search_path]
        except (OSError, TypeError) as exc:
            raise IntegrityError(
                f"trusted namespace search path is invalid: {module_name}"
            ) from exc
        if entries != [expected_path]:
            raise IntegrityError(
                f"trusted namespace search path escaped the control checkout: {module_name}"
            )

    for module_name, relative in _MODULE_PATHS.items():
        module = sys.modules.get(module_name)
        if module is None:
            continue
        raw = getattr(module, "__file__", None)
        if not isinstance(raw, str):
            raise IntegrityError(f"trusted module has no filesystem origin: {module_name}")
        loaded = Path(raw).resolve(strict=True)
        if loaded.suffix == ".pyc" and loaded.parent.name == "__pycache__":
            loaded = loaded.parent.parent / f"{loaded.name.split('.')[0]}.py"
            loaded = loaded.resolve(strict=True)
        expected = (control_root / Path(*PurePosixPath(relative).parts)).resolve(strict=True)
        if loaded != expected:
            raise IntegrityError(f"trusted module loaded outside control checkout: {module_name}")

    trusted = set(TRUSTED_CODE_PATHS)
    source_root = control_root / "harness"
    for module_name, module in tuple(sys.modules.items()):
        raw = getattr(module, "__file__", None)
        if not isinstance(raw, str):
            continue
        loaded = Path(raw).resolve(strict=True)
        if loaded.suffix == ".pyc" and loaded.parent.name == "__pycache__":
            loaded = loaded.parent.parent / f"{loaded.name.split('.')[0]}.py"
            loaded = loaded.resolve(strict=True)
        try:
            loaded.relative_to(source_root)
            relative = loaded.relative_to(control_root).as_posix()
        except ValueError:
            continue
        if relative not in trusted:
            raise IntegrityError(
                f"loaded Harness module is outside the exact trusted closure: {module_name}"
            )


def attest_trusted_code(
    control_root: Path, *, check_loaded_origins: bool = True
) -> dict[str, Any]:
    lexical = control_root.expanduser().absolute()
    if lexical.is_symlink():
        raise IntegrityError("control root must not be a symbolic link")
    try:
        control = lexical.resolve(strict=True)
    except OSError as exc:
        raise IntegrityError(f"cannot resolve control root: {exc}") from exc
    if not control.is_dir():
        raise IntegrityError("control root must be a directory")
    commit = _clean_commit(control)
    entries, aggregate = _manifest(control, commit)
    if _clean_commit(control) != commit:
        raise IntegrityError("control checkout HEAD changed during trusted-code attestation")
    if check_loaded_origins:
        _verify_loaded_origins(control)
    return {
        "schema_version": _MANIFEST_SCHEMA,
        "git_commit": commit,
        "aggregate_sha256": aggregate,
        "files": entries,
    }


def verify_trusted_code(control_root: Path, expected: Any) -> None:
    if not isinstance(expected, dict) or set(expected) != {
        "schema_version",
        "git_commit",
        "aggregate_sha256",
        "files",
    }:
        raise IntegrityError("trusted-code capability has an invalid shape")
    if expected.get("schema_version") != _MANIFEST_SCHEMA:
        raise IntegrityError("trusted-code capability has an invalid schema")
    if re.fullmatch(r"[0-9a-f]{40}", str(expected.get("git_commit", ""))) is None:
        raise IntegrityError("trusted-code capability has an invalid commit")
    if re.fullmatch(r"[0-9a-f]{64}", str(expected.get("aggregate_sha256", ""))) is None:
        raise IntegrityError("trusted-code capability has an invalid aggregate")
    files = expected.get("files")
    if not isinstance(files, list) or len(files) != len(TRUSTED_CODE_PATHS):
        raise IntegrityError("trusted-code capability has an invalid file closure")
    for relative, entry in zip(TRUSTED_CODE_PATHS, files, strict=True):
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256", "size_bytes"}:
            raise IntegrityError("trusted-code capability has an invalid file entry")
        if entry.get("path") != relative:
            raise IntegrityError("trusted-code capability does not name the exact file closure")
        if re.fullmatch(r"[0-9a-f]{64}", str(entry.get("sha256", ""))) is None:
            raise IntegrityError("trusted-code capability has an invalid file digest")
        size = entry.get("size_bytes")
        if isinstance(size, bool) or not isinstance(size, int) or size < 0:
            raise IntegrityError("trusted-code capability has an invalid file size")
    actual = attest_trusted_code(control_root, check_loaded_origins=False)
    if actual != expected:
        raise IntegrityError("trusted Harness code changed after Job launch")


def canonical_manifest_json(value: dict[str, Any]) -> str:
    """Stable debug rendering used only by tests and diagnostics."""

    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
