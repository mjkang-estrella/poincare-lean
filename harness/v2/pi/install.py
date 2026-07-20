"""Deterministic, fail-closed attestation for the pinned Pi distribution.

This module deliberately does not install Pi or execute ``npm`` or a ``.bin``
wrapper. Trusted orchestration supplies explicit absolute paths, the version
captured from that exact Node executable, and optionally the captured stdout of
``npm ls --json --all``. Verification re-probes the attested Node path directly;
it never resolves ``node`` through ``PATH``. The returned manifest is ordinary
canonical JSON that must be sealed outside the install tree.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import os
import posixpath
import re
import stat
import subprocess
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


class PiInstallError(RuntimeError):
    """Raised when a Pi install cannot be attested exactly."""


MANIFEST_SCHEMA = "poincare.pi-install.v2"
PI_PACKAGE_NAME = "@earendil-works/pi-coding-agent"
PI_PACKAGE_VERSION = "0.80.10"
PI_NODE_ENGINE = ">=22.19.0"
PI_MINIMUM_NODE_VERSION = "22.19.0"
ROOT_PACKAGE_NAME = "poincare-harness-pi-extension"
PINNED_PACKAGE_LOCK_SHA256 = (
    "a9b73914f657e6678cb7f8a8fb2fd518d1c0dd945b55cc7c10362cceae310832"
)

_TREE_DOMAIN = b"poincare-harness-v2-pi-install-tree-v1\0"
_GRAPH_FORMAT = "npm-ls-json-all-canonical-v1"
_SHA256_RE = frozenset("0123456789abcdef")
_NODE_VERSION_RE = re.compile(r"\Av?(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\Z")
_CAPTURE_PATHS = frozenset(
    {
        "package.json",
        "package-lock.json",
        "node_modules/@earendil-works/pi-coding-agent/package.json",
        "node_modules/@earendil-works/pi-coding-agent/dist/cli.js",
    }
)


@dataclass(frozen=True)
class _Metadata:
    kind: str
    mode: int
    size: int
    device: int
    inode: int
    mtime_ns: int
    ctime_ns: int
    target: str | None = None


def _canonical_json_bytes(value: Any) -> bytes:
    try:
        rendered = json.dumps(
            value,
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        return rendered.encode("utf-8", "strict")
    except (TypeError, ValueError, UnicodeError) as exc:
        raise PiInstallError("value is not canonical UTF-8 JSON") from exc


def canonical_manifest_bytes(manifest: Mapping[str, Any]) -> bytes:
    """Return the exact bytes callers should seal for an install manifest."""

    if not isinstance(manifest, Mapping):
        raise PiInstallError("install manifest must be a JSON object")
    return _canonical_json_bytes(dict(manifest))


def install_manifest_sha256(manifest: Mapping[str, Any]) -> str:
    """Hash the canonical, separately sealable manifest bytes."""

    return hashlib.sha256(canonical_manifest_bytes(manifest)).hexdigest()


def _reject_constant(raw: str) -> None:
    raise ValueError(f"non-finite JSON number is forbidden: {raw}")


def _reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _parse_json_bytes(data: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            data.decode("utf-8", "strict"),
            object_pairs_hook=_reject_duplicate_pairs,
            parse_constant=_reject_constant,
        )
    except (UnicodeError, ValueError, json.JSONDecodeError) as exc:
        raise PiInstallError(f"{label} is not strict UTF-8 JSON") from exc
    if not isinstance(value, dict):
        raise PiInstallError(f"{label} must contain a JSON object")
    return value


def _validate_sha256(value: str, label: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in _SHA256_RE for character in value)
    ):
        raise PiInstallError(f"{label} must be a lowercase SHA-256 digest")
    return value


def _absolute_path(raw: str | os.PathLike[str], label: str) -> Path:
    try:
        rendered = os.fspath(raw)
    except TypeError as exc:
        raise PiInstallError(f"{label} must be an explicit absolute path") from exc
    if not isinstance(rendered, str) or not rendered or "\x00" in rendered:
        raise PiInstallError(f"{label} must be an explicit absolute path")
    path = Path(rendered)
    if not path.is_absolute():
        raise PiInstallError(f"{label} must be an explicit absolute path")
    if any(part == ".." for part in path.parts):
        raise PiInstallError(f"{label} must not contain parent traversal")
    normalized = os.path.normpath(rendered)
    if normalized != rendered:
        raise PiInstallError(f"{label} must already be a normalized absolute path")
    return path


def _descriptor_flags(*, directory: bool) -> int:
    required = ("O_CLOEXEC", "O_NOFOLLOW")
    if directory:
        required += ("O_DIRECTORY",)
    missing = [name for name in required if not hasattr(os, name)]
    if missing:
        raise PiInstallError(
            "platform lacks required no-follow descriptor flags: " + ", ".join(missing)
        )
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    if directory:
        flags |= os.O_DIRECTORY
    return flags


def _open_absolute_no_symlinks(path: Path, *, directory: bool, label: str) -> int:
    """Open an absolute path one component at a time without following links."""

    current = os.open("/", _descriptor_flags(directory=True))
    try:
        parts = path.parts[1:]
        if not parts:
            if not directory:
                raise PiInstallError(f"{label} must be a regular file")
            return current
        for index, component in enumerate(parts):
            last = index == len(parts) - 1
            try:
                child = os.open(
                    component,
                    _descriptor_flags(directory=directory if last else True),
                    dir_fd=current,
                )
            except OSError as exc:
                raise PiInstallError(
                    f"{label} is missing, redirected, or not the required file type"
                ) from exc
            os.close(current)
            current = child
        metadata = os.fstat(current)
        expected = stat.S_ISDIR(metadata.st_mode) if directory else stat.S_ISREG(metadata.st_mode)
        if not expected:
            raise PiInstallError(
                f"{label} is not a {'directory' if directory else 'regular file'}"
            )
        return current
    except BaseException:
        os.close(current)
        raise


def _metadata(metadata: os.stat_result, *, target: str | None = None) -> _Metadata:
    if stat.S_ISREG(metadata.st_mode):
        kind = "file"
    elif stat.S_ISDIR(metadata.st_mode):
        kind = "directory"
    elif stat.S_ISLNK(metadata.st_mode):
        kind = "symlink"
    else:
        kind = "special"
    return _Metadata(
        kind=kind,
        mode=stat.S_IMODE(metadata.st_mode),
        size=metadata.st_size,
        device=metadata.st_dev,
        inode=metadata.st_ino,
        mtime_ns=metadata.st_mtime_ns,
        ctime_ns=metadata.st_ctime_ns,
        target=target,
    )


def _read_open_regular(
    descriptor: int,
    before: os.stat_result,
    label: str,
) -> tuple[bytes, str]:
    opened = os.fstat(descriptor)
    identity_before = _metadata(before)
    identity_opened = _metadata(opened)
    if identity_before != identity_opened or identity_opened.kind != "file":
        raise PiInstallError(f"regular file changed while opening: {label}")
    digest = hashlib.sha256()
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = os.read(descriptor, 1024 * 1024)
        if not chunk:
            break
        digest.update(chunk)
        total += len(chunk)
        if label in _CAPTURE_PATHS:
            chunks.append(chunk)
    after = os.fstat(descriptor)
    if _metadata(after) != identity_opened or total != opened.st_size:
        raise PiInstallError(f"regular file changed while hashing: {label}")
    return b"".join(chunks), digest.hexdigest()


def _safe_relative_path(relative: str) -> str:
    if not relative or "\x00" in relative or "\\" in relative:
        raise PiInstallError("install tree contains an unsafe path")
    try:
        relative.encode("utf-8", "strict")
    except UnicodeError as exc:
        raise PiInstallError("install tree path is not valid UTF-8") from exc
    parsed = PurePosixPath(relative)
    if parsed.is_absolute() or any(part in {"", ".", ".."} for part in parsed.parts):
        raise PiInstallError(f"install tree contains an unsafe path: {relative!r}")
    return parsed.as_posix()


def _scan_tree(
    root_fd: int,
) -> tuple[list[dict[str, Any]], dict[str, _Metadata], dict[str, bytes]]:
    entries: list[dict[str, Any]] = []
    metadata_by_path: dict[str, _Metadata] = {}
    captures: dict[str, bytes] = {}

    def visit(directory_fd: int, prefix: str) -> None:
        try:
            names = os.listdir(directory_fd)
        except OSError as exc:
            raise PiInstallError("cannot enumerate Pi install tree") from exc
        try:
            names.sort(key=lambda item: item.encode("utf-8", "strict"))
        except UnicodeError as exc:
            raise PiInstallError("install tree filename is not valid UTF-8") from exc
        for name in names:
            relative = _safe_relative_path(f"{prefix}/{name}" if prefix else name)
            try:
                before = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            except OSError as exc:
                raise PiInstallError(f"cannot stat install tree entry: {relative}") from exc
            basic = _metadata(before)
            if basic.kind == "directory":
                try:
                    child_fd = os.open(
                        name,
                        _descriptor_flags(directory=True),
                        dir_fd=directory_fd,
                    )
                except OSError as exc:
                    raise PiInstallError(
                        f"install directory changed while opening: {relative}"
                    ) from exc
                try:
                    opened = _metadata(os.fstat(child_fd))
                    if opened != basic:
                        raise PiInstallError(
                            f"install directory changed while opening: {relative}"
                        )
                    metadata_by_path[relative] = basic
                    entries.append(
                        {"kind": "directory", "mode": basic.mode, "path": relative}
                    )
                    visit(child_fd, relative)
                finally:
                    os.close(child_fd)
            elif basic.kind == "file":
                try:
                    child_fd = os.open(
                        name,
                        _descriptor_flags(directory=False),
                        dir_fd=directory_fd,
                    )
                except OSError as exc:
                    raise PiInstallError(
                        f"install file changed while opening: {relative}"
                    ) from exc
                try:
                    content, digest = _read_open_regular(child_fd, before, relative)
                finally:
                    os.close(child_fd)
                metadata_by_path[relative] = basic
                entries.append(
                    {
                        "kind": "file",
                        "mode": basic.mode,
                        "path": relative,
                        "sha256": digest,
                        "size_bytes": basic.size,
                    }
                )
                if relative in _CAPTURE_PATHS:
                    captures[relative] = content
            elif basic.kind == "symlink":
                try:
                    target = os.readlink(name, dir_fd=directory_fd)
                except OSError as exc:
                    raise PiInstallError(f"cannot read install symlink: {relative}") from exc
                if (
                    not target
                    or "\x00" in target
                    or "\\" in target
                    or PurePosixPath(target).is_absolute()
                ):
                    raise PiInstallError(
                        f"install symlink target must be nonempty and relative: {relative}"
                    )
                try:
                    target_bytes = target.encode("utf-8", "strict")
                except UnicodeError as exc:
                    raise PiInstallError(
                        f"install symlink target is not valid UTF-8: {relative}"
                    ) from exc
                if len(target_bytes) != basic.size:
                    raise PiInstallError(f"install symlink changed while reading: {relative}")
                with_target = _Metadata(**{**basic.__dict__, "target": target})
                metadata_by_path[relative] = with_target
                entries.append(
                    {
                        "kind": "symlink",
                        "mode": basic.mode,
                        "path": relative,
                        "sha256": hashlib.sha256(target_bytes).hexdigest(),
                        "size_bytes": len(target_bytes),
                        "target": target,
                    }
                )
            else:
                raise PiInstallError(f"special file is forbidden in Pi install: {relative}")

    visit(root_fd, "")
    entries.sort(key=lambda item: item["path"].encode("utf-8"))
    return entries, metadata_by_path, captures


def _scan_metadata(root_fd: int) -> dict[str, _Metadata]:
    result: dict[str, _Metadata] = {}

    def visit(directory_fd: int, prefix: str) -> None:
        try:
            names = os.listdir(directory_fd)
            names.sort(key=lambda item: item.encode("utf-8", "strict"))
        except (OSError, UnicodeError) as exc:
            raise PiInstallError("cannot revalidate Pi install tree") from exc
        for name in names:
            relative = _safe_relative_path(f"{prefix}/{name}" if prefix else name)
            try:
                found = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            except OSError as exc:
                raise PiInstallError(f"install entry disappeared: {relative}") from exc
            current = _metadata(found)
            if current.kind == "symlink":
                try:
                    target = os.readlink(name, dir_fd=directory_fd)
                except OSError as exc:
                    raise PiInstallError(f"cannot re-read install symlink: {relative}") from exc
                current = _Metadata(**{**current.__dict__, "target": target})
            elif current.kind == "directory":
                try:
                    child_fd = os.open(
                        name,
                        _descriptor_flags(directory=True),
                        dir_fd=directory_fd,
                    )
                except OSError as exc:
                    raise PiInstallError(
                        f"install directory changed during revalidation: {relative}"
                    ) from exc
                try:
                    if _metadata(os.fstat(child_fd)) != current:
                        raise PiInstallError(
                            f"install directory changed during revalidation: {relative}"
                        )
                    result[relative] = current
                    visit(child_fd, relative)
                finally:
                    os.close(child_fd)
                continue
            elif current.kind != "file":
                raise PiInstallError(f"special file is forbidden in Pi install: {relative}")
            result[relative] = current

    visit(root_fd, "")
    return result


def _validate_symlinks(metadata_by_path: Mapping[str, _Metadata]) -> None:
    for relative, metadata in metadata_by_path.items():
        if metadata.kind != "symlink":
            continue
        assert metadata.target is not None
        lexical = posixpath.normpath(
            posixpath.join(posixpath.dirname(relative), metadata.target)
        )
        if lexical in {"", ".", ".."} or lexical.startswith("../") or lexical.startswith("/"):
            raise PiInstallError(f"install symlink escapes its root: {relative}")
        _safe_relative_path(lexical)

        # Every traversed parent must be a real directory, never another link.
        parent_parts = PurePosixPath(lexical).parts[:-1]
        current: list[str] = []
        for part in parent_parts:
            current.append(part)
            parent = metadata_by_path.get("/".join(current))
            if parent is None or parent.kind != "directory":
                raise PiInstallError(
                    f"install symlink traverses a missing or linked directory: {relative}"
                )

        seen = {relative}
        terminal = lexical
        while True:
            target_metadata = metadata_by_path.get(terminal)
            if target_metadata is None:
                raise PiInstallError(f"install symlink is dangling: {relative}")
            if target_metadata.kind != "symlink":
                break
            if terminal in seen:
                raise PiInstallError(f"install symlink cycle is forbidden: {relative}")
            seen.add(terminal)
            assert target_metadata.target is not None
            terminal = posixpath.normpath(
                posixpath.join(posixpath.dirname(terminal), target_metadata.target)
            )
            if terminal in {"", ".", ".."} or terminal.startswith("../") or terminal.startswith("/"):
                raise PiInstallError(f"install symlink chain escapes its root: {relative}")


def _require_mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise PiInstallError(f"{label} must be a JSON object")
    return value


def _relative_bin_path(raw: Any) -> str:
    if not isinstance(raw, str) or not raw or "\x00" in raw or "\\" in raw:
        raise PiInstallError("installed Pi bin.pi must be a relative POSIX path")
    parsed = PurePosixPath(raw)
    if parsed.is_absolute() or any(part in {"", ".", ".."} for part in parsed.parts):
        raise PiInstallError("installed Pi bin.pi must be a contained relative path")
    return parsed.as_posix()


def _validate_package_metadata(
    captures: Mapping[str, bytes],
    *,
    cli_js_path: Path,
    install_root: Path,
    expected_package_lock_sha256: str,
) -> tuple[str, str, str]:
    missing = sorted(_CAPTURE_PATHS.difference(captures))
    if missing:
        raise PiInstallError("Pi install is missing required regular files: " + ", ".join(missing))

    root_package = _parse_json_bytes(captures["package.json"], "root package.json")
    if root_package.get("name") != ROOT_PACKAGE_NAME:
        raise PiInstallError("root package.json has the wrong package name")
    dependencies = _require_mapping(root_package.get("dependencies"), "root dependencies")
    if dependencies.get(PI_PACKAGE_NAME) != PI_PACKAGE_VERSION:
        raise PiInstallError("root package.json does not pin the exact Pi version")

    lock_bytes = captures["package-lock.json"]
    lock_sha256 = hashlib.sha256(lock_bytes).hexdigest()
    if not hmac.compare_digest(lock_sha256, expected_package_lock_sha256):
        raise PiInstallError("installed package-lock.json differs from the trusted pin")
    lock = _parse_json_bytes(lock_bytes, "root package-lock.json")
    if lock.get("name") != ROOT_PACKAGE_NAME or lock.get("lockfileVersion") != 3:
        raise PiInstallError("root package-lock.json identity or format is not pinned")
    packages = _require_mapping(lock.get("packages"), "package-lock packages")
    root_lock = _require_mapping(packages.get(""), "package-lock root package")
    root_lock_dependencies = _require_mapping(
        root_lock.get("dependencies"), "package-lock root dependencies"
    )
    if root_lock_dependencies.get(PI_PACKAGE_NAME) != PI_PACKAGE_VERSION:
        raise PiInstallError("package-lock root does not pin the exact Pi version")
    locked_pi = _require_mapping(
        packages.get(f"node_modules/{PI_PACKAGE_NAME}"), "package-lock Pi package"
    )
    if locked_pi.get("version") != PI_PACKAGE_VERSION:
        raise PiInstallError("package-lock contains the wrong Pi version")

    installed = _parse_json_bytes(
        captures[f"node_modules/{PI_PACKAGE_NAME}/package.json"],
        "installed Pi package.json",
    )
    if installed.get("name") != PI_PACKAGE_NAME or installed.get("version") != PI_PACKAGE_VERSION:
        raise PiInstallError("installed Pi package name or version differs from the pin")
    installed_engines = _require_mapping(installed.get("engines"), "installed Pi engines")
    locked_engines = _require_mapping(locked_pi.get("engines"), "package-lock Pi engines")
    if (
        installed_engines.get("node") != PI_NODE_ENGINE
        or locked_engines.get("node") != PI_NODE_ENGINE
    ):
        raise PiInstallError("installed Pi Node engine requirement differs from the pin")
    installed_bin = installed.get("bin")
    if isinstance(installed_bin, Mapping):
        bin_path = _relative_bin_path(installed_bin.get("pi"))
    else:
        bin_path = _relative_bin_path(installed_bin)
    locked_bin = locked_pi.get("bin")
    if isinstance(locked_bin, Mapping):
        locked_bin_path = _relative_bin_path(locked_bin.get("pi"))
    else:
        locked_bin_path = _relative_bin_path(locked_bin)
    if bin_path != locked_bin_path:
        raise PiInstallError("installed Pi CLI path differs from package-lock")

    expected_cli = install_root / "node_modules" / "@earendil-works" / "pi-coding-agent"
    expected_cli = expected_cli / Path(*PurePosixPath(bin_path).parts)
    if cli_js_path != expected_cli:
        raise PiInstallError("explicit Pi CLI JS path does not match pinned package metadata")
    relative_cli = cli_js_path.relative_to(install_root).as_posix()
    if relative_cli not in captures:
        raise PiInstallError("resolved Pi CLI JS is not a regular file")
    return lock_sha256, relative_cli, PI_NODE_ENGINE


def _dependency_graph_attestation(value: Any | None) -> dict[str, Any] | None:
    if value is None:
        return None
    if isinstance(value, bytes):
        graph = _parse_json_bytes(value, "npm dependency graph")
    elif isinstance(value, str):
        try:
            encoded = value.encode("utf-8", "strict")
        except UnicodeError as exc:
            raise PiInstallError("npm dependency graph is not strict UTF-8 JSON") from exc
        graph = _parse_json_bytes(encoded, "npm dependency graph")
    elif isinstance(value, Mapping):
        # Round-trip to reject non-JSON values and normalize Mapping subclasses.
        graph = _parse_json_bytes(_canonical_json_bytes(dict(value)), "npm dependency graph")
    else:
        raise PiInstallError("npm dependency graph must be JSON bytes, text, or an object")
    dependencies = _require_mapping(graph.get("dependencies"), "npm graph dependencies")
    pi = _require_mapping(dependencies.get(PI_PACKAGE_NAME), "npm graph Pi package")
    if pi.get("version") != PI_PACKAGE_VERSION:
        raise PiInstallError("npm dependency graph contains the wrong Pi version")
    canonical = _canonical_json_bytes(graph)
    return {
        "format": _GRAPH_FORMAT,
        "sha256": hashlib.sha256(canonical).hexdigest(),
        "size_bytes": len(canonical),
    }


def _node_attestation(node_executable: Path) -> dict[str, Any]:
    descriptor = _open_absolute_no_symlinks(
        node_executable, directory=False, label="Node executable"
    )
    try:
        before = os.fstat(descriptor)
        if stat.S_IMODE(before.st_mode) & 0o111 == 0:
            raise PiInstallError("Node executable has no executable mode bit")
        _unused, digest = _read_open_regular(descriptor, before, "Node executable")
        initial = _metadata(before)
    finally:
        os.close(descriptor)
    recheck = _open_absolute_no_symlinks(
        node_executable, directory=False, label="Node executable"
    )
    try:
        if _metadata(os.fstat(recheck)) != initial:
            raise PiInstallError("Node executable changed during attestation")
    finally:
        os.close(recheck)
    return {
        "mode": initial.mode,
        "path": str(node_executable),
        "sha256": digest,
        "size_bytes": initial.size,
    }


def _normalize_node_version(raw: Any, label: str) -> tuple[str, tuple[int, int, int]]:
    if not isinstance(raw, str):
        raise PiInstallError(f"{label} must be a strict Node semantic version")
    rendered = raw.strip()
    match = _NODE_VERSION_RE.fullmatch(rendered)
    if match is None:
        raise PiInstallError(f"{label} must be a strict Node semantic version")
    parts = tuple(int(part) for part in match.groups())
    normalized = ".".join(str(part) for part in parts)
    minimum = tuple(int(part) for part in PI_MINIMUM_NODE_VERSION.split("."))
    if parts < minimum:
        raise PiInstallError(
            f"Pi {PI_PACKAGE_VERSION} requires Node {PI_NODE_ENGINE}; found {normalized}"
        )
    return normalized, parts


def probe_node_version(node_executable: str | os.PathLike[str]) -> str:
    """Return the exact absolute Node executable's compatible semantic version."""

    node_path = _absolute_path(node_executable, "Node executable")
    before = _node_attestation(node_path)
    try:
        result = subprocess.run(
            (str(node_path), "--version"),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=10,
            env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise PiInstallError("exact attested Node version probe failed") from exc
    if result.returncode != 0 or result.stderr or len(result.stdout) > 128:
        raise PiInstallError("exact attested Node version probe failed")
    try:
        raw_version = result.stdout.decode("ascii", "strict")
    except UnicodeError as exc:
        raise PiInstallError("exact attested Node version is not ASCII") from exc
    normalized, _parts = _normalize_node_version(raw_version, "Node version")
    if _node_attestation(node_path) != before:
        raise PiInstallError("Node executable changed during version probe")
    return normalized


def build_install_manifest(
    *,
    node_executable: str | os.PathLike[str],
    node_version: str,
    install_root: str | os.PathLike[str],
    cli_js_path: str | os.PathLike[str],
    npm_dependency_graph: Any | None = None,
    expected_package_lock_sha256: str = PINNED_PACKAGE_LOCK_SHA256,
) -> dict[str, Any]:
    """Attest a complete Pi 0.80.10 install without executing any program.

    ``node_version`` is the stdout captured from the exact ``node_executable``;
    sealed verification executes that same absolute binary and compares it.
    ``npm_dependency_graph`` is optional trusted-caller input: pass the stdout
    bytes (or decoded JSON object) previously obtained with
    ``npm ls --json --all``.  This function never locates or invokes npm.
    The package-lock override exists for isolated tests and an explicitly
    reviewed future pin; production callers should use the compiled default.
    """

    expected_lock = _validate_sha256(
        expected_package_lock_sha256, "expected package-lock hash"
    )
    node_path = _absolute_path(node_executable, "Node executable")
    normalized_node_version, _node_version_parts = _normalize_node_version(
        node_version, "Node version"
    )
    root_path = _absolute_path(install_root, "Pi install root")
    cli_path = _absolute_path(cli_js_path, "Pi CLI JS")
    try:
        cli_path.relative_to(root_path)
    except ValueError as exc:
        raise PiInstallError("Pi CLI JS must be contained by the install root") from exc

    root_fd = _open_absolute_no_symlinks(
        root_path, directory=True, label="Pi install root"
    )
    try:
        root_before = _metadata(os.fstat(root_fd))
        entries, metadata_by_path, captures = _scan_tree(root_fd)
        _validate_symlinks(metadata_by_path)
        stable = _scan_metadata(root_fd)
        if stable != metadata_by_path or _metadata(os.fstat(root_fd)) != root_before:
            raise PiInstallError("Pi install tree changed during attestation")
    finally:
        os.close(root_fd)

    lock_sha256, relative_cli, node_engine = _validate_package_metadata(
        captures,
        cli_js_path=cli_path,
        install_root=root_path,
        expected_package_lock_sha256=expected_lock,
    )
    cli_entry = next(
        (entry for entry in entries if entry["path"] == relative_cli), None
    )
    if cli_entry is None or cli_entry.get("kind") != "file":
        raise PiInstallError("resolved Pi CLI JS is not a regular file")

    tree_payload = {"entries": entries, "root_mode": root_before.mode}
    tree_sha256 = hashlib.sha256(
        _TREE_DOMAIN + _canonical_json_bytes(tree_payload)
    ).hexdigest()
    counts = {
        "directories": sum(entry["kind"] == "directory" for entry in entries),
        "files": sum(entry["kind"] == "file" for entry in entries),
        "symlinks": sum(entry["kind"] == "symlink" for entry in entries),
    }
    node = _node_attestation(node_path)
    node.update(
        {
            "minimum_version": PI_MINIMUM_NODE_VERSION,
            "version": normalized_node_version,
        }
    )
    return {
        "cli_js": {
            "path": str(cli_path),
            "relative_path": relative_cli,
            "sha256": cli_entry["sha256"],
            "size_bytes": cli_entry["size_bytes"],
        },
        "install_root": str(root_path),
        "node": node,
        "npm_dependency_graph": _dependency_graph_attestation(npm_dependency_graph),
        "package": {
            "name": PI_PACKAGE_NAME,
            "node_engine": node_engine,
            "version": PI_PACKAGE_VERSION,
        },
        "package_lock_sha256": lock_sha256,
        "schema_version": MANIFEST_SCHEMA,
        "tree": {
            "counts": counts,
            "entries": entries,
            "entry_count": len(entries),
            "root_mode": root_before.mode,
            "sha256": tree_sha256,
            "total_file_bytes": sum(
                entry.get("size_bytes", 0)
                for entry in entries
                if entry["kind"] == "file"
            ),
        },
    }


def verify_install_manifest(
    manifest: Mapping[str, Any],
    *,
    node_executable: str | os.PathLike[str],
    install_root: str | os.PathLike[str],
    cli_js_path: str | os.PathLike[str],
    npm_dependency_graph: Any | None = None,
    expected_package_lock_sha256: str = PINNED_PACKAGE_LOCK_SHA256,
) -> dict[str, Any]:
    """Re-attest every byte and metadata entry, then match a sealed manifest."""

    if not isinstance(manifest, Mapping):
        raise PiInstallError("install manifest must be a JSON object")
    try:
        recorded_node_version = manifest["node"]["version"]
    except (KeyError, TypeError) as exc:
        raise PiInstallError("Pi install manifest lacks the recorded Node version") from exc
    expected = build_install_manifest(
        node_executable=node_executable,
        node_version=recorded_node_version,
        install_root=install_root,
        cli_js_path=cli_js_path,
        npm_dependency_graph=npm_dependency_graph,
        expected_package_lock_sha256=expected_package_lock_sha256,
    )
    try:
        supplied_bytes = canonical_manifest_bytes(manifest)
        expected_bytes = canonical_manifest_bytes(expected)
    except PiInstallError:
        raise
    if not hmac.compare_digest(supplied_bytes, expected_bytes):
        raise PiInstallError("Pi install manifest or live distribution has drifted")
    live_node_version = probe_node_version(node_executable)
    if live_node_version != expected["node"]["version"]:
        raise PiInstallError(
            "live Node version differs from the sealed Pi install manifest"
        )
    return expected


def _read_sealed_external_file(
    raw_path: str | os.PathLike[str], *, label: str, maximum_bytes: int
) -> tuple[Path, bytes]:
    path = _absolute_path(raw_path, label)
    descriptor = _open_absolute_no_symlinks(path, directory=False, label=label)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or stat.S_IMODE(before.st_mode) & 0o222
            or before.st_size > maximum_bytes
        ):
            raise PiInstallError(f"{label} must be a bounded sealed regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, maximum_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
            if total > maximum_bytes:
                raise PiInstallError(f"{label} exceeds {maximum_bytes} bytes")
        after = os.fstat(descriptor)
        if _metadata(before) != _metadata(after) or total != before.st_size:
            raise PiInstallError(f"{label} changed while being read")
    finally:
        os.close(descriptor)
    return path, b"".join(chunks)


def _require_read_only_install_modes(manifest: Mapping[str, Any]) -> None:
    """Reject a purported sealed install with any writable tree entry.

    The install manifest intentionally records exact POSIX modes.  A root-owned
    path may be non-writable by the Harness uid while still being mutable by
    its owner, so the sealed-install contract is stricter than effective uid
    access: the install root, every directory, and every regular file must
    have all owner/group/world write bits cleared.  Symlink modes are not
    meaningful on the supported platform and are covered by target/path
    attestation instead.
    """

    try:
        tree = _require_mapping(manifest["tree"], "Pi install manifest tree")
        root_mode = tree["root_mode"]
        entries = tree["entries"]
    except KeyError as exc:
        raise PiInstallError("Pi install manifest lacks sealed tree modes") from exc
    if (
        isinstance(root_mode, bool)
        or not isinstance(root_mode, int)
        or root_mode < 0
        or root_mode > 0o7777
    ):
        raise PiInstallError("Pi install manifest root mode is invalid")
    if root_mode & 0o222:
        raise PiInstallError("Pi install root has a writable mode bit")
    if not isinstance(entries, list):
        raise PiInstallError("Pi install manifest entries must be a JSON array")
    for index, raw_entry in enumerate(entries):
        entry = _require_mapping(raw_entry, f"Pi install manifest entry {index}")
        kind = entry.get("kind")
        if kind not in {"directory", "file"}:
            continue
        mode = entry.get("mode")
        relative = entry.get("path")
        if (
            isinstance(mode, bool)
            or not isinstance(mode, int)
            or mode < 0
            or mode > 0o7777
            or not isinstance(relative, str)
        ):
            raise PiInstallError(f"Pi install manifest {kind} mode is invalid")
        if mode & 0o222:
            raise PiInstallError(
                f"Pi install {kind} has a writable mode bit: {relative}"
            )


def verify_sealed_install_files(
    manifest_path: str | os.PathLike[str],
    dependency_graph_path: str | os.PathLike[str],
    *,
    expected_node_executable: str | os.PathLike[str] | None = None,
    expected_package_lock_sha256: str = PINNED_PACKAGE_LOCK_SHA256,
) -> dict[str, Any]:
    """Re-attest one separately sealed manifest/graph pair for deploy preflight."""

    sealed_manifest, manifest_bytes = _read_sealed_external_file(
        manifest_path,
        label="Pi install manifest",
        maximum_bytes=64 * 1024 * 1024,
    )
    sealed_graph, graph_bytes = _read_sealed_external_file(
        dependency_graph_path,
        label="Pi dependency graph",
        maximum_bytes=64 * 1024 * 1024,
    )
    manifest = _parse_json_bytes(manifest_bytes, "Pi install manifest")
    graph = _parse_json_bytes(graph_bytes, "Pi dependency graph")
    if canonical_manifest_bytes(manifest) != manifest_bytes:
        raise PiInstallError("sealed Pi install manifest is not canonical JSON")
    if _canonical_json_bytes(graph) != graph_bytes:
        raise PiInstallError("sealed Pi dependency graph is not canonical JSON")
    try:
        node = _absolute_path(manifest["node"]["path"], "manifest Node executable")
        install_root = _absolute_path(manifest["install_root"], "manifest install root")
        cli = _absolute_path(manifest["cli_js"]["path"], "manifest Pi CLI JS")
    except (KeyError, TypeError) as exc:
        raise PiInstallError("sealed Pi install manifest lacks exact install paths") from exc
    if expected_node_executable is not None:
        expected_node = _absolute_path(
            expected_node_executable, "expected Node executable"
        )
        if node != expected_node:
            raise PiInstallError("sealed Pi install manifest names an unexpected Node executable")
    for external, label in (
        (sealed_manifest, "manifest"),
        (sealed_graph, "dependency graph"),
    ):
        try:
            external.relative_to(install_root)
        except ValueError:
            pass
        else:
            raise PiInstallError(f"sealed Pi {label} must be outside the install tree")
    _require_read_only_install_modes(manifest)
    return verify_install_manifest(
        manifest,
        node_executable=node,
        install_root=install_root,
        cli_js_path=cli,
        npm_dependency_graph=graph,
        expected_package_lock_sha256=expected_package_lock_sha256,
    )


# Short aliases for callers that use attestation terminology.
attest_pi_install = build_install_manifest
verify_pi_install = verify_install_manifest


__all__ = [
    "MANIFEST_SCHEMA",
    "PINNED_PACKAGE_LOCK_SHA256",
    "PI_PACKAGE_NAME",
    "PI_PACKAGE_VERSION",
    "PI_MINIMUM_NODE_VERSION",
    "PI_NODE_ENGINE",
    "PiInstallError",
    "attest_pi_install",
    "build_install_manifest",
    "canonical_manifest_bytes",
    "install_manifest_sha256",
    "probe_node_version",
    "verify_install_manifest",
    "verify_pi_install",
    "verify_sealed_install_files",
]
