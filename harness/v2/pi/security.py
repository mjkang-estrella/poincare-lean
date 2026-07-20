"""Shared fail-closed path, scope, patch, and subprocess primitives."""

from __future__ import annotations

import fnmatch
import fcntl
import hashlib
import json
import os
import re
import resource
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from ctypes import CDLL, c_int
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Mapping, Sequence

from .install import PI_MINIMUM_NODE_VERSION


class SecurityError(RuntimeError):
    """Raised when a requested operation exceeds the Job capability."""


BWRAP_PROFILE_VERSION = "poincare-lean-bwrap-v2"
PI_BWRAP_PROFILE_VERSION = "poincare-pi-bwrap-v2"
SPARSE_LEAN_BWRAP_PROFILE_VERSION = "poincare-lean-sparse-bwrap-v1"

# Debian and Ubuntu externalize a small, fixed set of Node builtins from
# libnode.  A bare bind of /usr/bin/node therefore aborts before JavaScript can
# start.  Mount only those exact root-owned files when they exist; never expose
# the surrounding system node_modules tree.
_NODE_EXTERNALIZED_BUILTIN_PATHS = (
    Path("/usr/share/nodejs/acorn-walk/dist/walk.js"),
    Path("/usr/share/nodejs/acorn/dist/acorn.js"),
    Path("/usr/share/nodejs/cjs-module-lexer/dist/lexer.js"),
    Path("/usr/share/nodejs/cjs-module-lexer/lexer.js"),
    Path("/usr/share/nodejs/minimatch/dist/cjs/index.bundle.js"),
    Path("/usr/share/nodejs/undici/undici-fetch.js"),
)
CACHE_MANIFEST_NAME = ".harness-cache.json"
CACHE_MANIFEST_VERSION = "poincare-lake-cache-v1"
PACKAGE_OVERRIDES_NAME = ".harness-package-overrides.json"
SANDBOX_TOOLCHAIN_ROOT = Path("/opt/lean")
SANDBOX_WORKTREE_ROOT = Path("/work")
SANDBOX_PI_NODE = Path("/opt/pi-node/node")
SANDBOX_PI_INSTALL_ROOT = Path("/opt/pi-install")
SANDBOX_PI_INPUT_ROOT = Path("/sealed")
SANDBOX_PI_AGENT_ROOT = SANDBOX_PI_INPUT_ROOT / "agent"
SANDBOX_PI_RUNTIME_ROOT = Path("/runtime")
SANDBOX_PI_BROKER_ROOT = Path("/run/harness-broker")
SANDBOX_SPARSE_SOURCE_ROOT = Path("/work")
_SEALED_TREE_DOMAIN = b"poincare-sealed-tree-v1\0"
_PI_INSTALL_TREE_DOMAIN = b"poincare-harness-v2-pi-install-tree-v1\0"
_PI_ALLOWED_INPUT_DESTINATIONS = {
    "extension": SANDBOX_PI_INPUT_ROOT / "extension.ts",
    "public_config": SANDBOX_PI_INPUT_ROOT / "public-config.json",
    "system_prompt": SANDBOX_PI_INPUT_ROOT / "system-prompt.md",
    "settings": SANDBOX_PI_AGENT_ROOT / "settings.json",
}
_LIBC = CDLL(None, use_errno=True) if sys.platform == "linux" else None
if _LIBC is not None:
    _LIBC.prctl.argtypes = (c_int, c_int, c_int, c_int, c_int)
    _LIBC.prctl.restype = c_int


def normalize_relative(raw: str) -> str:
    if not isinstance(raw, str) or not raw or "\x00" in raw or "\\" in raw:
        raise SecurityError("path must be a nonempty POSIX repository-relative path")
    path = PurePosixPath(raw)
    if (
        path.is_absolute()
        or raw.startswith("~")
        or not path.parts
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise SecurityError(f"unsafe repository-relative path: {raw!r}")
    return path.as_posix()


def _match_parts(path: tuple[str, ...], pattern: tuple[str, ...]) -> bool:
    if not pattern:
        return not path
    head, *tail = pattern
    remaining = tuple(tail)
    if head == "**":
        return _match_parts(path, remaining) or bool(
            path and _match_parts(path[1:], pattern)
        )
    return bool(
        path
        and fnmatch.fnmatchcase(path[0], head)
        and _match_parts(path[1:], remaining)
    )


def scope_matches(path: str, pattern: str) -> bool:
    normalized_path = normalize_relative(path)
    normalized_pattern = normalize_relative(pattern)
    return _match_parts(
        PurePosixPath(normalized_path).parts,
        PurePosixPath(normalized_pattern).parts,
    )


def path_is_allowed(path: str, allowed: Sequence[str], forbidden: Sequence[str]) -> bool:
    normalized = normalize_relative(path)
    if normalized == ".git" or normalized.startswith(".git/"):
        return False
    return any(scope_matches(normalized, item) for item in allowed) and not any(
        scope_matches(normalized, item) for item in forbidden
    )


def resolve_repo_file(root: Path, relative: str, *, must_exist: bool = True) -> Path:
    normalized = normalize_relative(relative)
    candidate = root / Path(*PurePosixPath(normalized).parts)
    current = root
    for part in PurePosixPath(normalized).parts:
        current = current / part
        if current.is_symlink():
            raise SecurityError(f"path contains a symbolic link: {normalized}")
    if not must_exist:
        parent = candidate.parent.resolve(strict=True)
        try:
            parent.relative_to(root)
        except ValueError as exc:
            raise SecurityError(f"path escapes worktree: {normalized}") from exc
        return candidate
    try:
        resolved = candidate.resolve(strict=True)
        resolved.relative_to(root)
    except (OSError, ValueError) as exc:
        raise SecurityError(f"path escapes worktree or does not exist: {normalized}") from exc
    if not resolved.is_file():
        raise SecurityError(f"path is not a regular file: {normalized}")
    return resolved


_DIFF_HEADER = re.compile(r"^diff --git a/([^\s]+) b/([^\s]+)$")
_OLD_HEADER = re.compile(r"^--- a/([^\s\t]+)(?:\t.*)?$")
_NEW_HEADER = re.compile(r"^\+\+\+ b/([^\s\t]+)(?:\t.*)?$")
_HUNK_HEADER = re.compile(
    r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(.*)$"
)
_FORBIDDEN_PATCH_PREFIXES = (
    "GIT binary patch",
    "Binary files ",
    "rename from ",
    "rename to ",
    "copy from ",
    "copy to ",
    "old mode ",
    "new mode ",
    "new file mode ",
    "deleted file mode ",
    "similarity index ",
    "dissimilarity index ",
)


def normalize_unified_diff_hunk_counts(patch: str) -> tuple[str, bool]:
    """Repair only hunk counts, leaving paths, starts, and body bytes unchanged."""

    lines = patch.splitlines(keepends=True)
    normalized: list[str] = []
    changed = False
    index = 0
    while index < len(lines):
        line = lines[index]
        content = line[:-1] if line.endswith("\n") else line
        match = _HUNK_HEADER.fullmatch(content)
        if match is None:
            normalized.append(line)
            index += 1
            continue

        old_start, _declared_old, new_start, _declared_new, suffix = match.groups()
        body_end = index + 1
        old_count = 0
        new_count = 0
        while body_end < len(lines):
            body_line = lines[body_end]
            body = body_line[:-1] if body_line.endswith("\n") else body_line
            if _HUNK_HEADER.fullmatch(body) or _DIFF_HEADER.fullmatch(body):
                break
            if body == r"\ No newline at end of file":
                body_end += 1
                continue
            if body.startswith(" "):
                old_count += 1
                new_count += 1
            elif body.startswith("-"):
                old_count += 1
            elif body.startswith("+"):
                new_count += 1
            else:
                raise SecurityError("patch hunk body has an unsupported line prefix")
            body_end += 1
        if body_end == index + 1:
            raise SecurityError("patch contains an empty unified-diff hunk")

        ending = "\n" if line.endswith("\n") else ""
        corrected = (
            f"@@ -{old_start},{old_count} +{new_start},{new_count} @@{suffix}{ending}"
        )
        normalized.append(corrected)
        normalized.extend(lines[index + 1 : body_end])
        changed = changed or corrected != line
        index = body_end

    return "".join(normalized), changed


def validate_patch(
    patch: str,
    *,
    root: Path,
    allowed: Sequence[str],
    forbidden: Sequence[str],
    forbidden_tokens: Sequence[str],
    max_bytes: int = 512 * 1024,
) -> tuple[str, ...]:
    encoded = patch.encode("utf-8")
    if not patch.strip() or len(encoded) > max_bytes or "\x00" in patch:
        raise SecurityError("patch is empty, contains NUL, or exceeds the byte cap")
    if not patch.endswith("\n"):
        raise SecurityError("patch must end with a newline")
    touched: list[str] = []
    pending_old: str | None = None
    for line in patch.splitlines():
        if line.startswith(_FORBIDDEN_PATCH_PREFIXES):
            raise SecurityError(f"patch operation is forbidden: {line.split()[0]}")
        match = _DIFF_HEADER.fullmatch(line)
        if match:
            before, after = match.groups()
            if before != after:
                raise SecurityError("renames and cross-path patches are forbidden")
            normalized = normalize_relative(before)
            if not path_is_allowed(normalized, allowed, forbidden):
                raise SecurityError(f"patch path is outside Task scope: {normalized}")
            resolve_repo_file(root, normalized, must_exist=True)
            touched.append(normalized)
            pending_old = None
            continue
        match = _OLD_HEADER.fullmatch(line)
        if match:
            pending_old = normalize_relative(match.group(1))
            continue
        match = _NEW_HEADER.fullmatch(line)
        if match:
            new_path = normalize_relative(match.group(1))
            if pending_old is None or pending_old != new_path:
                raise SecurityError("patch file headers are missing or disagree")
            if new_path not in touched:
                raise SecurityError("patch headers do not match a diff --git header")
            pending_old = None
            continue
        if line.startswith(("--- /dev/null", "+++ /dev/null")):
            raise SecurityError("file creation and deletion are forbidden in scoped patches")
        if line.startswith("+") and not line.startswith("+++"):
            added = line[1:]
            for token in forbidden_tokens:
                if token and re.search(rf"\b{re.escape(token)}\b", added):
                    raise SecurityError(f"patch adds forbidden token: {token}")
    if not touched or pending_old is not None:
        raise SecurityError("patch has no complete, supported file diff")
    if len(set(touched)) != len(touched):
        raise SecurityError("patch repeats a file header")
    return tuple(touched)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _effectively_sealed(metadata: os.stat_result) -> bool:
    """Return whether the current uid cannot rewrite an attested entry."""

    mode = stat.S_IMODE(metadata.st_mode)
    if mode & 0o022:
        return False
    return metadata.st_uid != os.geteuid() or not bool(mode & 0o200)


def _stable_regular_record(
    path: Path,
    label: str,
    *,
    require_sealed: bool,
    require_executable: bool = False,
) -> dict[str, Any]:
    flags = os.O_RDONLY
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise SecurityError(f"cannot open {label} safely: {exc}") from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise SecurityError(f"{label} is not a regular file")
        if before.st_nlink != 1 and (not require_sealed or before.st_uid == os.geteuid()):
            raise SecurityError(f"{label} must not be hard-linked")
        if require_sealed and not _effectively_sealed(before):
            raise SecurityError(f"{label} is writable by the Harness uid or an untrusted group")
        if require_executable and not before.st_mode & 0o111:
            raise SecurityError(f"{label} is not executable")
        digest = hashlib.sha256()
        total = 0
        magic = b""
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            if not magic:
                magic = chunk[:4]
            digest.update(chunk)
            total += len(chunk)
        after = os.fstat(descriptor)
        identity_before = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_nlink,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        identity_after = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if total != before.st_size or identity_after != identity_before:
            raise SecurityError(f"{label} changed while it was attested")
        return {
            "sha256": digest.hexdigest(),
            "size_bytes": total,
            "mode": stat.S_IMODE(before.st_mode),
            "device": before.st_dev,
            "inode": before.st_ino,
            "mtime_ns": before.st_mtime_ns,
            "ctime_ns": before.st_ctime_ns,
            "elf": magic == b"\x7fELF",
        }
    finally:
        os.close(descriptor)


def _sealed_tree_attestation(
    root: Path,
    label: str,
    *,
    require_sealed: bool,
    allow_internal_symlinks: bool,
) -> tuple[str, int, tuple[Path, ...]]:
    """Hash one exact tree, including entry types, modes, and safe links."""

    if root.is_symlink() or not root.is_dir():
        raise SecurityError(f"{label} must be a real directory")
    root_info = root.stat(follow_symlinks=False)
    if require_sealed and not _effectively_sealed(root_info):
        raise SecurityError(f"{label} root is writable")
    digest = hashlib.sha256()
    digest.update(_SEALED_TREE_DOMAIN)
    digest.update(stat.S_IMODE(root_info.st_mode).to_bytes(4, "big"))
    count = 0
    elf_files: list[Path] = []
    pending: list[tuple[Path, PurePosixPath]] = [(root, PurePosixPath("."))]
    while pending:
        directory, relative_directory = pending.pop()
        try:
            children = sorted(os.scandir(directory), key=lambda item: item.name.encode("utf-8"))
        except (OSError, UnicodeEncodeError) as exc:
            raise SecurityError(f"cannot enumerate {label}: {exc}") from exc
        child_directories: list[tuple[Path, PurePosixPath]] = []
        for child in children:
            if any(marker in child.name for marker in ("\x00", "\n", "\r")):
                raise SecurityError(f"{label} contains an unsafe filename")
            try:
                child.name.encode("utf-8", "strict")
                info = child.stat(follow_symlinks=False)
            except (OSError, UnicodeEncodeError) as exc:
                raise SecurityError(f"cannot stat {label} entry: {exc}") from exc
            relative = (
                PurePosixPath(child.name)
                if relative_directory == PurePosixPath(".")
                else relative_directory / child.name
            )
            encoded = relative.as_posix().encode("utf-8")
            path = Path(child.path)
            if os.path.ismount(path):
                raise SecurityError(f"{label} contains a nested mountpoint: {relative}")
            if stat.S_ISDIR(info.st_mode):
                if require_sealed and not _effectively_sealed(info):
                    raise SecurityError(f"{label} contains a writable directory: {relative}")
                kind = b"D"
                payload = b""
                child_directories.append((path, relative))
            elif stat.S_ISREG(info.st_mode):
                record = _stable_regular_record(
                    path,
                    f"{label} entry {relative}",
                    require_sealed=require_sealed,
                )
                kind = b"F"
                payload = bytes.fromhex(record["sha256"])
                if record["elf"]:
                    elf_files.append(path)
            elif stat.S_ISLNK(info.st_mode):
                if not allow_internal_symlinks:
                    raise SecurityError(f"{label} contains a symbolic link: {relative}")
                try:
                    target = os.readlink(path)
                    resolved = path.resolve(strict=True)
                    resolved.relative_to(root)
                except (OSError, ValueError) as exc:
                    raise SecurityError(
                        f"{label} contains an escaping or broken symlink: {relative}"
                    ) from exc
                if not target or "\x00" in target or Path(target).is_absolute():
                    raise SecurityError(f"{label} contains an unsafe symlink: {relative}")
                kind = b"L"
                payload = target.encode("utf-8", "strict")
            else:
                raise SecurityError(f"{label} contains a special file: {relative}")
            digest.update(kind)
            digest.update(len(encoded).to_bytes(8, "big"))
            digest.update(encoded)
            digest.update(stat.S_IMODE(info.st_mode).to_bytes(4, "big"))
            digest.update(info.st_size.to_bytes(8, "big"))
            digest.update(len(payload).to_bytes(8, "big"))
            digest.update(payload)
            count += 1
        pending.extend(reversed(child_directories))
    if count == 0:
        raise SecurityError(f"{label} is empty")
    return digest.hexdigest(), count, tuple(sorted(elf_files, key=str))


def pi_distribution_tree_digest(install_root: Path | str) -> str:
    """Return the content-and-layout digest of a sealed npm installation."""

    root = _safe_absolute_directory(install_root, "Pi installation")
    digest, _, _ = _pi_install_tree_attestation(
        root,
    )
    return digest


def _pi_install_tree_attestation(
    root: Path,
) -> tuple[str, int, tuple[Path, ...]]:
    """Reproduce ``install.py``'s canonical tree digest while enforcing sealing."""

    if root.is_symlink() or not root.is_dir():
        raise SecurityError("Pi installation must be a real directory")
    root_info = root.stat(follow_symlinks=False)
    if stat.S_IMODE(root_info.st_mode) & 0o222:
        raise SecurityError("Pi installation root has a writable mode bit")
    entries: list[dict[str, Any]] = []
    elf_files: list[Path] = []
    pending: list[tuple[Path, PurePosixPath]] = [(root, PurePosixPath("."))]
    while pending:
        directory, relative_directory = pending.pop()
        try:
            children = sorted(os.scandir(directory), key=lambda item: item.name.encode("utf-8"))
        except (OSError, UnicodeEncodeError) as exc:
            raise SecurityError(f"cannot enumerate Pi installation: {exc}") from exc
        child_directories: list[tuple[Path, PurePosixPath]] = []
        for child in children:
            if any(marker in child.name for marker in ("\x00", "\n", "\r")):
                raise SecurityError("Pi installation contains an unsafe filename")
            try:
                child.name.encode("utf-8", "strict")
                info = child.stat(follow_symlinks=False)
            except (OSError, UnicodeEncodeError) as exc:
                raise SecurityError(f"cannot stat Pi installation entry: {exc}") from exc
            relative = (
                PurePosixPath(child.name)
                if relative_directory == PurePosixPath(".")
                else relative_directory / child.name
            )
            path = Path(child.path)
            if os.path.ismount(path):
                raise SecurityError(f"Pi installation contains a mountpoint: {relative}")
            mode = stat.S_IMODE(info.st_mode)
            if stat.S_ISDIR(info.st_mode):
                if mode & 0o222:
                    raise SecurityError(
                        f"Pi installation contains a directory with a writable mode bit: {relative}"
                    )
                entries.append({"kind": "directory", "mode": mode, "path": relative.as_posix()})
                child_directories.append((path, relative))
            elif stat.S_ISREG(info.st_mode):
                if mode & 0o222:
                    raise SecurityError(
                        f"Pi installation contains a file with a writable mode bit: {relative}"
                    )
                record = _stable_regular_record(
                    path,
                    f"Pi installation entry {relative}",
                    require_sealed=True,
                )
                entries.append(
                    {
                        "kind": "file",
                        "mode": mode,
                        "path": relative.as_posix(),
                        "sha256": record["sha256"],
                        "size_bytes": record["size_bytes"],
                    }
                )
                if record["elf"]:
                    elf_files.append(path)
            elif stat.S_ISLNK(info.st_mode):
                try:
                    target = os.readlink(path)
                    target_bytes = target.encode("utf-8", "strict")
                    resolved = path.resolve(strict=True)
                    resolved.relative_to(root)
                except (OSError, UnicodeEncodeError, ValueError) as exc:
                    raise SecurityError(
                        f"Pi installation contains an escaping or broken symlink: {relative}"
                    ) from exc
                if not target or "\x00" in target or "\\" in target or Path(target).is_absolute():
                    raise SecurityError(f"Pi installation contains an unsafe symlink: {relative}")
                entries.append(
                    {
                        "kind": "symlink",
                        "mode": mode,
                        "path": relative.as_posix(),
                        "sha256": hashlib.sha256(target_bytes).hexdigest(),
                        "size_bytes": len(target_bytes),
                        "target": target,
                    }
                )
            else:
                raise SecurityError(f"Pi installation contains a special file: {relative}")
        pending.extend(reversed(child_directories))
    if not entries:
        raise SecurityError("Pi installation is empty")
    entries.sort(key=lambda item: item["path"].encode("utf-8"))
    payload = json.dumps(
        {"entries": entries, "root_mode": stat.S_IMODE(root_info.st_mode)},
        ensure_ascii=False,
        allow_nan=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8", "strict")
    return (
        hashlib.sha256(_PI_INSTALL_TREE_DOMAIN + payload).hexdigest(),
        len(entries),
        tuple(sorted(elf_files, key=str)),
    )


def _is_within(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def _safe_absolute_directory(raw: str | Path, label: str) -> Path:
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink():
        raise SecurityError(f"{label} must not be a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise SecurityError(f"cannot resolve {label}: {exc}") from exc
    if not resolved.is_dir():
        raise SecurityError(f"{label} is not a directory")
    return resolved


def _safe_absolute_existing_path(raw: str | Path, label: str) -> Path:
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink():
        raise SecurityError(f"{label} must not be a symbolic link")
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as exc:
        raise SecurityError(f"cannot resolve {label}: {exc}") from exc
    if not (resolved.is_dir() or resolved.is_file()):
        raise SecurityError(f"{label} is not a regular file or directory")
    return resolved


def _runtime_library_mounts(
    executables: Sequence[Path],
) -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    """Resolve the exact dynamic-library closure for trusted ELF tools."""

    ldd = Path("/usr/bin/ldd")
    if ldd.is_symlink() or not ldd.is_file() or not os.access(ldd, os.X_OK):
        raise SecurityError("audited sandbox requires the fixed /usr/bin/ldd inspector")
    mounts: dict[str, dict[str, str]] = {}
    for executable in executables:
        result = run_limited(
            (str(ldd), str(executable)),
            cwd=Path("/"),
            env={"PATH": "/usr/bin:/bin", "LANG": "C", "LC_ALL": "C"},
            timeout_seconds=10,
            output_limit_bytes=128 * 1024,
            supervise_parent=True,
        )
        output = result.stdout.decode("utf-8", "replace")
        if result.returncode != 0 or result.timed_out or result.output_limited:
            error = result.stderr.decode("utf-8", "replace").strip()
            raise SecurityError(f"ldd rejected trusted toolchain executable: {error or result.returncode}")
        for line in output.splitlines():
            stripped = line.strip()
            if not stripped or stripped.startswith("linux-vdso"):
                continue
            if "=> not found" in stripped:
                raise SecurityError(f"toolchain has an unresolved runtime library: {stripped}")
            candidate: str | None = None
            if "=>" in stripped:
                candidate = stripped.split("=>", 1)[1].strip().split(" ", 1)[0]
            elif stripped.startswith("/"):
                candidate = stripped.split(" ", 1)[0]
            if candidate is None:
                # Statically resolved pseudo-libraries have no host path.
                continue
            destination = Path(candidate)
            if not destination.is_absolute() or "\x00" in candidate:
                raise SecurityError("ldd returned an unsafe runtime library path")
            try:
                source = destination.resolve(strict=True)
            except OSError as exc:
                raise SecurityError(f"runtime library disappeared: {destination}") from exc
            if not source.is_file():
                raise SecurityError(f"runtime library is not a regular file: {source}")
            mounts[str(destination)] = {
                "source": str(source),
                "destination": str(destination),
                "sha256": _sha256_file(source),
            }
    if not mounts:
        raise SecurityError("toolchain ELF files exposed no auditable runtime libraries")
    return [mounts[key] for key in sorted(mounts)], []


def _pi_runtime_mounts(
    node: Path, elf_files: Sequence[Path]
) -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    """Return Pi's ELF closure plus exact distro-externalized Node builtins."""

    runtime_mounts, runtime_symlinks = _runtime_library_mounts((node, *elf_files))
    mounts = {item["destination"]: item for item in runtime_mounts}
    if node == Path("/usr/bin/node"):
        for destination in _NODE_EXTERNALIZED_BUILTIN_PATHS:
            if destination.is_symlink():
                raise SecurityError(
                    f"Node externalized builtin must not be a symbolic link: {destination}"
                )
            if not destination.exists():
                continue
            record = _stable_regular_record(
                destination,
                "Node externalized builtin",
                require_sealed=True,
            )
            mounts[str(destination)] = {
                "source": str(destination),
                "destination": str(destination),
                "sha256": record["sha256"],
            }
    return [mounts[key] for key in sorted(mounts)], runtime_symlinks


def _assert_mount_separation(
    mounts: Sequence[str | Path], forbidden_paths: Sequence[Path]
) -> None:
    for raw_mount in mounts:
        mount = Path(raw_mount).resolve(strict=True)
        if mount == Path("/"):
            raise SecurityError("bubblewrap must not mount the host root")
        for forbidden in forbidden_paths:
            if _is_within(forbidden, mount) or _is_within(mount, forbidden):
                raise SecurityError(
                    f"sandbox mount overlaps forbidden control path: {mount}"
                )


def _directory_flags(paths: Sequence[Path], *, under_tmp: bool) -> list[str]:
    directories: set[Path] = set()
    for path in paths:
        current = path
        while current != Path("/"):
            if (current == Path("/tmp") or _is_within(current, Path("/tmp"))) != under_tmp:
                current = current.parent
                continue
            if current != Path("/tmp"):
                directories.add(current)
            current = current.parent
    flags: list[str] = []
    for directory in sorted(directories, key=lambda item: (len(item.parts), str(item))):
        flags.extend(("--dir", str(directory)))
    return flags


def _private_directory_record(raw: Path | str, label: str) -> dict[str, Any]:
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink():
        raise SecurityError(f"{label} must not be a symbolic link")
    directory = _safe_absolute_directory(lexical, label)
    info = directory.stat(follow_symlinks=False)
    if info.st_uid != os.geteuid() or stat.S_IMODE(info.st_mode) & 0o077:
        raise SecurityError(f"{label} must be owned by the Harness uid and private")
    if os.path.ismount(directory):
        raise SecurityError(f"{label} must not itself be a mountpoint")
    return {
        "source": str(directory),
        "device": info.st_dev,
        "inode": info.st_ino,
        "mode": stat.S_IMODE(info.st_mode),
    }


def _private_socket_record(raw: Path | str) -> dict[str, Any]:
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink() or lexical.name in {"", ".", ".."}:
        raise SecurityError("broker socket must be a non-symlink named path")
    parent = _private_directory_record(lexical.parent, "broker socket directory")
    canonical = Path(parent["source"]) / lexical.name
    try:
        info = canonical.stat(follow_symlinks=False)
    except OSError as exc:
        raise SecurityError(f"cannot stat broker socket: {exc}") from exc
    if not stat.S_ISSOCK(info.st_mode):
        raise SecurityError("broker endpoint must be a Unix-domain socket")
    if info.st_uid != os.geteuid() or stat.S_IMODE(info.st_mode) & 0o077:
        raise SecurityError("broker socket must be owned by the Harness uid and private")
    try:
        names = sorted(item.name for item in os.scandir(Path(parent["source"])))
    except OSError as exc:
        raise SecurityError(f"cannot enumerate broker socket directory: {exc}") from exc
    if names != [lexical.name]:
        raise SecurityError("broker socket directory must contain only the broker socket")
    return {
        "directory_source": parent["source"],
        "directory_device": parent["device"],
        "directory_inode": parent["inode"],
        "directory_mode": parent["mode"],
        "destination": str(SANDBOX_PI_BROKER_ROOT),
        "socket_name": lexical.name,
        "socket_device": info.st_dev,
        "socket_inode": info.st_ino,
        "socket_mode": stat.S_IMODE(info.st_mode),
    }


def _validate_runtime_mount_records(value: Any) -> list[dict[str, str]]:
    if not isinstance(value, list) or not value:
        raise SecurityError("sandbox runtime library closure must be nonempty")
    destinations: set[str] = set()
    for item in value:
        if not isinstance(item, dict) or set(item) != {"source", "destination", "sha256"}:
            raise SecurityError("sandbox runtime library record has an invalid shape")
        source = item.get("source")
        destination = item.get("destination")
        digest = item.get("sha256")
        if (
            not isinstance(source, str)
            or not Path(source).is_absolute()
            or not isinstance(destination, str)
            or not Path(destination).is_absolute()
            or destination in destinations
            or not isinstance(digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        ):
            raise SecurityError("sandbox runtime library record is invalid")
        if Path(destination) in {Path("/bin"), Path("/usr/bin"), Path("/usr/local/bin")}:
            raise SecurityError("sandbox runtime library destination is executable search space")
        destinations.add(destination)
    return value


def _pi_input_record(
    *, role: str, raw: Path | str, expected_sha256: str
) -> dict[str, Any]:
    if role not in _PI_ALLOWED_INPUT_DESTINATIONS:
        raise SecurityError("unknown Pi sealed-input role")
    if re.fullmatch(r"[0-9a-f]{64}", expected_sha256) is None:
        raise SecurityError(f"Pi {role} digest must be lowercase SHA-256")
    lexical = Path(raw).expanduser().absolute()
    if lexical.is_symlink():
        raise SecurityError(f"Pi {role} must not be a symbolic link")
    path = lexical.resolve(strict=True)
    record = _stable_regular_record(
        path,
        f"Pi {role}",
        require_sealed=True,
    )
    if record["sha256"] != expected_sha256:
        raise SecurityError(f"Pi {role} digest mismatch")
    return {
        "source": str(path),
        "destination": str(_PI_ALLOWED_INPUT_DESTINATIONS[role]),
        "sha256": record["sha256"],
        "size_bytes": record["size_bytes"],
    }


def _validated_node_attestation(value: Mapping[str, Any]) -> dict[str, Any]:
    """Validate the exact Node record carried by the sealed install manifest."""

    required = {
        "path",
        "sha256",
        "size_bytes",
        "mode",
        "minimum_version",
        "version",
    }
    if not isinstance(value, Mapping) or set(value) != required:
        raise SecurityError("manifest-attested Node record has an invalid shape")
    path = value.get("path")
    digest = value.get("sha256")
    size_bytes = value.get("size_bytes")
    mode = value.get("mode")
    minimum_version = value.get("minimum_version")
    version = value.get("version")
    version_match = (
        re.fullmatch(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)", version)
        if isinstance(version, str)
        else None
    )
    minimum_parts = tuple(int(part) for part in PI_MINIMUM_NODE_VERSION.split("."))
    if (
        not isinstance(path, str)
        or not path
        or "\x00" in path
        or not Path(path).is_absolute()
        or os.path.normpath(path) != path
        or not isinstance(digest, str)
        or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        or isinstance(size_bytes, bool)
        or not isinstance(size_bytes, int)
        or size_bytes < 0
        or isinstance(mode, bool)
        or not isinstance(mode, int)
        or mode < 0
        or mode > 0o7777
        or mode & 0o111 == 0
        or minimum_version != PI_MINIMUM_NODE_VERSION
        or version_match is None
        or tuple(int(part) for part in version_match.groups()) < minimum_parts
    ):
        raise SecurityError("manifest-attested Node record is invalid")
    return {
        "path": path,
        "sha256": digest,
        "size_bytes": size_bytes,
        "mode": mode,
        "minimum_version": minimum_version,
        "version": version,
    }


def _validate_pi_bwrap_spec(spec: Any) -> dict[str, Any]:
    required = {
        "kind",
        "profile_version",
        "bwrap",
        "node",
        "install",
        "inputs",
        "tmpfs_limits",
        "broker",
        "runtime_mounts",
        "runtime_symlinks",
        "forbidden_host_paths",
    }
    if not isinstance(spec, dict) or set(spec) != required:
        raise SecurityError("Pi bubblewrap capability has an invalid shape")
    if spec["kind"] != "pi-bubblewrap" or spec["profile_version"] != PI_BWRAP_PROFILE_VERSION:
        raise SecurityError("unsupported Pi sandbox profile")
    for name, destination in (
        ("bwrap", None),
        ("node", str(SANDBOX_PI_NODE)),
    ):
        record = spec[name]
        fields = (
            {"source", "sha256"}
            if destination is None
            else {
                "source",
                "destination",
                "sha256",
                "size_bytes",
                "mode",
                "minimum_version",
                "version",
            }
        )
        if not isinstance(record, dict) or set(record) != fields:
            raise SecurityError(f"Pi sandbox {name} record has an invalid shape")
        if not isinstance(record["source"], str) or not Path(record["source"]).is_absolute():
            raise SecurityError(f"Pi sandbox {name} source is invalid")
        if re.fullmatch(r"[0-9a-f]{64}", record.get("sha256", "")) is None:
            raise SecurityError(f"Pi sandbox {name} digest is invalid")
        if destination is not None and record["destination"] != destination:
            raise SecurityError(f"Pi sandbox {name} destination is not fixed")
        if destination is not None and (
            isinstance(record["size_bytes"], bool)
            or not isinstance(record["size_bytes"], int)
            or record["size_bytes"] < 0
            or isinstance(record["mode"], bool)
            or not isinstance(record["mode"], int)
            or record["mode"] < 0
            or record["mode"] > 0o7777
            or record["mode"] & 0o111 == 0
            or record["minimum_version"] != PI_MINIMUM_NODE_VERSION
            or not isinstance(record["version"], str)
            or re.fullmatch(
                r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)",
                record["version"],
            )
            is None
            or tuple(int(part) for part in record["version"].split("."))
            < tuple(int(part) for part in PI_MINIMUM_NODE_VERSION.split("."))
        ):
            raise SecurityError(f"Pi sandbox {name} identity is invalid")
    install_required = {
        "source",
        "destination",
        "tree_sha256",
        "entry_count",
        "cli_relative",
        "cli_resolved_relative",
        "cli_sha256",
    }
    install = spec["install"]
    if not isinstance(install, dict) or set(install) != install_required:
        raise SecurityError("Pi installation record has an invalid shape")
    if (
        not isinstance(install["source"], str)
        or not Path(install["source"]).is_absolute()
        or install["destination"] != str(SANDBOX_PI_INSTALL_ROOT)
        or re.fullmatch(r"[0-9a-f]{64}", install.get("tree_sha256", "")) is None
        or not isinstance(install["entry_count"], int)
        or isinstance(install["entry_count"], bool)
        or install["entry_count"] < 1
        or re.fullmatch(r"[0-9a-f]{64}", install.get("cli_sha256", "")) is None
    ):
        raise SecurityError("Pi installation record is invalid")
    for name in ("cli_relative", "cli_resolved_relative"):
        if not isinstance(install.get(name), str):
            raise SecurityError("Pi CLI path is invalid")
        normalize_relative(install[name])
    inputs = spec["inputs"]
    if not isinstance(inputs, dict) or set(inputs) != set(_PI_ALLOWED_INPUT_DESTINATIONS):
        raise SecurityError("Pi sealed inputs have an invalid shape")
    for role, record in inputs.items():
        if (
            not isinstance(record, dict)
            or set(record) != {"source", "destination", "sha256", "size_bytes"}
            or not isinstance(record["source"], str)
            or not Path(record["source"]).is_absolute()
            or record["destination"] != str(_PI_ALLOWED_INPUT_DESTINATIONS[role])
            or re.fullmatch(r"[0-9a-f]{64}", record.get("sha256", "")) is None
            or not isinstance(record["size_bytes"], int)
            or isinstance(record["size_bytes"], bool)
            or record["size_bytes"] < 0
        ):
            raise SecurityError(f"Pi sealed {role} record is invalid")
    tmpfs_limits = spec["tmpfs_limits"]
    if (
        not isinstance(tmpfs_limits, dict)
        or set(tmpfs_limits) != {"runtime_bytes", "tmp_bytes", "run_bytes"}
        or any(
            isinstance(tmpfs_limits[name], bool)
            or not isinstance(tmpfs_limits[name], int)
            or tmpfs_limits[name] < 4096
            or tmpfs_limits[name] > 1024 * 1024 * 1024
            for name in ("runtime_bytes", "tmp_bytes", "run_bytes")
        )
    ):
        raise SecurityError("Pi tmpfs limits are invalid")
    broker = spec["broker"]
    broker_required = {
        "directory_source",
        "directory_device",
        "directory_inode",
        "directory_mode",
        "destination",
        "socket_name",
        "socket_device",
        "socket_inode",
        "socket_mode",
    }
    if (
        not isinstance(broker, dict)
        or set(broker) != broker_required
        or not isinstance(broker["directory_source"], str)
        or not Path(broker["directory_source"]).is_absolute()
        or broker["destination"] != str(SANDBOX_PI_BROKER_ROOT)
        or not isinstance(broker["socket_name"], str)
        or broker["socket_name"] in {"", ".", ".."}
        or "/" in broker["socket_name"]
        or any(
            not isinstance(broker[name], int)
            for name in (
                "directory_device",
                "directory_inode",
                "directory_mode",
                "socket_device",
                "socket_inode",
                "socket_mode",
            )
        )
    ):
        raise SecurityError("Pi broker socket record is invalid")
    _validate_runtime_mount_records(spec["runtime_mounts"])
    if spec["runtime_symlinks"] != []:
        raise SecurityError("Pi sandbox does not permit runtime symlink mounts")
    forbidden = spec["forbidden_host_paths"]
    if (
        not isinstance(forbidden, list)
        or any(not isinstance(item, str) or not Path(item).is_absolute() for item in forbidden)
    ):
        raise SecurityError("Pi forbidden-host-path record is invalid")
    return spec


def audit_pi_bubblewrap(
    *,
    configured_path: str | None,
    expected_node_attestation: Mapping[str, Any],
    install_root: Path | str,
    cli_relative: str,
    expected_install_tree_sha256: str,
    extension_path: Path | str,
    extension_sha256: str,
    public_config_path: Path | str,
    public_config_sha256: str,
    system_prompt_path: Path | str,
    system_prompt_sha256: str,
    settings_path: Path | str,
    settings_sha256: str,
    broker_socket: Path | str,
    forbidden_paths: Sequence[Path] = (),
    runtime_tmpfs_bytes: int = 64 * 1024 * 1024,
    tmp_tmpfs_bytes: int = 64 * 1024 * 1024,
    run_tmpfs_bytes: int = 1024 * 1024,
) -> dict[str, Any]:
    """Attest the minimal host closure exposed to one Pi process."""

    if sys.platform != "linux":
        raise SecurityError("Pi requires audited bubblewrap on Linux")
    if not configured_path or not configured_path.strip():
        raise SecurityError("HARNESS_PI_BWRAP must configure bubblewrap explicitly")
    lexical_bwrap = Path(configured_path).expanduser().absolute()
    if lexical_bwrap.is_symlink():
        raise SecurityError("configured bubblewrap must not be a symbolic link")
    bwrap = lexical_bwrap.resolve(strict=True)
    bwrap_record = _stable_regular_record(
        bwrap,
        "bubblewrap",
        require_sealed=True,
        require_executable=True,
    )
    expected_node = _validated_node_attestation(expected_node_attestation)
    lexical_node = Path(expected_node["path"])
    if lexical_node.is_symlink():
        raise SecurityError("configured Node executable must not be a symbolic link")
    node = lexical_node.resolve(strict=True)
    if node != lexical_node:
        raise SecurityError("manifest-attested Node path must not traverse symbolic links")
    node_record = _stable_regular_record(
        node,
        "Node executable",
        require_sealed=True,
        require_executable=True,
    )
    if not node_record["elf"]:
        raise SecurityError("configured Node executable must be native ELF")
    if any(
        node_record[name] != expected_node[name]
        for name in ("sha256", "size_bytes", "mode")
    ):
        raise SecurityError("Node executable differs from the sealed install manifest")

    install = _safe_absolute_directory(install_root, "Pi installation")
    if re.fullmatch(r"[0-9a-f]{64}", expected_install_tree_sha256) is None:
        raise SecurityError("Pi installation digest must be lowercase SHA-256")
    tree_digest, entry_count, elf_files = _pi_install_tree_attestation(install)
    if tree_digest != expected_install_tree_sha256:
        raise SecurityError("Pi installation tree digest mismatch")
    normalized_cli = normalize_relative(cli_relative)
    lexical_cli = install / Path(*PurePosixPath(normalized_cli).parts)
    try:
        resolved_cli = lexical_cli.resolve(strict=True)
        resolved_cli_relative = resolved_cli.relative_to(install).as_posix()
    except (OSError, ValueError) as exc:
        raise SecurityError("Pi CLI resolves outside its attested installation") from exc
    cli_record = _stable_regular_record(
        resolved_cli,
        "Pi CLI",
        require_sealed=True,
    )

    inputs = {
        "extension": _pi_input_record(
            role="extension", raw=extension_path, expected_sha256=extension_sha256
        ),
        "public_config": _pi_input_record(
            role="public_config",
            raw=public_config_path,
            expected_sha256=public_config_sha256,
        ),
        "system_prompt": _pi_input_record(
            role="system_prompt",
            raw=system_prompt_path,
            expected_sha256=system_prompt_sha256,
        ),
        "settings": _pi_input_record(
            role="settings",
            raw=settings_path,
            expected_sha256=settings_sha256,
        ),
    }
    broker = _private_socket_record(broker_socket)

    runtime_mounts, runtime_symlinks = _pi_runtime_mounts(node, elf_files)
    if runtime_symlinks:
        raise SecurityError("Pi runtime library closure must not require host symlinks")
    forbidden = sorted(
        {
            str(_safe_absolute_existing_path(item, "forbidden host path"))
            for item in forbidden_paths
        }
    )
    forbidden_resolved = [Path(item) for item in forbidden]
    source_mounts = [
        bwrap,
        node,
        install,
        *(Path(item["source"]) for item in inputs.values()),
        Path(broker["directory_source"]),
        *(Path(item["source"]) for item in runtime_mounts),
    ]
    _assert_mount_separation(source_mounts, forbidden_resolved)
    spec: dict[str, Any] = {
        "kind": "pi-bubblewrap",
        "profile_version": PI_BWRAP_PROFILE_VERSION,
        "bwrap": {"source": str(bwrap), "sha256": bwrap_record["sha256"]},
        "node": {
            "source": str(node),
            "destination": str(SANDBOX_PI_NODE),
            "sha256": node_record["sha256"],
            "size_bytes": node_record["size_bytes"],
            "mode": node_record["mode"],
            "minimum_version": expected_node["minimum_version"],
            "version": expected_node["version"],
        },
        "install": {
            "source": str(install),
            "destination": str(SANDBOX_PI_INSTALL_ROOT),
            "tree_sha256": tree_digest,
            "entry_count": entry_count,
            "cli_relative": normalized_cli,
            "cli_resolved_relative": resolved_cli_relative,
            "cli_sha256": cli_record["sha256"],
        },
        "inputs": inputs,
        "tmpfs_limits": {
            "runtime_bytes": runtime_tmpfs_bytes,
            "tmp_bytes": tmp_tmpfs_bytes,
            "run_bytes": run_tmpfs_bytes,
        },
        "broker": broker,
        "runtime_mounts": runtime_mounts,
        "runtime_symlinks": [],
        "forbidden_host_paths": forbidden,
    }
    return _validate_pi_bwrap_spec(spec)


def _revalidate_private_directory(record: dict[str, Any], label: str) -> Path:
    current = _private_directory_record(record["source"], label)
    for name in ("source", "device", "inode", "mode"):
        if current[name] != record[name]:
            raise SecurityError(f"{label} identity changed after attestation")
    return Path(current["source"])


def _pi_base_bwrap_argv(spec: dict[str, Any], broker_token: str) -> list[str]:
    destinations = [
        SANDBOX_PI_NODE.parent,
        SANDBOX_PI_INSTALL_ROOT,
        *(Path(item["destination"]).parent for item in spec["inputs"].values()),
        *(Path(item["destination"]).parent for item in spec["runtime_mounts"]),
    ]
    argv = [
        spec["bwrap"]["source"],
        "--unshare-all",
        "--share-net",
        "--unshare-user",
        "--die-with-parent",
        "--new-session",
        "--disable-userns",
        "--cap-drop",
        "ALL",
        "--clearenv",
        *_directory_flags(destinations, under_tmp=False),
    ]
    for item in spec["runtime_mounts"]:
        argv.extend(("--ro-bind", item["source"], item["destination"]))
    argv.extend(
        (
            "--ro-bind",
            spec["node"]["source"],
            spec["node"]["destination"],
            "--ro-bind",
            spec["install"]["source"],
            spec["install"]["destination"],
        )
    )
    for role in _PI_ALLOWED_INPUT_DESTINATIONS:
        item = spec["inputs"][role]
        argv.extend(("--ro-bind", item["source"], item["destination"]))
    argv.extend(
        (
            "--dir",
            "/tmp",
            "--dir",
            str(SANDBOX_PI_RUNTIME_ROOT),
            "--dir",
            "/run",
            "--dir",
            "/proc",
            "--dir",
            "/dev",
            "--remount-ro",
            "/",
            "--size",
            str(spec["tmpfs_limits"]["tmp_bytes"]),
            "--tmpfs",
            "/tmp",
            "--dir",
            "/tmp/home",
            "--dir",
            "/tmp/cache",
            "--dir",
            "/tmp/config",
            "--size",
            str(spec["tmpfs_limits"]["runtime_bytes"]),
            "--tmpfs",
            str(SANDBOX_PI_RUNTIME_ROOT),
            "--size",
            str(spec["tmpfs_limits"]["run_bytes"]),
            "--tmpfs",
            "/run",
            "--dir",
            str(SANDBOX_PI_BROKER_ROOT),
            "--ro-bind",
            spec["broker"]["directory_source"],
            spec["broker"]["destination"],
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--setenv",
            "HOME",
            "/tmp/home",
            "--setenv",
            "XDG_CACHE_HOME",
            "/tmp/cache",
            "--setenv",
            "XDG_CONFIG_HOME",
            "/tmp/config",
            "--setenv",
            "TMPDIR",
            "/tmp",
            "--setenv",
            "PATH",
            "/nonexistent",
            "--setenv",
            "LANG",
            "C.UTF-8",
            "--setenv",
            "TZ",
            "UTC",
            "--setenv",
            "NO_COLOR",
            "1",
            "--setenv",
            "PI_CODING_AGENT_DIR",
            str(SANDBOX_PI_AGENT_ROOT),
            "--setenv",
            "HARNESS_PI_BROKER_SOCKET",
            str(SANDBOX_PI_BROKER_ROOT / spec["broker"]["socket_name"]),
            "--setenv",
            "HARNESS_PI_BROKER_TOKEN",
            broker_token,
            "--setenv",
            "HARNESS_PI_EXTENSION_PATH",
            str(_PI_ALLOWED_INPUT_DESTINATIONS["extension"]),
            "--setenv",
            "HARNESS_PI_PUBLIC_CONFIG_PATH",
            str(_PI_ALLOWED_INPUT_DESTINATIONS["public_config"]),
            "--setenv",
            "HARNESS_PI_SYSTEM_PROMPT_PATH",
            str(_PI_ALLOWED_INPUT_DESTINATIONS["system_prompt"]),
            "--remount-ro",
            "/proc",
            "--remount-ro",
            "/run",
            "--chdir",
            str(SANDBOX_PI_RUNTIME_ROOT),
        )
    )
    if "--bind" in argv:
        raise SecurityError("Pi sandbox must not expose a writable host bind")
    return argv


def bubblewrap_pi_argv(
    *, spec: Any, pi_arguments: Sequence[str], broker_token: str
) -> tuple[str, ...]:
    """Re-attest the Pi closure and return a shell-free bubblewrap argv."""

    sandbox = _validate_pi_bwrap_spec(spec)
    if isinstance(pi_arguments, (str, bytes)) or any(
        not isinstance(item, str) or "\x00" in item for item in pi_arguments
    ):
        raise SecurityError("Pi arguments must be a NUL-free argv sequence")
    try:
        token_bytes = broker_token.encode("utf-8", "strict") if isinstance(broker_token, str) else b""
    except UnicodeError as exc:
        raise SecurityError("broker token must be strict UTF-8") from exc
    if (
        not isinstance(broker_token, str)
        or len(token_bytes) < 32
        or len(token_bytes) > 4096
        or any(marker in broker_token for marker in ("\x00", "\n", "\r"))
    ):
        raise SecurityError("broker token must be a 32-4096 byte single-line secret")
    bwrap = Path(sandbox["bwrap"]["source"])
    if (
        bwrap.is_symlink()
        or _stable_regular_record(
            bwrap, "bubblewrap", require_sealed=True, require_executable=True
        )["sha256"]
        != sandbox["bwrap"]["sha256"]
    ):
        raise SecurityError("bubblewrap changed after Pi attestation")
    node = Path(sandbox["node"]["source"])
    node_record = _stable_regular_record(
        node, "Node executable", require_sealed=True, require_executable=True
    )
    if (
        not node_record["elf"]
        or any(
            node_record[name] != sandbox["node"][name]
            for name in ("sha256", "size_bytes", "mode")
        )
    ):
        raise SecurityError("Node changed after Pi attestation")
    install = _safe_absolute_directory(sandbox["install"]["source"], "Pi installation")
    tree_digest, entry_count, elf_files = _pi_install_tree_attestation(install)
    if (
        tree_digest != sandbox["install"]["tree_sha256"]
        or entry_count != sandbox["install"]["entry_count"]
    ):
        raise SecurityError("Pi installation changed after attestation")
    cli = install / Path(*PurePosixPath(sandbox["install"]["cli_relative"]).parts)
    try:
        resolved_cli = cli.resolve(strict=True)
        resolved_relative = resolved_cli.relative_to(install).as_posix()
    except (OSError, ValueError) as exc:
        raise SecurityError("Pi CLI identity escaped its installation") from exc
    if (
        resolved_relative != sandbox["install"]["cli_resolved_relative"]
        or _stable_regular_record(resolved_cli, "Pi CLI", require_sealed=True)["sha256"]
        != sandbox["install"]["cli_sha256"]
    ):
        raise SecurityError("Pi CLI changed after attestation")
    for role, item in sandbox["inputs"].items():
        current = _pi_input_record(
            role=role,
            raw=item["source"],
            expected_sha256=item["sha256"],
        )
        if current != item:
            raise SecurityError(f"Pi sealed {role} changed after attestation")
    current_broker = _private_socket_record(
        Path(sandbox["broker"]["directory_source"]) / sandbox["broker"]["socket_name"]
    )
    if current_broker != sandbox["broker"]:
        raise SecurityError("Pi broker socket changed after attestation")
    current_mounts, current_symlinks = _pi_runtime_mounts(node, elf_files)
    if current_mounts != sandbox["runtime_mounts"] or current_symlinks:
        raise SecurityError("Pi runtime library closure changed after attestation")
    for item in current_mounts:
        if _sha256_file(Path(item["source"])) != item["sha256"]:
            raise SecurityError("Pi runtime library changed after attestation")
    forbidden = [Path(item).resolve(strict=True) for item in sandbox["forbidden_host_paths"]]
    _assert_mount_separation(
        [
            bwrap,
            node,
            install,
            *(Path(item["source"]) for item in sandbox["inputs"].values()),
            Path(sandbox["broker"]["directory_source"]),
            *(Path(item["source"]) for item in current_mounts),
        ],
        forbidden,
    )
    cli_destination = SANDBOX_PI_INSTALL_ROOT / Path(
        *PurePosixPath(sandbox["install"]["cli_resolved_relative"]).parts
    )
    return tuple(
        (
            *_pi_base_bwrap_argv(sandbox, broker_token),
            str(SANDBOX_PI_NODE),
            str(cli_destination),
            *tuple(pi_arguments),
        )
    )


def _base_bwrap_argv(spec: dict[str, Any]) -> list[str]:
    runtime_mounts = spec["runtime_mounts"]
    toolchain = spec["toolchain"]
    destinations = [
        *(Path(item["destination"]).parent for item in runtime_mounts),
        Path(toolchain["destination"]),
    ]
    argv = [
        spec["bwrap_path"],
        "--unshare-all",
        "--unshare-user",
        "--die-with-parent",
        "--new-session",
        "--disable-userns",
        "--cap-drop",
        "ALL",
        "--clearenv",
        *_directory_flags(destinations, under_tmp=False),
    ]
    for item in runtime_mounts:
        argv.extend(("--ro-bind", item["source"], item["destination"]))
    argv.extend(
        (
            "--ro-bind",
            toolchain["source"],
            toolchain["destination"],
        )
    )
    for item in spec["runtime_symlinks"]:
        argv.extend(("--symlink", item["target"], item["linkpath"]))
    argv.extend(
        (
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--size",
            str(256 * 1024 * 1024),
            "--tmpfs",
            "/tmp",
            "--dir",
            "/tmp/harness-home",
            "--dir",
            "/tmp/harness-cache",
            "--dir",
            "/tmp/harness-config",
            "--setenv",
            "HOME",
            "/tmp/harness-home",
            "--setenv",
            "XDG_CACHE_HOME",
            "/tmp/harness-cache",
            "--setenv",
            "XDG_CONFIG_HOME",
            "/tmp/harness-config",
            "--setenv",
            "TMPDIR",
            "/tmp",
            "--setenv",
            "PATH",
            spec["path_env"],
            "--setenv",
            "LEAN_NUM_THREADS",
            "1",
            "--setenv",
            "LANG",
            "C.UTF-8",
            "--setenv",
            "TZ",
            "UTC",
            "--setenv",
            "NO_COLOR",
            "1",
        )
    )
    return argv


def _validate_bwrap_spec(spec: Any) -> dict[str, Any]:
    required = {
        "kind",
        "profile_version",
        "bwrap_path",
        "bwrap_sha256",
        "toolchain",
        "runtime_mounts",
        "runtime_symlinks",
        "path_env",
        "worktree",
        "worktree_entries",
        "lake_cache",
        "forbidden_host_paths",
    }
    if not isinstance(spec, dict) or set(spec) != required:
        raise SecurityError("bubblewrap capability has an invalid shape")
    if spec["kind"] != "bubblewrap" or spec["profile_version"] != BWRAP_PROFILE_VERSION:
        raise SecurityError("unsupported Lean sandbox profile")
    if (
        not isinstance(spec["bwrap_path"], str)
        or not Path(spec["bwrap_path"]).is_absolute()
        or not isinstance(spec["bwrap_sha256"], str)
        or re.fullmatch(r"[0-9a-f]{64}", spec["bwrap_sha256"]) is None
    ):
        raise SecurityError("sandbox bubblewrap identity is invalid")
    toolchain_required = {
        "source",
        "destination",
        "lake_host",
        "lake_sandbox",
        "lake_sha256",
        "lean_host",
        "lean_sandbox",
        "lean_sha256",
    }
    toolchain = spec["toolchain"]
    if not isinstance(toolchain, dict) or set(toolchain) != toolchain_required:
        raise SecurityError("sandbox toolchain identity has an invalid shape")
    if toolchain["destination"] != str(SANDBOX_TOOLCHAIN_ROOT):
        raise SecurityError("sandbox toolchain destination is not fixed")
    for name in ("source", "destination", "lake_host", "lake_sandbox", "lean_host", "lean_sandbox"):
        if not isinstance(toolchain[name], str) or not Path(toolchain[name]).is_absolute():
            raise SecurityError(f"sandbox toolchain {name} must be an absolute path")
    for name in ("lake_sha256", "lean_sha256"):
        if not isinstance(toolchain[name], str) or re.fullmatch(r"[0-9a-f]{64}", toolchain[name]) is None:
            raise SecurityError(f"sandbox toolchain {name} has an invalid digest")
    try:
        toolchain_source = Path(toolchain["source"])
        for name in ("lake", "lean"):
            relative = Path(toolchain[f"{name}_host"]).relative_to(toolchain_source)
            expected = Path(toolchain["destination"]) / relative
            if Path(toolchain[f"{name}_sandbox"]) != expected:
                raise SecurityError(f"sandbox toolchain {name} remap is inconsistent")
    except ValueError as exc:
        raise SecurityError("sandbox tool identity escapes its source root") from exc
    if not isinstance(spec["runtime_mounts"], list) or not spec["runtime_mounts"]:
        raise SecurityError("sandbox runtime_mounts must be nonempty")
    for item in spec["runtime_mounts"]:
        if not isinstance(item, dict) or set(item) != {"source", "destination", "sha256"}:
            raise SecurityError("sandbox runtime mount has an invalid shape")
        if any(
            not isinstance(item[key], str) or not Path(item[key]).is_absolute()
            for key in ("source", "destination")
        ):
            raise SecurityError("sandbox runtime mount paths must be absolute")
        if not isinstance(item["sha256"], str) or re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is None:
            raise SecurityError("sandbox runtime mount digest is invalid")
    if not isinstance(spec["runtime_symlinks"], list):
        raise SecurityError("sandbox runtime_symlinks must be an array")
    for item in spec["runtime_symlinks"]:
        if not isinstance(item, dict) or set(item) != {"target", "linkpath"}:
            raise SecurityError("sandbox runtime symlink has an invalid shape")
        if (
            not isinstance(item["target"], str)
            or not isinstance(item["linkpath"], str)
            or not Path(item["linkpath"]).is_absolute()
        ):
            raise SecurityError("sandbox runtime symlink is invalid")
    if not isinstance(spec["worktree_entries"], list):
        raise SecurityError("sandbox worktree_entries must be an array")
    for item in spec["worktree_entries"]:
        if (
            not isinstance(item, dict)
            or set(item) != {"name", "kind"}
            or not isinstance(item["name"], str)
            or "/" in item["name"]
            or item["name"] in {"", ".", "..", ".git", ".lake"}
            or not isinstance(item["kind"], str)
            or item["kind"] not in {"file", "directory"}
        ):
            raise SecurityError("sandbox worktree entry is invalid")
    if not isinstance(spec["forbidden_host_paths"], list):
        raise SecurityError("sandbox forbidden_host_paths must be an array")
    if any(
        not isinstance(item, str) or not Path(item).is_absolute()
        for item in spec["forbidden_host_paths"]
    ):
        raise SecurityError("sandbox forbidden host path is invalid")
    if not isinstance(spec["worktree"], str) or not Path(spec["worktree"]).is_absolute():
        raise SecurityError("sandbox worktree must be an absolute path")
    if spec["path_env"] != str(SANDBOX_TOOLCHAIN_ROOT / "bin"):
        raise SecurityError("sandbox PATH is not the fixed toolchain-only path")
    cache_required = {
        "source",
        "manifest_sha256",
        "cache_tree_sha256",
        "package_overrides_sha256",
        "metadata_fingerprint",
    }
    if not isinstance(spec["lake_cache"], dict) or set(spec["lake_cache"]) != cache_required:
        raise SecurityError("sandbox lake_cache has an invalid shape")
    if not isinstance(spec["lake_cache"]["source"], str) or not Path(spec["lake_cache"]["source"]).is_absolute():
        raise SecurityError("sandbox lake cache source must be absolute")
    for name in (
        "manifest_sha256",
        "cache_tree_sha256",
        "package_overrides_sha256",
        "metadata_fingerprint",
    ):
        value = spec["lake_cache"].get(name)
        if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
            raise SecurityError(f"sandbox lake cache {name} is invalid")
    return spec


def _safe_file_digest(root: Path, relative: str) -> str:
    path = resolve_repo_file(root, relative, must_exist=True)
    return _sha256_file(path)


def _cache_entries(
    root: Path,
    *,
    include_content: bool,
) -> tuple[str, int]:
    """Audit a frozen cache and return a deterministic digest and entry count."""

    if root.is_symlink() or not root.is_dir():
        raise SecurityError("immutable Lake cache must be a real directory")
    root_stat = root.stat(follow_symlinks=False)
    if root_stat.st_mode & 0o222:
        raise SecurityError("immutable Lake cache root is writable")
    digest = hashlib.sha256()
    digest.update(
        b"poincare-lake-cache-tree-v1\0"
        if include_content
        else b"poincare-lake-cache-metadata-v1\0"
    )
    count = 0
    pending: list[tuple[Path, PurePosixPath]] = [(root, PurePosixPath("."))]
    while pending:
        directory, relative_directory = pending.pop()
        try:
            entries = sorted(os.scandir(directory), key=lambda item: item.name)
        except OSError as exc:
            raise SecurityError(f"cannot enumerate immutable Lake cache: {exc}") from exc
        child_directories: list[tuple[Path, PurePosixPath]] = []
        for entry in entries:
            if entry.name == CACHE_MANIFEST_NAME:
                if relative_directory == PurePosixPath("."):
                    continue
            if entry.name == ".git":
                raise SecurityError("immutable Lake cache contains forbidden .git metadata")
            if "\n" in entry.name or "\r" in entry.name:
                raise SecurityError("immutable Lake cache contains an unsafe filename")
            relative = (
                PurePosixPath(entry.name)
                if relative_directory == PurePosixPath(".")
                else relative_directory / entry.name
            )
            try:
                info = entry.stat(follow_symlinks=False)
            except OSError as exc:
                raise SecurityError(f"cannot stat Lake cache entry {relative}: {exc}") from exc
            mode = info.st_mode
            if stat.S_ISLNK(mode):
                raise SecurityError(f"immutable Lake cache contains a symlink: {relative}")
            if mode & 0o222:
                raise SecurityError(f"immutable Lake cache contains a writable entry: {relative}")
            encoded = relative.as_posix().encode("utf-8")
            if stat.S_ISDIR(mode):
                kind = b"D"
                child_directories.append((Path(entry.path), relative))
            elif stat.S_ISREG(mode):
                kind = b"F"
                if info.st_nlink != 1:
                    raise SecurityError(f"immutable Lake cache contains a hard-linked file: {relative}")
            else:
                raise SecurityError(f"immutable Lake cache contains a special file: {relative}")
            digest.update(kind)
            digest.update(len(encoded).to_bytes(8, "big"))
            digest.update(encoded)
            digest.update(stat.S_IMODE(mode).to_bytes(4, "big"))
            digest.update(info.st_size.to_bytes(8, "big"))
            if include_content and kind == b"F":
                digest.update(bytes.fromhex(_sha256_file(Path(entry.path))))
            else:
                digest.update(info.st_dev.to_bytes(8, "big"))
                digest.update(info.st_ino.to_bytes(8, "big"))
                digest.update(info.st_mtime_ns.to_bytes(8, "big", signed=True))
            count += 1
        pending.extend(reversed(child_directories))
    return digest.hexdigest(), count


def lake_cache_tree_digest(cache: Path) -> str:
    """Compute the content digest stored in a frozen cache manifest."""

    root = _safe_absolute_directory(cache, "immutable Lake cache")
    digest, _ = _cache_entries(root, include_content=True)
    return digest


def _package_override_payload(worktree: Path) -> dict[str, Any]:
    manifest_path = resolve_repo_file(worktree, "lake-manifest.json", must_exist=True)
    try:
        raw = manifest_path.read_bytes()
    except OSError as exc:
        raise SecurityError(f"cannot read lake-manifest.json: {exc}") from exc
    if len(raw) > 1024 * 1024:
        raise SecurityError("lake-manifest.json exceeds its byte cap")
    try:
        manifest = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SecurityError("lake-manifest.json is not valid JSON") from exc
    if (
        not isinstance(manifest, dict)
        or manifest.get("version") != "1.1.0"
        or manifest.get("packagesDir") != ".lake/packages"
        or manifest.get("lakeDir") != ".lake"
        or not isinstance(manifest.get("packages"), list)
        or not manifest["packages"]
        or len(manifest["packages"]) > 256
    ):
        raise SecurityError("lake-manifest.json is not the supported Lake 1.1.0 layout")
    overrides: list[dict[str, Any]] = []
    seen: set[str] = set()
    preserved = ("name", "scope", "inherited", "configFile", "manifestFile")
    for package in manifest["packages"]:
        if not isinstance(package, dict) or package.get("type") != "git":
            raise SecurityError("package overrides require Git entries in lake-manifest.json")
        if any(name not in package for name in preserved):
            raise SecurityError("lake-manifest package is missing an override field")
        name = package["name"]
        if (
            not isinstance(name, str)
            or re.fullmatch(r"[A-Za-z0-9_.-]+", name) is None
            or name in seen
        ):
            raise SecurityError("lake-manifest package name is unsafe or duplicated")
        seen.add(name)
        if not isinstance(package["scope"], str) or len(package["scope"]) > 256:
            raise SecurityError("lake-manifest package scope is invalid")
        if not isinstance(package["inherited"], bool):
            raise SecurityError("lake-manifest package inherited flag is invalid")
        config_file = package["configFile"]
        if not isinstance(config_file, str):
            raise SecurityError("lake-manifest package configFile is invalid")
        normalize_relative(config_file)
        manifest_file = package["manifestFile"]
        if manifest_file is not None:
            if not isinstance(manifest_file, str):
                raise SecurityError("lake-manifest package manifestFile is invalid")
            normalize_relative(manifest_file)
        overrides.append(
            {
                "type": "path",
                "dir": str(SANDBOX_WORKTREE_ROOT / ".lake" / "packages" / name),
                **{field: package[field] for field in preserved},
            }
        )
    return {"version": "1.1.0", "packages": overrides}


def canonical_package_overrides(worktree: Path) -> bytes:
    """Render the only package-override file accepted by the sandbox."""

    root = _safe_absolute_directory(worktree, "Job worktree")
    return (
        json.dumps(
            _package_override_payload(root),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
        + "\n"
    ).encode("ascii")


def _validate_package_overrides(cache: Path, worktree: Path) -> str:
    path = cache / PACKAGE_OVERRIDES_NAME
    if path.is_symlink() or not path.is_file():
        raise SecurityError(f"immutable Lake cache is missing {PACKAGE_OVERRIDES_NAME}")
    if path.stat(follow_symlinks=False).st_mode & 0o222:
        raise SecurityError("immutable Lake package overrides are writable")
    expected = canonical_package_overrides(worktree)
    try:
        actual = path.read_bytes()
    except OSError as exc:
        raise SecurityError(f"cannot read immutable Lake package overrides: {exc}") from exc
    if actual != expected:
        raise SecurityError("immutable Lake package overrides are not canonical for this Job")
    payload = _package_override_payload(worktree)
    for package in payload["packages"]:
        package_dir = cache / "packages" / package["name"]
        if package_dir.is_symlink() or not package_dir.is_dir():
            raise SecurityError(f"immutable Lake cache is missing package {package['name']}")
    return hashlib.sha256(actual).hexdigest()


def _load_cache_manifest(
    cache: Path,
    *,
    worktree: Path,
    base_commit: str,
    base_tree: str,
) -> tuple[dict[str, Any], str]:
    manifest_path = cache / CACHE_MANIFEST_NAME
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise SecurityError(f"immutable Lake cache is missing {CACHE_MANIFEST_NAME}")
    if manifest_path.stat(follow_symlinks=False).st_mode & 0o222:
        raise SecurityError("immutable Lake cache manifest is writable")
    try:
        raw = manifest_path.read_bytes()
    except OSError as exc:
        raise SecurityError(f"cannot read immutable Lake cache manifest: {exc}") from exc
    if len(raw) > 16 * 1024:
        raise SecurityError("immutable Lake cache manifest exceeds its byte cap")
    try:
        manifest = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SecurityError("immutable Lake cache manifest is not valid JSON") from exc
    required = {
        "schema_version",
        "base_commit",
        "base_tree",
        "cache_tree_sha256",
        "package_overrides_sha256",
        "lean_toolchain_sha256",
        "lake_manifest_sha256",
    }
    if not isinstance(manifest, dict) or set(manifest) != required:
        raise SecurityError("immutable Lake cache manifest has an invalid shape")
    if manifest["schema_version"] != CACHE_MANIFEST_VERSION:
        raise SecurityError("immutable Lake cache manifest version is unsupported")
    if manifest["base_commit"] != base_commit:
        raise SecurityError("immutable Lake cache is for a different base commit")
    if manifest["base_tree"] != base_tree:
        raise SecurityError("immutable Lake cache is for a different Git tree")
    for name in (
        "cache_tree_sha256",
        "package_overrides_sha256",
        "lean_toolchain_sha256",
        "lake_manifest_sha256",
    ):
        if not isinstance(manifest[name], str) or re.fullmatch(r"[0-9a-f]{64}", manifest[name]) is None:
            raise SecurityError(f"immutable Lake cache manifest {name} is invalid")
    if manifest["lean_toolchain_sha256"] != _safe_file_digest(worktree, "lean-toolchain"):
        raise SecurityError("immutable Lake cache has the wrong Lean toolchain binding")
    if manifest["lake_manifest_sha256"] != _safe_file_digest(worktree, "lake-manifest.json"):
        raise SecurityError("immutable Lake cache has the wrong lake-manifest binding")
    return manifest, hashlib.sha256(raw).hexdigest()


def _worktree_entries(root: Path) -> list[dict[str, str]]:
    """Validate everything exposed by per-top-level binds."""

    records: list[dict[str, str]] = []
    try:
        top_entries = sorted(os.scandir(root), key=lambda item: item.name)
    except OSError as exc:
        raise SecurityError(f"cannot enumerate worktree: {exc}") from exc
    for top in top_entries:
        if top.name in {".git", ".lake"}:
            continue
        if "\n" in top.name or "\r" in top.name:
            raise SecurityError("worktree contains an unsafe top-level filename")
        try:
            top_info = top.stat(follow_symlinks=False)
        except OSError as exc:
            raise SecurityError(f"cannot stat worktree entry {top.name}: {exc}") from exc
        if stat.S_ISDIR(top_info.st_mode):
            kind = "directory"
        elif stat.S_ISREG(top_info.st_mode):
            kind = "file"
        else:
            raise SecurityError(f"worktree top-level entry is not bind-safe: {top.name}")
        records.append({"name": top.name, "kind": kind})
        if kind != "directory":
            continue
        pending = [Path(top.path)]
        while pending:
            directory = pending.pop()
            try:
                entries = list(os.scandir(directory))
            except OSError as exc:
                raise SecurityError(f"cannot enumerate worktree tree: {exc}") from exc
            for entry in entries:
                if entry.name == ".git":
                    raise SecurityError("worktree bind tree contains nested .git metadata")
                try:
                    info = entry.stat(follow_symlinks=False)
                except OSError as exc:
                    raise SecurityError(f"cannot stat worktree bind entry: {exc}") from exc
                if stat.S_ISDIR(info.st_mode):
                    pending.append(Path(entry.path))
                elif not stat.S_ISREG(info.st_mode):
                    raise SecurityError(f"worktree bind tree contains a symlink or special file: {entry.path}")
    if not records:
        raise SecurityError("worktree has no bind-safe project entries")
    return records


def _toolchain_record(raw_roots: str | None) -> dict[str, str]:
    roots = [] if raw_roots is None else [item for item in raw_roots.split(os.pathsep) if item.strip()]
    if len(roots) != 1:
        raise SecurityError("HARNESS_PI_TOOLCHAIN_ROOTS must name exactly one Lean toolchain root")
    source = _safe_absolute_directory(roots[0], "Lean toolchain root")
    if source == Path("/") or source in {Path("/usr"), Path("/home"), Path("/srv")}:
        raise SecurityError("Lean toolchain root is overly broad")
    record: dict[str, str] = {
        "source": str(source),
        "destination": str(SANDBOX_TOOLCHAIN_ROOT),
    }
    for name in ("lake", "lean"):
        lexical = source / "bin" / name
        try:
            resolved = lexical.resolve(strict=True)
            resolved.relative_to(source)
        except (OSError, ValueError) as exc:
            raise SecurityError(f"toolchain {name} does not resolve inside the configured root") from exc
        if not resolved.is_file() or not os.access(resolved, os.X_OK):
            raise SecurityError(f"toolchain {name} is not executable")
        try:
            with resolved.open("rb") as stream:
                magic = stream.read(4)
        except OSError as exc:
            raise SecurityError(f"cannot inspect toolchain {name}: {exc}") from exc
        if magic != b"\x7fELF":
            raise SecurityError(f"toolchain {name} must be a native ELF executable")
        sandbox_path = SANDBOX_TOOLCHAIN_ROOT / resolved.relative_to(source)
        record[f"{name}_host"] = str(resolved)
        record[f"{name}_sandbox"] = str(sandbox_path)
        record[f"{name}_sha256"] = _sha256_file(resolved)
    return record


def audit_bubblewrap(
    *,
    configured_path: str | None,
    control_root: Path,
    worktree: Path,
    forbidden_paths: Sequence[Path],
    extra_toolchain_roots: str | None = None,
    immutable_lake_cache: Path | None = None,
    base_commit: str | None = None,
    base_tree: str | None = None,
) -> dict[str, Any]:
    if sys.platform != "linux":
        raise SecurityError("Lean checks require audited bubblewrap on Linux")
    if not configured_path or not configured_path.strip():
        raise SecurityError("HARNESS_PI_BWRAP must configure the audited bubblewrap binary")
    lexical_bwrap = Path(configured_path).expanduser().absolute()
    if lexical_bwrap.is_symlink() or not lexical_bwrap.is_file() or not os.access(lexical_bwrap, os.X_OK):
        raise SecurityError("configured bubblewrap must be an executable non-symlink file")
    bwrap = lexical_bwrap.resolve(strict=True)
    if not isinstance(base_commit, str) or re.fullmatch(r"[0-9a-f]{40}", base_commit) is None:
        raise SecurityError("Lean sandbox requires the exact 40-hex base commit")
    if not isinstance(base_tree, str) or re.fullmatch(r"[0-9a-f]{40}", base_tree) is None:
        raise SecurityError("Lean sandbox requires the exact 40-hex base tree")
    root = _safe_absolute_directory(worktree, "Job worktree")
    control = _safe_absolute_directory(control_root, "Harness control root")
    if root == control or _is_within(root, control) or _is_within(control, root):
        raise SecurityError("Job worktree must be isolated from the Harness control root")
    git_marker = root / ".git"
    if not git_marker.exists() and not git_marker.is_symlink():
        raise SecurityError("Job worktree has no Git marker")
    entries = _worktree_entries(root)

    if immutable_lake_cache is None:
        raise SecurityError("HARNESS_PI_LAKE_CACHE_ROOT must provide a frozen cache snapshot")
    cache = _safe_absolute_directory(immutable_lake_cache, "immutable Lake cache")
    if cache.name != base_commit:
        raise SecurityError("immutable Lake cache path is not keyed by the base commit")
    for required_cache_entry in ("packages", "build", "config"):
        candidate = cache / required_cache_entry
        if candidate.is_symlink() or not candidate.is_dir():
            raise SecurityError(
                f"immutable Lake cache lacks prebuilt {required_cache_entry}/"
            )
    manifest, manifest_sha256 = _load_cache_manifest(
        cache,
        worktree=root,
        base_commit=base_commit,
        base_tree=base_tree,
    )
    package_overrides_sha256 = _validate_package_overrides(cache, root)
    if package_overrides_sha256 != manifest["package_overrides_sha256"]:
        raise SecurityError("immutable Lake package override digest mismatch")
    cache_tree_sha256, _ = _cache_entries(cache, include_content=True)
    if cache_tree_sha256 != manifest["cache_tree_sha256"]:
        raise SecurityError("immutable Lake cache content digest mismatch")
    metadata_fingerprint, _ = _cache_entries(cache, include_content=False)

    toolchain = _toolchain_record(extra_toolchain_roots)
    runtime_mounts, runtime_symlinks = _runtime_library_mounts(
        (Path(toolchain["lake_host"]), Path(toolchain["lean_host"]))
    )
    forbidden = sorted(
        {
            str(control),
            str(root),
            *(str(_safe_absolute_existing_path(item, "forbidden host path")) for item in forbidden_paths),
        }
    )
    forbidden_resolved = [Path(item) for item in forbidden]
    source_mounts = [
        *(Path(item["source"]) for item in runtime_mounts),
        Path(toolchain["source"]),
        cache,
    ]
    _assert_mount_separation(source_mounts, forbidden_resolved)
    spec: dict[str, Any] = {
        "kind": "bubblewrap",
        "profile_version": BWRAP_PROFILE_VERSION,
        "bwrap_path": str(bwrap),
        "bwrap_sha256": _sha256_file(bwrap),
        "toolchain": toolchain,
        "runtime_mounts": runtime_mounts,
        "runtime_symlinks": runtime_symlinks,
        "path_env": str(SANDBOX_TOOLCHAIN_ROOT / "bin"),
        "worktree": str(root),
        "worktree_entries": entries,
        "lake_cache": {
            "source": str(cache),
            "manifest_sha256": manifest_sha256,
            "cache_tree_sha256": cache_tree_sha256,
            "package_overrides_sha256": package_overrides_sha256,
            "metadata_fingerprint": metadata_fingerprint,
        },
        "forbidden_host_paths": forbidden,
    }
    _validate_bwrap_spec(spec)
    with tempfile.NamedTemporaryFile(prefix="harness-pi-preflight-", suffix=".lean") as source:
        source.write(b"theorem harness_bwrap_preflight : True := by trivial\n")
        source.flush()
        preflight = _build_bwrap_argv(
            spec,
            root,
            inner=(
                toolchain["lake_sandbox"],
                f"--packages={SANDBOX_WORKTREE_ROOT / '.lake' / PACKAGE_OVERRIDES_NAME}",
                "env",
                toolchain["lean_sandbox"],
                "/tmp/harness-preflight.lean",
            ),
            preflight_source=Path(source.name),
        )
        result = run_limited(
            preflight,
            cwd=root,
            env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"},
            timeout_seconds=30,
            output_limit_bytes=64 * 1024,
            supervise_parent=True,
        )
    if result.returncode != 0 or result.timed_out or result.output_limited:
        error = result.stderr.decode("utf-8", "replace").strip()
        raise SecurityError(f"bubblewrap namespace preflight failed: {error or result.returncode}")
    return spec


def _build_bwrap_argv(
    sandbox: dict[str, Any],
    root: Path,
    *,
    inner: Sequence[str],
    preflight_source: Path | None = None,
) -> tuple[str, ...]:
    argv = _base_bwrap_argv(sandbox)
    argv.extend(_directory_flags([SANDBOX_WORKTREE_ROOT], under_tmp=False))
    for item in sandbox["worktree_entries"]:
        source = root / item["name"]
        destination = SANDBOX_WORKTREE_ROOT / item["name"]
        argv.extend(("--ro-bind", str(source), str(destination)))
    cache = Path(sandbox["lake_cache"]["source"])
    argv.extend(("--ro-bind", str(cache), str(SANDBOX_WORKTREE_ROOT / ".lake")))
    if preflight_source is not None:
        argv.extend(
            (
                "--ro-bind",
                str(preflight_source),
                "/tmp/harness-preflight.lean",
            )
        )
    argv.extend(
        (
            "--remount-ro",
            "/proc",
            "--remount-ro",
            "/",
            "--chdir",
            str(SANDBOX_WORKTREE_ROOT),
            *inner,
        )
    )
    return tuple(argv)


def bubblewrap_lean_argv(
    *, spec: Any, worktree: Path, command: Sequence[str]
) -> tuple[str, ...]:
    sandbox = _validate_bwrap_spec(spec)
    bwrap = Path(sandbox["bwrap_path"])
    if bwrap.is_symlink() or not bwrap.is_file() or _sha256_file(bwrap) != sandbox["bwrap_sha256"]:
        raise SecurityError("bubblewrap binary changed after Job launch")
    toolchain = sandbox["toolchain"]
    source = _safe_absolute_directory(toolchain["source"], "Lean toolchain root")
    for name in ("lake", "lean"):
        host = Path(toolchain[f"{name}_host"])
        try:
            host.resolve(strict=True).relative_to(source)
        except (OSError, ValueError) as exc:
            raise SecurityError(f"toolchain {name} identity escaped its root") from exc
        if not host.is_file() or _sha256_file(host) != toolchain[f"{name}_sha256"]:
            raise SecurityError(f"toolchain {name} changed after Job launch")
    current_mounts, current_symlinks = _runtime_library_mounts(
        (Path(toolchain["lake_host"]), Path(toolchain["lean_host"]))
    )
    if current_mounts != sandbox["runtime_mounts"] or current_symlinks != sandbox["runtime_symlinks"]:
        raise SecurityError("runtime library mount set changed after Job launch")
    for item in current_mounts:
        if _sha256_file(Path(item["source"])) != item["sha256"]:
            raise SecurityError("runtime library changed after Job launch")
    forbidden = [Path(item).resolve(strict=True) for item in sandbox["forbidden_host_paths"]]
    cache = _safe_absolute_directory(sandbox["lake_cache"]["source"], "immutable Lake cache")
    _assert_mount_separation(
        [
            *(Path(item["source"]) for item in sandbox["runtime_mounts"]),
            source,
            cache,
        ],
        forbidden,
    )
    manifest_path = cache / CACHE_MANIFEST_NAME
    if (
        manifest_path.is_symlink()
        or not manifest_path.is_file()
        or _sha256_file(manifest_path) != sandbox["lake_cache"]["manifest_sha256"]
    ):
        raise SecurityError("immutable Lake cache manifest changed after Job launch")
    overrides_path = cache / PACKAGE_OVERRIDES_NAME
    if (
        overrides_path.is_symlink()
        or not overrides_path.is_file()
        or _sha256_file(overrides_path)
        != sandbox["lake_cache"]["package_overrides_sha256"]
    ):
        raise SecurityError("immutable Lake package overrides changed after Job launch")
    metadata_fingerprint, _ = _cache_entries(cache, include_content=False)
    if metadata_fingerprint != sandbox["lake_cache"]["metadata_fingerprint"]:
        raise SecurityError("immutable Lake cache metadata changed after Job launch")
    root = worktree.resolve(strict=True)
    if str(root) != sandbox["worktree"] or str(root) not in sandbox["forbidden_host_paths"]:
        raise SecurityError("sandbox worktree identity mismatch")
    git_marker = root / ".git"
    if not git_marker.exists() and not git_marker.is_symlink():
        raise SecurityError("sandbox worktree has no Git marker")
    if _worktree_entries(root) != sandbox["worktree_entries"]:
        raise SecurityError("sandbox worktree top-level layout changed after Job launch")
    normalized = lean_acceptance_argv(command)
    inner = (
        toolchain["lake_sandbox"],
        f"--packages={SANDBOX_WORKTREE_ROOT / '.lake' / PACKAGE_OVERRIDES_NAME}",
        "env",
        toolchain["lean_sandbox"],
        normalized[3],
    )
    return _build_bwrap_argv(sandbox, root, inner=inner)


SPARSE_LEAN_SNAPSHOT_VERSION = "poincare-sparse-lean-snapshot-v1"


def _run_snapshot_git(git: Path, worktree: Path, arguments: Sequence[str]) -> int:
    result = run_limited(
        (str(git), "-C", str(worktree), *arguments),
        cwd=worktree,
        env={"PATH": "/nonexistent", "LANG": "C", "LC_ALL": "C"},
        timeout_seconds=15,
        output_limit_bytes=64 * 1024,
        supervise_parent=sys.platform == "linux",
    )
    if result.timed_out or result.output_limited or result.guard_cancelled:
        raise SecurityError("Git path audit exceeded its execution bound")
    return result.returncode


def _audit_sparse_source_path(
    *, git: Path, worktree: Path, relative: str
) -> tuple[Path, dict[str, Any]]:
    normalized = normalize_relative(relative)
    if any(
        re.fullmatch(r"[A-Za-z0-9_.-]+", part) is None
        for part in PurePosixPath(normalized).parts
    ):
        raise SecurityError(f"sparse Lean source path is not Git-literal-safe: {normalized}")
    source = resolve_repo_file(worktree, normalized, must_exist=True)
    current = worktree
    for part in PurePosixPath(normalized).parts:
        current = current / part
        if current.is_symlink():
            raise SecurityError(f"sparse Lean source contains a symlink: {normalized}")
        if os.path.ismount(current):
            raise SecurityError(f"sparse Lean source crosses a mountpoint: {normalized}")
    tracked = _run_snapshot_git(
        git, worktree, ("ls-files", "--error-unmatch", "--", normalized)
    )
    if tracked != 0:
        raise SecurityError(f"sparse Lean source is not Git-tracked: {normalized}")
    ignored = _run_snapshot_git(
        git,
        worktree,
        ("check-ignore", "--no-index", "--quiet", "--", normalized),
    )
    if ignored == 0:
        raise SecurityError(f"sparse Lean source is ignored: {normalized}")
    if ignored != 1:
        raise SecurityError(f"Git could not determine ignore status: {normalized}")
    return source, _stable_regular_record(
        source,
        f"sparse Lean source {normalized}",
        require_sealed=False,
    )


def _remove_partial_sparse_snapshot(root: Path) -> None:
    if not root.exists() or root.is_symlink():
        return
    for directory, child_directories, _ in os.walk(root, topdown=False):
        for name in child_directories:
            try:
                (Path(directory) / name).chmod(0o700)
            except OSError:
                pass
        try:
            Path(directory).chmod(0o700)
        except OSError:
            pass
    shutil.rmtree(root, ignore_errors=True)


def _copy_attested_sparse_file(
    source: Path,
    destination: Path,
    *,
    expected: dict[str, Any],
    label: str,
) -> dict[str, Any]:
    destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    source_flags = os.O_RDONLY
    destination_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_CLOEXEC"):
        source_flags |= os.O_CLOEXEC
        destination_flags |= os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        source_flags |= os.O_NOFOLLOW
        destination_flags |= os.O_NOFOLLOW
    try:
        source_fd = os.open(source, source_flags)
    except OSError as exc:
        raise SecurityError(f"cannot reopen {label}: {exc}") from exc
    destination_fd: int | None = None
    try:
        before = os.fstat(source_fd)
        identity = {
            "size_bytes": before.st_size,
            "mode": stat.S_IMODE(before.st_mode),
            "device": before.st_dev,
            "inode": before.st_ino,
            "mtime_ns": before.st_mtime_ns,
            "ctime_ns": before.st_ctime_ns,
        }
        if any(identity[name] != expected[name] for name in identity):
            raise SecurityError(f"{label} changed before snapshot copy")
        destination_fd = os.open(destination, destination_flags, 0o400)
        digest = hashlib.sha256()
        copied = 0
        while True:
            chunk = os.read(source_fd, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            copied += len(chunk)
            view = memoryview(chunk)
            while view:
                written = os.write(destination_fd, view)
                if written < 1:
                    raise SecurityError(f"could not finish copying {label}")
                view = view[written:]
        os.fsync(destination_fd)
        after = os.fstat(source_fd)
        after_identity = {
            "size_bytes": after.st_size,
            "mode": stat.S_IMODE(after.st_mode),
            "device": after.st_dev,
            "inode": after.st_ino,
            "mtime_ns": after.st_mtime_ns,
            "ctime_ns": after.st_ctime_ns,
        }
        if (
            copied != expected["size_bytes"]
            or digest.hexdigest() != expected["sha256"]
            or after_identity != identity
        ):
            raise SecurityError(f"{label} changed during snapshot copy")
    finally:
        if destination_fd is not None:
            os.close(destination_fd)
        os.close(source_fd)
    destination.chmod(0o444)
    return {
        "sha256": expected["sha256"],
        "size_bytes": expected["size_bytes"],
    }


def _snapshot_file_records(root: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    pending = [root]
    while pending:
        directory = pending.pop()
        try:
            entries = sorted(os.scandir(directory), key=lambda item: item.name.encode("utf-8"))
        except (OSError, UnicodeEncodeError) as exc:
            raise SecurityError(f"cannot enumerate sparse Lean snapshot: {exc}") from exc
        for entry in entries:
            path = Path(entry.path)
            relative = path.relative_to(root).as_posix()
            info = entry.stat(follow_symlinks=False)
            if os.path.ismount(path):
                raise SecurityError(f"sparse Lean snapshot contains a mountpoint: {relative}")
            if stat.S_ISDIR(info.st_mode):
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                record = _stable_regular_record(
                    path,
                    f"sparse Lean snapshot file {relative}",
                    require_sealed=True,
                )
                records.append(
                    {
                        "path": relative,
                        "sha256": record["sha256"],
                        "size_bytes": record["size_bytes"],
                    }
                )
            else:
                raise SecurityError(f"sparse Lean snapshot contains a symlink or special file: {relative}")
    return sorted(records, key=lambda item: item["path"])


def build_sparse_lean_snapshot(
    *,
    worktree: Path | str,
    acceptance_commands: Sequence[Sequence[str]],
    output_dir: Path | str,
    git_path: Path | str = Path("/usr/bin/git"),
) -> dict[str, Any]:
    """Copy only recorded Lean targets and exact Lake configuration into a sealed tree."""

    root = _safe_absolute_directory(worktree, "Job worktree")
    if not acceptance_commands:
        raise SecurityError("sparse Lean snapshot requires at least one acceptance command")
    targets = sorted({lean_acceptance_argv(command)[3] for command in acceptance_commands})
    required = sorted({*targets, "lakefile.lean", "lake-manifest.json", "lean-toolchain"})
    lexical_output = Path(output_dir).expanduser().absolute()
    if lexical_output.exists() or lexical_output.is_symlink():
        raise SecurityError("sparse Lean snapshot destination must not already exist")
    try:
        output_parent = lexical_output.parent.resolve(strict=True)
    except OSError as exc:
        raise SecurityError(f"cannot resolve sparse snapshot parent: {exc}") from exc
    destination = output_parent / lexical_output.name
    if destination in {Path("/"), Path("/tmp"), Path("/var/tmp"), Path("/run")}:
        raise SecurityError("sparse Lean snapshot destination is overly broad")
    if _is_within(destination, root) or _is_within(root, destination):
        raise SecurityError("sparse Lean snapshot must be isolated from the worktree")
    lexical_git = Path(git_path).expanduser().absolute()
    if lexical_git.is_symlink():
        raise SecurityError("snapshot Git executable must not be a symbolic link")
    git = lexical_git.resolve(strict=True)
    _stable_regular_record(
        git,
        "snapshot Git executable",
        require_sealed=True,
        require_executable=True,
    )
    audited: dict[str, tuple[Path, dict[str, Any]]] = {}
    for relative in required:
        audited[relative] = _audit_sparse_source_path(
            git=git,
            worktree=root,
            relative=relative,
        )
    try:
        destination.mkdir(mode=0o700)
        (destination / ".lake").mkdir(mode=0o700)
        files: list[dict[str, Any]] = []
        for relative in required:
            source, record = audited[relative]
            copied = _copy_attested_sparse_file(
                source,
                destination / Path(*PurePosixPath(relative).parts),
                expected=record,
                label=f"sparse Lean source {relative}",
            )
            files.append({"path": relative, **copied})
        directories = [destination]
        directories.extend(
            Path(directory)
            for directory, _, _ in os.walk(destination)
            if Path(directory) != destination
        )
        for directory in sorted(directories, key=lambda item: len(item.parts), reverse=True):
            directory.chmod(0o555)
        tree_sha256, entry_count, _ = _sealed_tree_attestation(
            destination,
            "sparse Lean snapshot",
            require_sealed=True,
            allow_internal_symlinks=False,
        )
    except BaseException:
        _remove_partial_sparse_snapshot(destination)
        raise
    return {
        "schema_version": SPARSE_LEAN_SNAPSHOT_VERSION,
        "root": str(destination),
        "tree_sha256": tree_sha256,
        "entry_count": entry_count,
        "targets": targets,
        "files": sorted(files, key=lambda item: item["path"]),
    }


def _validate_sparse_snapshot_manifest(value: Any) -> dict[str, Any]:
    required = {
        "schema_version",
        "root",
        "tree_sha256",
        "entry_count",
        "targets",
        "files",
    }
    if not isinstance(value, dict) or set(value) != required:
        raise SecurityError("sparse Lean snapshot manifest has an invalid shape")
    if (
        value["schema_version"] != SPARSE_LEAN_SNAPSHOT_VERSION
        or not isinstance(value["root"], str)
        or not Path(value["root"]).is_absolute()
        or re.fullmatch(r"[0-9a-f]{64}", value.get("tree_sha256", "")) is None
        or not isinstance(value["entry_count"], int)
        or isinstance(value["entry_count"], bool)
        or value["entry_count"] < 4
        or not isinstance(value["targets"], list)
        or not value["targets"]
        or not isinstance(value["files"], list)
    ):
        raise SecurityError("sparse Lean snapshot manifest is invalid")
    targets: list[str] = []
    for target in value["targets"]:
        if not isinstance(target, str):
            raise SecurityError("sparse Lean target is invalid")
        normalized = normalize_relative(target)
        if normalized != target or not target.endswith(".lean"):
            raise SecurityError("sparse Lean target is invalid")
        targets.append(target)
    if targets != sorted(set(targets)):
        raise SecurityError("sparse Lean targets must be unique and sorted")
    expected_paths = sorted({*targets, "lakefile.lean", "lake-manifest.json", "lean-toolchain"})
    actual_paths: list[str] = []
    for record in value["files"]:
        if (
            not isinstance(record, dict)
            or set(record) != {"path", "sha256", "size_bytes"}
            or not isinstance(record["path"], str)
            or normalize_relative(record["path"]) != record["path"]
            or re.fullmatch(r"[0-9a-f]{64}", record.get("sha256", "")) is None
            or not isinstance(record["size_bytes"], int)
            or isinstance(record["size_bytes"], bool)
            or record["size_bytes"] < 0
        ):
            raise SecurityError("sparse Lean snapshot file record is invalid")
        actual_paths.append(record["path"])
    if actual_paths != expected_paths:
        raise SecurityError("sparse Lean snapshot exposes files outside its exact target set")
    return value


def _revalidate_sparse_snapshot(value: Any) -> tuple[dict[str, Any], Path]:
    manifest = _validate_sparse_snapshot_manifest(value)
    root = _safe_absolute_directory(manifest["root"], "sparse Lean snapshot")
    digest, count, _ = _sealed_tree_attestation(
        root,
        "sparse Lean snapshot",
        require_sealed=True,
        allow_internal_symlinks=False,
    )
    if digest != manifest["tree_sha256"] or count != manifest["entry_count"]:
        raise SecurityError("sparse Lean snapshot tree changed after creation")
    if _snapshot_file_records(root) != manifest["files"]:
        raise SecurityError("sparse Lean snapshot files changed after creation")
    return manifest, root


def remove_sparse_lean_snapshot(
    *, sparse_snapshot: Any, checks_root: Path | str
) -> None:
    """Remove one re-attested snapshot contained by the private checks root."""

    _manifest, snapshot_root = _revalidate_sparse_snapshot(sparse_snapshot)
    scratch = Path(
        _private_directory_record(checks_root, "Lean checks scratch root")["source"]
    )
    if snapshot_root == scratch or not _is_within(snapshot_root, scratch):
        raise SecurityError("sparse Lean snapshot is outside its checks scratch root")
    relative = snapshot_root.relative_to(scratch)
    if not relative.parts or any(part in {"", ".", ".."} for part in relative.parts):
        raise SecurityError("sparse Lean snapshot cleanup target is invalid")
    _remove_partial_sparse_snapshot(snapshot_root)
    if snapshot_root.exists() or snapshot_root.is_symlink():
        raise SecurityError("sparse Lean snapshot cleanup did not complete")


def _sparse_toolchain_record(raw_roots: str | None) -> tuple[dict[str, Any], tuple[Path, ...]]:
    roots = [] if raw_roots is None else [item for item in raw_roots.split(os.pathsep) if item.strip()]
    if len(roots) != 1:
        raise SecurityError("HARNESS_PI_TOOLCHAIN_ROOTS must name exactly one Lean toolchain root")
    root = _safe_absolute_directory(roots[0], "Lean toolchain root")
    if root in {Path("/"), Path("/usr"), Path("/home"), Path("/srv")}:
        raise SecurityError("Lean toolchain root is overly broad")
    result: dict[str, Any] = {}
    executables: list[Path] = []
    for name in ("lake", "lean"):
        lexical = root / "bin" / name
        try:
            resolved = lexical.resolve(strict=True)
            resolved.relative_to(root)
        except (OSError, ValueError) as exc:
            raise SecurityError(f"toolchain {name} escaped its configured root") from exc
        record = _stable_regular_record(
            resolved,
            f"toolchain {name}",
            require_sealed=False,
            require_executable=True,
        )
        if not record["elf"]:
            raise SecurityError(f"toolchain {name} must be native ELF")
        result[name] = {
            "source": str(resolved),
            "destination": str(SANDBOX_TOOLCHAIN_ROOT / "bin" / name),
            "sha256": record["sha256"],
        }
        executables.append(resolved)
    compiler_lib = _safe_absolute_directory(root / "lib" / "lean", "Lean compiler library")
    try:
        compiler_lib.relative_to(root)
    except ValueError as exc:
        raise SecurityError("Lean compiler library escaped its configured root") from exc
    lib_digest, lib_count, lib_elf = _sealed_tree_attestation(
        compiler_lib,
        "Lean compiler library",
        require_sealed=False,
        allow_internal_symlinks=True,
    )
    result["compiler_lib"] = {
        "source": str(compiler_lib),
        "destination": str(SANDBOX_TOOLCHAIN_ROOT / "lib" / "lean"),
        "tree_sha256": lib_digest,
        "entry_count": lib_count,
    }
    return result, tuple((*executables, *lib_elf))


def _validate_resource_settings(value: Any) -> dict[str, Any]:
    required = {
        "memory_max_bytes",
        "memory_swap_max_bytes",
        "tasks_max",
        "cpu_quota_percent",
        "rlimits",
    }
    if not isinstance(value, dict) or set(value) != required:
        raise SecurityError("Lean resource settings have an invalid shape")
    for name in ("memory_max_bytes", "tasks_max"):
        if isinstance(value[name], bool) or not isinstance(value[name], int) or value[name] < 1:
            raise SecurityError(f"Lean resource setting {name} is invalid")
    if value["memory_swap_max_bytes"] != 0:
        raise SecurityError("Lean sandbox must disable swap")
    quota = value["cpu_quota_percent"]
    if isinstance(quota, bool) or not isinstance(quota, (int, float)) or quota <= 0 or quota > 1000:
        raise SecurityError("Lean CPU quota is invalid")
    ProcessResourceLimits.from_mapping(value["rlimits"])
    return value


def _validate_sparse_lean_bwrap_spec(spec: Any) -> dict[str, Any]:
    required = {
        "kind",
        "profile_version",
        "bwrap",
        "systemd_run",
        "snapshot",
        "lake_cache",
        "toolchain",
        "runtime_mounts",
        "runtime_symlinks",
        "resources",
        "forbidden_host_paths",
    }
    if not isinstance(spec, dict) or set(spec) != required:
        raise SecurityError("sparse Lean sandbox capability has an invalid shape")
    if (
        spec["kind"] != "sparse-lean-bubblewrap"
        or spec["profile_version"] != SPARSE_LEAN_BWRAP_PROFILE_VERSION
    ):
        raise SecurityError("unsupported sparse Lean sandbox profile")
    for key in ("bwrap", "systemd_run"):
        record = spec[key]
        if (
            not isinstance(record, dict)
            or set(record) != {"source", "sha256"}
            or not isinstance(record["source"], str)
            or not Path(record["source"]).is_absolute()
            or re.fullmatch(r"[0-9a-f]{64}", record.get("sha256", "")) is None
        ):
            raise SecurityError(f"sparse Lean {key} identity is invalid")
    _validate_sparse_snapshot_manifest(spec["snapshot"])
    cache = spec["lake_cache"]
    cache_required = {
        "source",
        "manifest_sha256",
        "tree_sha256",
        "package_overrides_sha256",
        "base_commit",
        "base_tree",
    }
    if not isinstance(cache, dict) or set(cache) != cache_required:
        raise SecurityError("sparse Lean cache identity has an invalid shape")
    if not isinstance(cache["source"], str) or not Path(cache["source"]).is_absolute():
        raise SecurityError("sparse Lean cache source is invalid")
    for name in ("manifest_sha256", "tree_sha256", "package_overrides_sha256"):
        if re.fullmatch(r"[0-9a-f]{64}", cache.get(name, "")) is None:
            raise SecurityError(f"sparse Lean cache {name} is invalid")
    for name in ("base_commit", "base_tree"):
        if re.fullmatch(r"[0-9a-f]{40}", cache.get(name, "")) is None:
            raise SecurityError(f"sparse Lean cache {name} is invalid")
    toolchain = spec["toolchain"]
    if not isinstance(toolchain, dict) or set(toolchain) != {"lake", "lean", "compiler_lib"}:
        raise SecurityError("sparse Lean toolchain identity has an invalid shape")
    for name in ("lake", "lean"):
        record = toolchain[name]
        if (
            not isinstance(record, dict)
            or set(record) != {"source", "destination", "sha256"}
            or not isinstance(record["source"], str)
            or not Path(record["source"]).is_absolute()
            or record["destination"] != str(SANDBOX_TOOLCHAIN_ROOT / "bin" / name)
            or re.fullmatch(r"[0-9a-f]{64}", record.get("sha256", "")) is None
        ):
            raise SecurityError(f"sparse Lean toolchain {name} identity is invalid")
    compiler = toolchain["compiler_lib"]
    if (
        not isinstance(compiler, dict)
        or set(compiler) != {"source", "destination", "tree_sha256", "entry_count"}
        or not isinstance(compiler["source"], str)
        or not Path(compiler["source"]).is_absolute()
        or compiler["destination"] != str(SANDBOX_TOOLCHAIN_ROOT / "lib" / "lean")
        or re.fullmatch(r"[0-9a-f]{64}", compiler.get("tree_sha256", "")) is None
        or not isinstance(compiler["entry_count"], int)
        or isinstance(compiler["entry_count"], bool)
        or compiler["entry_count"] < 1
    ):
        raise SecurityError("sparse Lean compiler library identity is invalid")
    _validate_runtime_mount_records(spec["runtime_mounts"])
    if spec["runtime_symlinks"] != []:
        raise SecurityError("sparse Lean sandbox does not permit runtime symlink mounts")
    _validate_resource_settings(spec["resources"])
    forbidden = spec["forbidden_host_paths"]
    if (
        not isinstance(forbidden, list)
        or any(not isinstance(item, str) or not Path(item).is_absolute() for item in forbidden)
    ):
        raise SecurityError("sparse Lean forbidden-host paths are invalid")
    return spec


def audit_sparse_lean_bubblewrap(
    *,
    configured_path: str | None,
    systemd_run_path: Path | str,
    sparse_snapshot: dict[str, Any],
    immutable_lake_cache: Path | str,
    extra_toolchain_roots: str | None,
    forbidden_paths: Sequence[Path],
    base_commit: str,
    base_tree: str,
    memory_max_bytes: int,
    tasks_max: int,
    cpu_quota_percent: int | float,
    process_limits: ProcessResourceLimits | dict[str, int],
) -> dict[str, Any]:
    """Attest an exact sparse source/cache/toolchain closure for Lean."""

    if sys.platform != "linux":
        raise SecurityError("sparse Lean checks require Linux")
    if not configured_path or not configured_path.strip():
        raise SecurityError("HARNESS_PI_BWRAP must configure bubblewrap explicitly")
    identities: dict[str, dict[str, str]] = {}
    for key, raw, label in (
        ("bwrap", configured_path, "bubblewrap"),
        ("systemd_run", systemd_run_path, "systemd-run"),
    ):
        lexical = Path(raw).expanduser().absolute()
        if lexical.is_symlink():
            raise SecurityError(f"{label} must not be a symbolic link")
        path = lexical.resolve(strict=True)
        record = _stable_regular_record(
            path,
            label,
            require_sealed=True,
            require_executable=True,
        )
        if not record["elf"]:
            raise SecurityError(f"{label} must be native ELF")
        identities[key] = {"source": str(path), "sha256": record["sha256"]}
    snapshot_manifest, snapshot_root = _revalidate_sparse_snapshot(sparse_snapshot)
    if re.fullmatch(r"[0-9a-f]{40}", base_commit) is None:
        raise SecurityError("sparse Lean sandbox requires an exact base commit")
    if re.fullmatch(r"[0-9a-f]{40}", base_tree) is None:
        raise SecurityError("sparse Lean sandbox requires an exact base tree")
    cache = _safe_absolute_directory(immutable_lake_cache, "immutable Lake cache")
    if cache.name != base_commit:
        raise SecurityError("immutable Lake cache path is not keyed by the base commit")
    for name in ("packages", "build", "config"):
        child = cache / name
        if child.is_symlink() or not child.is_dir():
            raise SecurityError(f"immutable Lake cache lacks prebuilt {name}/")
    cache_manifest, cache_manifest_sha = _load_cache_manifest(
        cache,
        worktree=snapshot_root,
        base_commit=base_commit,
        base_tree=base_tree,
    )
    overrides_sha = _validate_package_overrides(cache, snapshot_root)
    if overrides_sha != cache_manifest["package_overrides_sha256"]:
        raise SecurityError("immutable Lake package override digest mismatch")
    cache_tree_sha, _ = _cache_entries(cache, include_content=True)
    if cache_tree_sha != cache_manifest["cache_tree_sha256"]:
        raise SecurityError("immutable Lake cache content digest mismatch")
    toolchain, toolchain_elf = _sparse_toolchain_record(extra_toolchain_roots)
    runtime_mounts, runtime_symlinks = _runtime_library_mounts(toolchain_elf)
    if runtime_symlinks:
        raise SecurityError("Lean runtime closure must not require host symlinks")
    forbidden = sorted(
        {
            str(_safe_absolute_existing_path(item, "forbidden host path"))
            for item in forbidden_paths
        }
    )
    sources = [
        identities["bwrap"]["source"],
        identities["systemd_run"]["source"],
        snapshot_root,
        cache,
        toolchain["lake"]["source"],
        toolchain["lean"]["source"],
        toolchain["compiler_lib"]["source"],
        *(item["source"] for item in runtime_mounts),
    ]
    _assert_mount_separation(sources, [Path(item) for item in forbidden])
    limits = ProcessResourceLimits.coerce(process_limits)
    resources = {
        "memory_max_bytes": memory_max_bytes,
        "memory_swap_max_bytes": 0,
        "tasks_max": tasks_max,
        "cpu_quota_percent": cpu_quota_percent,
        "rlimits": limits.as_dict(),
    }
    _validate_resource_settings(resources)
    spec: dict[str, Any] = {
        "kind": "sparse-lean-bubblewrap",
        "profile_version": SPARSE_LEAN_BWRAP_PROFILE_VERSION,
        **identities,
        "snapshot": snapshot_manifest,
        "lake_cache": {
            "source": str(cache),
            "manifest_sha256": cache_manifest_sha,
            "tree_sha256": cache_tree_sha,
            "package_overrides_sha256": overrides_sha,
            "base_commit": base_commit,
            "base_tree": base_tree,
        },
        "toolchain": toolchain,
        "runtime_mounts": runtime_mounts,
        "runtime_symlinks": [],
        "resources": resources,
        "forbidden_host_paths": forbidden,
    }
    return _validate_sparse_lean_bwrap_spec(spec)


def _sparse_lean_bwrap_inner(spec: dict[str, Any], target: str) -> tuple[str, ...]:
    destinations = [
        SANDBOX_TOOLCHAIN_ROOT / "bin",
        SANDBOX_TOOLCHAIN_ROOT / "lib" / "lean",
        SANDBOX_SPARSE_SOURCE_ROOT,
        *(Path(item["destination"]).parent for item in spec["runtime_mounts"]),
    ]
    argv = [
        spec["bwrap"]["source"],
        "--unshare-all",
        "--unshare-user",
        "--die-with-parent",
        "--new-session",
        "--disable-userns",
        "--cap-drop",
        "ALL",
        "--clearenv",
        *_directory_flags(destinations, under_tmp=False),
    ]
    for item in spec["runtime_mounts"]:
        argv.extend(("--ro-bind", item["source"], item["destination"]))
    toolchain = spec["toolchain"]
    for name in ("lake", "lean"):
        item = toolchain[name]
        argv.extend(("--ro-bind", item["source"], item["destination"]))
    compiler = toolchain["compiler_lib"]
    argv.extend(
        (
            "--ro-bind",
            compiler["source"],
            compiler["destination"],
            "--ro-bind",
            spec["snapshot"]["root"],
            str(SANDBOX_SPARSE_SOURCE_ROOT),
            "--ro-bind",
            spec["lake_cache"]["source"],
            str(SANDBOX_SPARSE_SOURCE_ROOT / ".lake"),
            "--size",
            str(256 * 1024 * 1024),
            "--tmpfs",
            "/tmp",
            "--dir",
            "/tmp/home",
            "--dir",
            "/tmp/cache",
            "--dir",
            "/tmp/config",
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--setenv",
            "HOME",
            "/tmp/home",
            "--setenv",
            "XDG_CACHE_HOME",
            "/tmp/cache",
            "--setenv",
            "XDG_CONFIG_HOME",
            "/tmp/config",
            "--setenv",
            "TMPDIR",
            "/tmp",
            "--setenv",
            "PATH",
            str(SANDBOX_TOOLCHAIN_ROOT / "bin"),
            "--setenv",
            "LEAN_NUM_THREADS",
            "1",
            "--setenv",
            "LANG",
            "C.UTF-8",
            "--setenv",
            "TZ",
            "UTC",
            "--setenv",
            "NO_COLOR",
            "1",
            "--remount-ro",
            "/proc",
            "--remount-ro",
            "/",
            "--chdir",
            str(SANDBOX_SPARSE_SOURCE_ROOT),
            toolchain["lake"]["destination"],
            f"--packages={SANDBOX_SPARSE_SOURCE_ROOT / '.lake' / PACKAGE_OVERRIDES_NAME}",
            "env",
            toolchain["lean"]["destination"],
            str(SANDBOX_SPARSE_SOURCE_ROOT / Path(*PurePosixPath(target).parts)),
        )
    )
    return tuple(argv)


def sparse_lean_process_limits(spec: Any) -> ProcessResourceLimits:
    sandbox = _validate_sparse_lean_bwrap_spec(spec)
    return ProcessResourceLimits.from_mapping(sandbox["resources"]["rlimits"])


def bubblewrap_sparse_lean_argv(
    *, spec: Any, command: Sequence[str]
) -> tuple[str, ...]:
    """Rehash the full sparse closure and return systemd-run plus bubblewrap argv."""

    sandbox = _validate_sparse_lean_bwrap_spec(spec)
    target = lean_acceptance_argv(command)[3]
    if target not in sandbox["snapshot"]["targets"]:
        raise SecurityError("Lean command target is absent from the recorded sparse snapshot")
    for name in ("bwrap", "systemd_run"):
        record = sandbox[name]
        path = Path(record["source"])
        current = _stable_regular_record(
            path,
            name.replace("_", "-"),
            require_sealed=True,
            require_executable=True,
        )
        if not current["elf"] or current["sha256"] != record["sha256"]:
            raise SecurityError(f"{name} changed after Lean attestation")
    _, snapshot_root = _revalidate_sparse_snapshot(sandbox["snapshot"])
    cache_record = sandbox["lake_cache"]
    cache = _safe_absolute_directory(cache_record["source"], "immutable Lake cache")
    manifest_path = cache / CACHE_MANIFEST_NAME
    if (
        manifest_path.is_symlink()
        or not manifest_path.is_file()
        or _sha256_file(manifest_path) != cache_record["manifest_sha256"]
    ):
        raise SecurityError("immutable Lake cache manifest changed after attestation")
    overrides_path = cache / PACKAGE_OVERRIDES_NAME
    if (
        overrides_path.is_symlink()
        or not overrides_path.is_file()
        or _sha256_file(overrides_path) != cache_record["package_overrides_sha256"]
    ):
        raise SecurityError("immutable Lake package overrides changed after attestation")
    cache_digest, _ = _cache_entries(cache, include_content=True)
    if cache_digest != cache_record["tree_sha256"]:
        raise SecurityError("immutable Lake cache content changed after attestation")
    toolchain = sandbox["toolchain"]
    toolchain_elf: list[Path] = []
    for name in ("lake", "lean"):
        record = toolchain[name]
        current = _stable_regular_record(
            Path(record["source"]),
            f"toolchain {name}",
            require_sealed=False,
            require_executable=True,
        )
        if not current["elf"] or current["sha256"] != record["sha256"]:
            raise SecurityError(f"toolchain {name} changed after attestation")
        toolchain_elf.append(Path(record["source"]))
    compiler = toolchain["compiler_lib"]
    compiler_root = _safe_absolute_directory(compiler["source"], "Lean compiler library")
    compiler_digest, compiler_count, compiler_elf = _sealed_tree_attestation(
        compiler_root,
        "Lean compiler library",
        require_sealed=False,
        allow_internal_symlinks=True,
    )
    if (
        compiler_digest != compiler["tree_sha256"]
        or compiler_count != compiler["entry_count"]
    ):
        raise SecurityError("Lean compiler library changed after attestation")
    current_mounts, current_symlinks = _runtime_library_mounts(
        (*toolchain_elf, *compiler_elf)
    )
    if current_mounts != sandbox["runtime_mounts"] or current_symlinks:
        raise SecurityError("Lean runtime library closure changed after attestation")
    for item in current_mounts:
        if _sha256_file(Path(item["source"])) != item["sha256"]:
            raise SecurityError("Lean runtime library changed after attestation")
    forbidden = [Path(item).resolve(strict=True) for item in sandbox["forbidden_host_paths"]]
    _assert_mount_separation(
        [
            snapshot_root,
            cache,
            *(Path(toolchain[name]["source"]) for name in ("lake", "lean")),
            compiler_root,
            *(Path(item["source"]) for item in current_mounts),
        ],
        forbidden,
    )
    resources = _validate_resource_settings(sandbox["resources"])
    quota = resources["cpu_quota_percent"]
    quota_text = str(int(quota)) if float(quota).is_integer() else str(quota)
    systemd_prefix = (
        sandbox["systemd_run"]["source"],
        "--user",
        "--scope",
        "--quiet",
        "--collect",
        f"--property=MemoryMax={resources['memory_max_bytes']}",
        f"--property=MemorySwapMax={resources['memory_swap_max_bytes']}",
        f"--property=TasksMax={resources['tasks_max']}",
        f"--property=CPUQuota={quota_text}%",
        "--",
    )
    return (*systemd_prefix, *_sparse_lean_bwrap_inner(sandbox, target))


@dataclass(frozen=True)
class ProcessResourceLimits:
    """Exact POSIX limits applied in the child before trusted execution."""

    address_space_bytes: int
    processes: int
    open_files: int
    file_size_bytes: int
    core_bytes: int
    cpu_seconds: int

    def __post_init__(self) -> None:
        values = self.as_dict()
        maximums = {
            "address_space_bytes": 1 << 50,
            "processes": 65536,
            "open_files": 1 << 20,
            "file_size_bytes": 1 << 50,
            "core_bytes": 1 << 40,
            "cpu_seconds": 86400,
        }
        for name, value in values.items():
            minimum = 0 if name == "core_bytes" else 1
            if (
                isinstance(value, bool)
                or not isinstance(value, int)
                or value < minimum
                or value > maximums[name]
            ):
                raise SecurityError(f"process resource limit {name} is invalid")

    def as_dict(self) -> dict[str, int]:
        return {
            "address_space_bytes": self.address_space_bytes,
            "processes": self.processes,
            "open_files": self.open_files,
            "file_size_bytes": self.file_size_bytes,
            "core_bytes": self.core_bytes,
            "cpu_seconds": self.cpu_seconds,
        }

    @classmethod
    def from_mapping(cls, value: Any) -> ProcessResourceLimits:
        fields = {
            "address_space_bytes",
            "processes",
            "open_files",
            "file_size_bytes",
            "core_bytes",
            "cpu_seconds",
        }
        if not isinstance(value, dict) or set(value) != fields:
            raise SecurityError("process resource limits have an invalid shape")
        return cls(**{name: value[name] for name in fields})

    @classmethod
    def coerce(
        cls, value: ProcessResourceLimits | dict[str, int]
    ) -> ProcessResourceLimits:
        if isinstance(value, cls):
            return value
        return cls.from_mapping(value)


@dataclass(frozen=True)
class LimitedProcessResult:
    argv: tuple[str, ...]
    returncode: int
    stdout: bytes
    stderr: bytes
    timed_out: bool
    output_limited: bool
    guard_cancelled: bool
    duration_seconds: float


def arm_parent_death_guard(expected_parent_pid: int) -> None:
    """Kill this process if its exact expected parent disappears."""

    if sys.platform != "linux" or _LIBC is None:
        raise SecurityError("parent-death supervision requires Linux prctl")
    if (
        isinstance(expected_parent_pid, bool)
        or not isinstance(expected_parent_pid, int)
        or expected_parent_pid <= 1
        or os.getppid() != expected_parent_pid
    ):
        raise SecurityError("parent-death guard has the wrong expected parent")
    # PR_SET_PDEATHSIG = 1. The second PPID check closes the race in which the
    # expected parent exits between the first check and arming the signal.
    if _LIBC.prctl(1, int(signal.SIGKILL), 0, 0, 0) != 0:
        raise SecurityError("could not arm the Linux parent-death signal")
    if os.getppid() != expected_parent_pid:
        raise SecurityError("expected parent exited while arming the death guard")


def _parent_death_preexec(expected_parent: int) -> Callable[[], None] | None:
    if sys.platform != "linux":
        return None

    def arm_parent_death_signal() -> None:
        try:
            arm_parent_death_guard(expected_parent)
        except BaseException:
            os._exit(126)

    return arm_parent_death_signal


def _bounded_process_preexec(
    *,
    expected_parent: int | None,
    limits: ProcessResourceLimits | None,
) -> Callable[[], None] | None:
    if expected_parent is None and limits is None:
        return None

    def configure_child() -> None:
        try:
            if expected_parent is not None:
                arm_parent_death_guard(expected_parent)
            if limits is not None:
                bindings = (
                    (resource.RLIMIT_AS, limits.address_space_bytes),
                    (resource.RLIMIT_NPROC, limits.processes),
                    (resource.RLIMIT_NOFILE, limits.open_files),
                    (resource.RLIMIT_FSIZE, limits.file_size_bytes),
                    (resource.RLIMIT_CORE, limits.core_bytes),
                    (resource.RLIMIT_CPU, limits.cpu_seconds),
                )
                for resource_name, value in bindings:
                    resource.setrlimit(resource_name, (value, value))
        except BaseException:
            os._exit(126)

    return configure_child


def _terminate_and_reap(
    process: subprocess.Popen[bytes], *, grace_seconds: float = 0.5
) -> None:
    """Terminate a dedicated process group before reaping its leader."""

    leader_exited = _leader_exited_without_reaping(process)
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    deadline = time.monotonic() + grace_seconds
    while not leader_exited and time.monotonic() < deadline:
        time.sleep(0.02)
        leader_exited = _leader_exited_without_reaping(process)
    # Always kill the group while the unreaped leader still reserves its PID;
    # this also removes children that inherited the stdout/stderr descriptors.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    if not leader_exited:
        deadline = time.monotonic() + 2
        while not leader_exited and time.monotonic() < deadline:
            time.sleep(0.02)
            leader_exited = _leader_exited_without_reaping(process)
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired as exc:
        raise SecurityError("bounded process group could not be reaped") from exc


def _leader_exited_without_reaping(process: subprocess.Popen[bytes]) -> bool:
    """Observe exit while retaining the PID as the process-group identity."""

    if sys.platform == "linux" and hasattr(os, "WNOWAIT"):
        try:
            result = os.waitid(
                os.P_PID,
                process.pid,
                os.WEXITED | os.WNOHANG | os.WNOWAIT,
            )
        except ChildProcessError:
            return True
        return result is not None
    return process.poll() is not None


def run_limited(
    argv: Sequence[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout_seconds: float,
    output_limit_bytes: int,
    stdin: bytes | None = None,
    guard: Callable[[], bool] | None = None,
    guard_interval_seconds: float = 0.25,
    supervise_parent: bool = False,
    resource_limits: ProcessResourceLimits | dict[str, int] | None = None,
) -> LimitedProcessResult:
    if (
        not argv
        or timeout_seconds <= 0
        or output_limit_bytes < 1
        or guard_interval_seconds <= 0
    ):
        raise SecurityError("invalid bounded process request")
    started = time.monotonic()
    if guard is not None:
        try:
            initially_allowed = bool(guard())
        except Exception:
            initially_allowed = False
        if not initially_allowed:
            return LimitedProcessResult(
                argv=tuple(argv),
                returncode=-int(signal.SIGKILL),
                stdout=b"",
                stderr=b"",
                timed_out=False,
                output_limited=False,
                guard_cancelled=True,
                duration_seconds=time.monotonic() - started,
            )
    expected_parent = os.getpid()
    limits = (
        None
        if resource_limits is None
        else ProcessResourceLimits.coerce(resource_limits)
    )
    process: subprocess.Popen[bytes] | None = None
    selector: selectors.BaseSelector | None = None
    stdin_file: Any | None = None
    streams: dict[str, bytearray] = {"stdout": bytearray(), "stderr": bytearray()}
    output_bytes = 0
    timed_out = False
    output_limited = False
    guard_cancelled = False
    termination_started: float | None = None
    group_killed = False
    next_guard = started + guard_interval_seconds
    completed = False

    try:
        if stdin is not None:
            stdin_file = tempfile.TemporaryFile(mode="w+b")
            stdin_file.write(stdin)
            stdin_file.seek(0)
        process = subprocess.Popen(
            list(argv),
            cwd=cwd,
            env=env,
            stdin=stdin_file if stdin_file is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            shell=False,
            start_new_session=True,
            preexec_fn=_bounded_process_preexec(
                expected_parent=(
                    expected_parent
                    if supervise_parent and sys.platform == "linux"
                    else None
                ),
                limits=limits,
            ),
        )
        assert process.stdout is not None and process.stderr is not None
        selector = selectors.DefaultSelector()
        selector.register(process.stdout, selectors.EVENT_READ, "stdout")
        selector.register(process.stderr, selectors.EVENT_READ, "stderr")
        leader_exited = False
        leader_exit_observed_at: float | None = None
        while selector.get_map() or not leader_exited:
            now = time.monotonic()
            if not leader_exited:
                leader_exited = _leader_exited_without_reaping(process)
                if leader_exited:
                    leader_exit_observed_at = now
                if leader_exited and not group_killed:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    group_killed = True
            if (
                leader_exited
                and selector.get_map()
                and leader_exit_observed_at is not None
                and now - leader_exit_observed_at >= 2
            ):
                raise SecurityError(
                    "bounded process left output descriptors open after its leader exited"
                )
            elapsed = now - started
            if not leader_exited and elapsed >= timeout_seconds:
                timed_out = True
            if not leader_exited and guard is not None and now >= next_guard:
                next_guard = now + guard_interval_seconds
                try:
                    if not guard():
                        guard_cancelled = True
                except Exception:
                    guard_cancelled = True
            if timed_out or output_limited or guard_cancelled:
                if termination_started is None:
                    termination_started = now
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                elif now - termination_started >= 0.5:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    group_killed = True
            if termination_started is not None and now - termination_started >= 5:
                if not leader_exited:
                    raise SecurityError(
                        "bounded process group did not terminate within grace period"
                    )
            timeout = 0.2
            if not timed_out:
                timeout = min(timeout, max(0.0, timeout_seconds - elapsed))
            if guard is not None and not leader_exited:
                timeout = min(timeout, max(0.0, next_guard - now))
            if selector.get_map():
                events = selector.select(timeout=timeout)
            else:
                time.sleep(timeout)
                events = []
            for key, _ in events:
                try:
                    chunk = os.read(key.fileobj.fileno(), 8192)
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                target = streams[key.data]
                remaining = max(0, output_limit_bytes - output_bytes)
                if remaining:
                    retained = chunk[:remaining]
                    target.extend(retained)
                    output_bytes += len(retained)
                if len(chunk) > remaining:
                    output_limited = True
        if not group_killed:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            group_killed = True
        returncode = process.wait(timeout=2)
        completed = True
        return LimitedProcessResult(
            argv=tuple(argv),
            returncode=returncode,
            stdout=bytes(streams["stdout"]),
            stderr=bytes(streams["stderr"]),
            timed_out=timed_out,
            output_limited=output_limited,
            guard_cancelled=guard_cancelled,
            duration_seconds=time.monotonic() - started,
        )
    finally:
        if selector is not None:
            selector.close()
        if process is not None:
            if not completed:
                _terminate_and_reap(process)
            if process.stdout is not None:
                process.stdout.close()
            if process.stderr is not None:
                process.stderr.close()
        if stdin_file is not None:
            stdin_file.close()


def lean_acceptance_argv(command: Sequence[str]) -> tuple[str, ...]:
    argv = tuple(command)
    if argv[:2] == ("env", "LEAN_NUM_THREADS=1"):
        argv = argv[2:]
    if len(argv) == 4 and argv[:3] == ("lake", "env", "lean"):
        relative = normalize_relative(argv[3])
        if not relative.endswith(".lean"):
            raise SecurityError("lean_check accepts only a repository-relative .lean file")
        return ("lake", "env", "lean", relative)
    raise SecurityError("lean_check accepts only lake env lean <relative.lean>")


def canonical_poincare_state_dir(raw: Path | str | None = None) -> Path:
    """Resolve the one private directory allowed to coordinate Lean builds."""

    value: Path | str | None = raw
    if value is None:
        value = os.environ.get("POINCARE_STATE_DIR")
    try:
        rendered = os.fspath(value) if value is not None else ""
    except TypeError as exc:
        raise SecurityError("POINCARE_STATE_DIR must be an explicit absolute path") from exc
    if not isinstance(rendered, str) or not rendered or "\x00" in rendered:
        raise SecurityError("POINCARE_STATE_DIR must be an explicit absolute path")
    lexical = Path(rendered)
    if not lexical.is_absolute() or os.path.normpath(rendered) != rendered:
        raise SecurityError("POINCARE_STATE_DIR must already be a normalized absolute path")
    try:
        canonical = lexical.resolve(strict=True)
    except OSError as exc:
        raise SecurityError(f"cannot resolve POINCARE_STATE_DIR: {exc}") from exc
    if str(canonical) != rendered or lexical.is_symlink() or not canonical.is_dir():
        raise SecurityError("POINCARE_STATE_DIR must be canonical and symlink-free")
    if canonical in {
        Path("/"),
        Path("/tmp"),
        Path("/var"),
        Path("/var/tmp"),
        Path("/run"),
        Path("/home"),
        Path("/srv"),
    }:
        raise SecurityError("POINCARE_STATE_DIR is overly broad")
    info = canonical.stat(follow_symlinks=False)
    if info.st_uid != os.geteuid() or stat.S_IMODE(info.st_mode) & 0o022:
        raise SecurityError("POINCARE_STATE_DIR must be owned by the Harness uid and not group-writable")
    return canonical


@dataclass
class BuildJobLock:
    """Held advisory lock for the canonical POINCARE_STATE_DIR build slot."""

    path: Path
    descriptor: int
    _released: bool = False

    def release(self) -> None:
        if self._released:
            return
        try:
            fcntl.flock(self.descriptor, fcntl.LOCK_UN)
        finally:
            os.close(self.descriptor)
            self._released = True

    def __enter__(self) -> BuildJobLock:
        return self

    def __exit__(self, _kind: Any, _value: Any, _traceback: Any) -> None:
        self.release()


def acquire_build_job_lock(
    state_dir: Path | str | None = None,
    *,
    timeout_seconds: float = 5.0,
    poll_seconds: float = 0.05,
) -> BuildJobLock:
    """Acquire ``POINCARE_STATE_DIR/build-job.lock`` within a strict time bound."""

    if (
        isinstance(timeout_seconds, bool)
        or not isinstance(timeout_seconds, (int, float))
        or timeout_seconds < 0
        or timeout_seconds > 60
        or isinstance(poll_seconds, bool)
        or not isinstance(poll_seconds, (int, float))
        or poll_seconds <= 0
        or poll_seconds > 1
    ):
        raise SecurityError("build-job lock bounds are invalid")
    root = canonical_poincare_state_dir(state_dir)
    directory_flags = os.O_RDONLY
    lock_flags = os.O_RDONLY
    if hasattr(os, "O_CLOEXEC"):
        directory_flags |= os.O_CLOEXEC
        lock_flags |= os.O_CLOEXEC
    if hasattr(os, "O_DIRECTORY"):
        directory_flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        directory_flags |= os.O_NOFOLLOW
        lock_flags |= os.O_NOFOLLOW
    directory_fd = os.open(root, directory_flags)
    descriptor: int | None = None
    created = False
    try:
        try:
            descriptor = os.open("build-job.lock", lock_flags, dir_fd=directory_fd)
        except FileNotFoundError:
            create_flags = lock_flags | os.O_CREAT | os.O_EXCL
            try:
                descriptor = os.open(
                    "build-job.lock", create_flags, 0o600, dir_fd=directory_fd
                )
                created = True
            except FileExistsError:
                descriptor = os.open("build-job.lock", lock_flags, dir_fd=directory_fd)
        if created:
            os.fsync(directory_fd)
    except OSError as exc:
        raise SecurityError(f"cannot open build-job lock safely: {exc}") from exc
    finally:
        os.close(directory_fd)
    assert descriptor is not None
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_nlink != 1
            or info.st_uid != os.geteuid()
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise SecurityError("build-job lock file has unsafe ownership or mode")
        deadline = time.monotonic() + float(timeout_seconds)
        while True:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_SH | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise SecurityError("build-job lock acquisition timed out")
                time.sleep(min(float(poll_seconds), remaining))
        return BuildJobLock(path=root / "build-job.lock", descriptor=descriptor)
    except BaseException:
        os.close(descriptor)
        raise
