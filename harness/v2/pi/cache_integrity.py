"""Reusable cache hashes only for an OS-protected, pinned cache generation.

This opt-in API accepts a recursively read-only *filesystem*, never a read-only
bind over a writable superblock or a chmod-sealed directory.  It intentionally
supports only ext4/xfs backed by an inaccessible physical block device; virtual,
network, FUSE, overlay, loop and device-mapper storage require separate proofs.
The ordinary sparse sandbox path always hashes every cache file.

Tokens are private in-memory receipts, not a JSON/config authorization.  Their
binding includes the cache manifest, base tree and compiler identity.  Every use
rechecks mount identity/options, namespace, privileges, parent path identities
and backing-device protection.  A changed protection generation fails closed.
The kernel mountinfo field contract is documented at
https://docs.kernel.org/filesystems/proc.html#proc-pid-mountinfo .
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Mapping


class CacheProtectionError(RuntimeError):
    """The cache does not have a proven reusable protected generation."""


_ISSUER = object()
_ALLOWED_FILESYSTEMS = frozenset({"ext4", "xfs"})


@dataclass(frozen=True)
class MountRecord:
    mount_id: int
    parent_id: int
    device: str
    root: str
    point: str
    options: tuple[str, ...]
    optional: tuple[str, ...]
    filesystem: str
    source: str
    super_options: tuple[str, ...]


@dataclass(frozen=True)
class ProtectedCacheAttestation:
    """Issued only after one full content hash and stable OS protection checks."""
    root: str
    binding_sha256: str
    tree_sha256: str
    generation: tuple[object, ...]
    _issuer: object


def _decode_mount_field(raw: str) -> str:
    # mountinfo escapes only these four octal values; reject unknown escapes.
    if re.search(r"\\(?!040|011|012|134)", raw):
        raise CacheProtectionError("unsupported mountinfo escape")
    return re.sub(r"\\(040|011|012|134)", lambda match: chr(int(match[1], 8)), raw)


def _parse_mountinfo(raw: str) -> tuple[MountRecord, ...]:
    records: list[MountRecord] = []
    ids: set[int] = set()
    for line in raw.splitlines():
        fields = line.split()
        try:
            divider = fields.index("-")
            if divider < 6 or len(fields) != divider + 4:
                raise ValueError("shape")
            mount_id, parent_id = int(fields[0]), int(fields[1])
            if mount_id <= 0 or parent_id <= 0 or mount_id in ids:
                raise ValueError("mount ID")
            if re.fullmatch(r"[0-9]+:[0-9]+", fields[2]) is None:
                raise ValueError("device")
            root, point = _decode_mount_field(fields[3]), _decode_mount_field(fields[4])
            if not root.startswith("/") or not point.startswith("/"):
                raise ValueError("path")
            ids.add(mount_id)
            records.append(MountRecord(
                mount_id, parent_id, fields[2], root, point,
                tuple(sorted(fields[5].split(","))), tuple(fields[6:divider]),
                fields[divider + 1], _decode_mount_field(fields[divider + 2]),
                tuple(sorted(fields[divider + 3].split(","))),
            ))
        except (ValueError, IndexError) as exc:
            raise CacheProtectionError("invalid mountinfo table") from exc
    if not records:
        raise CacheProtectionError("empty mountinfo table")
    return tuple(records)


def _read_mountinfo() -> tuple[MountRecord, ...]:
    try:
        with Path("/proc/self/mountinfo").open("r", encoding="utf-8") as stream:
            raw = stream.read(1024 * 1024 + 1)
        if len(raw) > 1024 * 1024:
            raise CacheProtectionError("mountinfo exceeds its cap")
        return _parse_mountinfo(raw)
    except (OSError, UnicodeDecodeError) as exc:
        raise CacheProtectionError("cannot inspect mountinfo") from exc


def _within(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


def _metadata(path: Path) -> tuple[int, ...]:
    try:
        info = path.stat(follow_symlinks=False)
    except OSError as exc:
        raise CacheProtectionError(f"cannot inspect protected path: {path}") from exc
    if stat.S_ISLNK(info.st_mode):
        raise CacheProtectionError(f"protected path is a symlink: {path}")
    return (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid)


def _root_protected_path(path: Path, *, device: bool = False) -> tuple[object, ...]:
    records = []
    for item in (*reversed(path.parents), path):
        data = _metadata(item)
        mode, uid = data[2], data[3]
        write_mask = 0o002 if device and item == path else 0o022
        if uid != 0 or mode & write_mask:
            raise CacheProtectionError(f"path is not protected by root ownership: {item}")
        if os.access(item, os.W_OK):
            raise CacheProtectionError(f"protected path is writable by this process: {item}")
        if item != path and not stat.S_ISDIR(mode):
            raise CacheProtectionError("protected path parent is not a directory")
        records.append((str(item), data))
    if device and not stat.S_ISBLK(records[-1][1][2]):
        raise CacheProtectionError("protected filesystem source must be a block device")
    return tuple(records)


def _process_protection() -> tuple[object, ...]:
    if sys.platform != "linux":
        raise CacheProtectionError("protected-cache reuse requires Linux")
    # No administrative authority may be carried across the cached hash.
    if os.geteuid() == 0 or os.getuid() != os.geteuid():
        raise CacheProtectionError("protected-cache reuse requires an unprivileged process")
    try:
        status = Path("/proc/self/status").read_text(encoding="ascii")
        values = dict(line.split(":", 1) for line in status.splitlines() if ":" in line)
        capabilities = tuple(int(values[key].strip(), 16) for key in (
            "CapInh", "CapPrm", "CapEff", "CapAmb",
        ))
        if any(capabilities):
            raise CacheProtectionError("protected-cache process must carry no capabilities")
        namespace = Path("/proc/self/ns/mnt").stat()
    except (OSError, KeyError, ValueError) as exc:
        raise CacheProtectionError("cannot prove process/mount namespace protection") from exc
    return (os.getuid(), os.geteuid(), os.getgid(), tuple(os.getgroups()),
            capabilities, namespace.st_dev, namespace.st_ino)


def _block_protection(record: MountRecord) -> tuple[object, ...]:
    source = Path(record.source)
    if not source.is_absolute():
        raise CacheProtectionError("filesystem source is not an absolute block device")
    protected = _root_protected_path(source, device=True)
    info = source.stat(follow_symlinks=False)
    if f"{os.major(info.st_rdev)}:{os.minor(info.st_rdev)}" != record.device:
        raise CacheProtectionError("mount source does not match its pinned device")
    try:
        sysdev = (Path("/sys/dev/block") / record.device).resolve(strict=True)
        devices = [sysdev]
        if (sysdev / "partition").exists():
            devices.append(sysdev.parent)
        evidence = []
        for entry in devices:
            # Loop backing files and virtual slave graphs need a separate proof.
            if any((entry / name).exists() for name in ("loop", "dm", "md")):
                raise CacheProtectionError("virtual backing devices are not supported")
            # Partition sysfs directories do not have a slaves/ entry; their
            # containing physical device is checked separately below.
            slaves = entry / "slaves"
            if slaves.exists() and list(slaves.iterdir()):
                raise CacheProtectionError("stacked backing devices are not supported")
            raw_dev = (entry / "dev").read_text(encoding="ascii").strip()
            if re.fullmatch(r"[0-9]+:[0-9]+", raw_dev) is None:
                raise CacheProtectionError("invalid backing device identity")
            node = (Path("/dev/block") / raw_dev).resolve(strict=True)
            evidence.append((str(entry), raw_dev, _root_protected_path(node, device=True)))
    except OSError as exc:
        raise CacheProtectionError("cannot prove physical backing device protection") from exc
    return (protected, tuple(evidence))


def _inspect_protection_generation(root: Path) -> tuple[object, ...]:
    privileges = _process_protection()
    if not root.is_absolute() or root.resolve(strict=True) != root:
        raise CacheProtectionError("protected cache root must be a canonical absolute path")
    mounts = _read_mountinfo()
    covers = [item for item in mounts if _within(root, Path(item.point))]
    if not covers:
        raise CacheProtectionError("cache has no covering mount")
    longest = max(len(Path(item.point).parts) for item in covers)
    nearest = [item for item in covers if len(Path(item.point).parts) == longest]
    if len(nearest) != 1:
        raise CacheProtectionError("stacked cache mounts are not supported")
    covering = nearest[0]
    relevant = [covering, *(item for item in mounts if _within(Path(item.point), root)
                          and item.mount_id != covering.mount_id)]
    devices = {item.device for item in relevant}
    aliases = [item for item in mounts if item.device in devices]
    backing = []
    for item in relevant:
        if ("ro" not in item.options or "rw" in item.options or
                "ro" not in item.super_options or "rw" in item.super_options):
            raise CacheProtectionError("cache requires recursively read-only filesystem mounts")
        if item.filesystem not in _ALLOWED_FILESYSTEMS:
            raise CacheProtectionError("cache filesystem has no supported protection proof")
        point = Path(item.point)
        point_info = point.stat(follow_symlinks=False)
        root_dev = root.stat(follow_symlinks=False).st_dev if item is covering else point_info.st_dev
        if f"{os.major(root_dev)}:{os.minor(root_dev)}" != item.device:
            raise CacheProtectionError("cache mount device identity does not match the path")
        backing.append((item.mount_id, _block_protection(item)))
    if any("rw" in item.super_options or "ro" not in item.super_options for item in aliases):
        raise CacheProtectionError("cache filesystem has a writable alias")
    # Outside the protected filesystem, writable ancestor renames could replace
    # the mount path.  Root-controlled ancestors prevent same-user substitution.
    parents = _root_protected_path(Path(covering.point))
    cache_path = tuple((str(item), _metadata(item)) for item in
                       (*reversed(root.parents), root))
    generation = (privileges, tuple(sorted(relevant, key=lambda item: item.mount_id)),
                  tuple(sorted(aliases, key=lambda item: item.mount_id)),
                  parents, cache_path, tuple(backing))
    if _read_mountinfo() != mounts:
        raise CacheProtectionError("mount table changed during protection attestation")
    return generation


def _protection_generation(root: Path) -> tuple[object, ...]:
    try:
        return _inspect_protection_generation(root)
    except OSError as exc:
        raise CacheProtectionError("cannot prove protected cache generation") from exc


def _binding_digest(binding: Mapping[str, object]) -> str:
    try:
        raw = json.dumps(dict(binding), sort_keys=True, separators=(",", ":"),
                         allow_nan=False).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise CacheProtectionError("invalid protected-cache binding") from exc
    return hashlib.sha256(raw).hexdigest()


def attest_protected_cache(*, root: Path, binding: Mapping[str, object],
                           tree_sha256: str,
                           hash_content: Callable[[], str]) -> ProtectedCacheAttestation:
    """Hash once between matching protection snapshots; never silently downgrade."""
    before = _protection_generation(root)
    if hash_content() != tree_sha256:
        raise CacheProtectionError("protected cache content digest mismatch")
    after = _protection_generation(root)
    if after != before:
        raise CacheProtectionError("protected cache generation changed while hashing")
    return ProtectedCacheAttestation(str(root), _binding_digest(binding),
                                     tree_sha256, before, _ISSUER)


def revalidate_protected_cache(*, attestation: ProtectedCacheAttestation,
                              root: Path, binding: Mapping[str, object],
                              tree_sha256: str) -> None:
    """Cheap OS generation validation; no file-content or directory tree scan."""
    if (not isinstance(attestation, ProtectedCacheAttestation) or
            attestation._issuer is not _ISSUER or attestation.root != str(root) or
            attestation.binding_sha256 != _binding_digest(binding) or
            attestation.tree_sha256 != tree_sha256):
        raise CacheProtectionError("protected cache attestation binding changed")
    if _protection_generation(root) != attestation.generation:
        raise CacheProtectionError("protected cache generation changed")
