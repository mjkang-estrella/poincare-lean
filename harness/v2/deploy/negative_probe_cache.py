"""Reuse only a sealed, exact negative completion probe at unchanged inputs.

This is an observation cache, never an acceptance or completion certificate.
The source receipt identity alone is insufficient: the actual imported Lean
artifacts are also bound. Missing provenance, dirty inputs, corruption and races
all fall back to a fresh Lean invocation. Evidence is append-only and bounded;
only the ignored negative receipt is atomically replaceable.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import time
from typing import Callable
import uuid


RESERVED = "Poincare.poincare_conjecture"
PROBE_SOURCE = (
    "import Poincare\n\n"
    "run_cmd do\n"
    "  let modules := (← Lean.getEnv).header.moduleNames\n"
    "  let entries ← modules.toList.mapM fun name => do\n"
    "    let path ← Lean.findOLean name\n"
    "    pure (Lean.Json.mkObj [(\"module\", Lean.toJson name.toString),\n"
    "      (\"olean\", Lean.toJson path.toString)])\n"
    "  let manifest := Lean.Json.arr entries.toArray\n"
    "  Lean.Elab.Command.liftIO <| IO.println (\"POINCARE_NEGATIVE_PROBE_IMPORTS=\" ++ manifest.compress)\n\n"
    "#check (Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement)\n"
    "#print axioms Poincare.poincare_conjecture\n"
)
SCHEMA = "poincare.negative-exact-probe.v1"
MAX_TRANSCRIPT_BYTES = 4 * 1024 * 1024
MAX_JSON_BYTES = 4 * 1024 * 1024
MAX_EVIDENCE_BYTES = 16 * 1024 * 1024
MAX_EVIDENCE_FILES = 1024
CODE_ROOT = Path(__file__).resolve().parents[3]


class CacheUnavailable(ValueError):
    """Identity or evidence is unsafe; a fresh check remains necessary."""


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _file_bytes(path: Path, *, sealed: bool = False, maximum: int | None = None) -> bytes:
    if str(path.resolve()) != str(path.absolute()):
        raise CacheUnavailable("redirected evidence/input path")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode):
            raise CacheUnavailable("input is not a regular file")
        if sealed and (before.st_uid != os.geteuid() or stat.S_IMODE(before.st_mode) != 0o400):
            raise CacheUnavailable("evidence is not owned and sealed")
        chunks = []
        size = 0
        while chunk := os.read(fd, 1024 * 1024):
            chunks.append(chunk)
            size += len(chunk)
            if maximum is not None and size > maximum:
                raise CacheUnavailable("input exceeds its bound")
        after = os.fstat(fd)
        key = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_uid, s.st_nlink,
                         s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        if key(before) != key(after) or size != before.st_size:
            raise CacheUnavailable("input changed while hashing")
        return b"".join(chunks)
    finally:
        os.close(fd)


def _file_identity(path: Path) -> dict:
    # Configured executable symlinks are resolved before being bound; evidence
    # paths themselves are never followed.
    resolved = path.resolve(strict=True)
    return {"path": str(resolved), "sha256": _sha256(_file_bytes(resolved))}


def _capture_identity(root: Path, toolchain_root: Path) -> dict:
    path = CODE_ROOT / "scripts/verification_receipts.py"
    spec = importlib.util.spec_from_file_location("poincare_verification_receipts", path)
    if spec is None or spec.loader is None:
        raise CacheUnavailable("verification identity implementation unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module.capture_identity(root, toolchain_root=toolchain_root)


def classify_probe(returncode: int, output: str) -> tuple[str, int]:
    """Unrelated import/parser errors are invalid, never a cached absence."""
    if returncode != 0:
        exact = re.compile(
            r"(?:^|\s)error:\s*Unknown (?:identifier|constant)\s+[`'\"]"
            + re.escape(RESERVED) + r"[`'\"]\s*$"
        )
        errors = [line.strip() for line in output.splitlines() if "error:" in line]
        if returncode == 1 and errors and all(exact.search(line) for line in errors):
            return "absent", 3
        return "invalid", 4
    match = re.search(r"depends on axioms:\s*\[(.*?)\]", output, re.S)
    if "does not depend on any axioms" in output:
        return "verified", 0
    if match is not None:
        axioms = {part.strip() for part in match.group(1).replace("\n", " ").split(",") if part.strip()}
        if axioms <= {"propext", "Classical.choice", "Quot.sound"}:
            return "verified", 0
    return "nonstandard_axioms", 5


def _run_lean(root: Path, command: list[str]) -> tuple[int, str]:
    env = _probe_environment()
    result = subprocess.run(command, cwd=root, input=PROBE_SOURCE, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
    return result.returncode, result.stdout


def _probe_environment() -> dict:
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    for name in ("LAKE_OVERRIDE_LEAN", "LAKE_OVERRIDE_LAKE", "LEAN_SYSROOT", "LEAN"):
        env.pop(name, None)
    return env


@dataclass
class ProbeResult:
    classification: str
    exit_code: int
    execution: str
    transcript: str
    identity: dict | None = None
    evidence_time: str | None = None
    evidence_path: str | None = None
    cache_note: str | None = None
    timings: dict | None = None
    artifact_snapshot: dict | None = None

    def emit(self) -> None:
        print(f"EXACT_DECLARATION_PROBE={self.classification}")
        source = self.identity.get("source", self.identity) if self.identity is not None else None
        metadata = {
            "execution": self.execution,
            "original_evidence_time": self.evidence_time,
            "original_identity_sha256": None if self.identity is None else _sha256(_json_bytes(self.identity)),
            "original_head": None if source is None else source["head"],
            "evidence_path": self.evidence_path,
            "cache_note": self.cache_note,
            "timings_seconds": self.timings,
        }
        if self.execution == "reused_negative":
            print("Reused negative result: exact reserved declaration absent; "
                  f"original evidence time={self.evidence_time} "
                  f"identity={metadata['original_identity_sha256']} HEAD={metadata['original_head']}.")
        print("EXACT_DECLARATION_PROBE_METADATA=" + json.dumps(metadata, sort_keys=True))
        if self.transcript and self.execution == "fresh":
            print(self.transcript.rstrip(), file=sys.stderr)


class NegativeProbeCache:
    def __init__(self, root: Path, toolchain_root: Path, config: Path,
                 config_fingerprint: str, *,
                 capture: Callable[[Path, Path], dict] = _capture_identity,
                 search_paths: Callable[[Path, Path], list[Path]] | None = None,
                 runner: Callable[[Path, list[str]], tuple[int, str]] = _run_lean,
                 maximum_evidence_bytes: int = MAX_EVIDENCE_BYTES):
        self.root = root.resolve(strict=True)
        self.toolchain_root = toolchain_root.resolve(strict=True)
        self.config = config.resolve(strict=True)
        self.config_fingerprint = config_fingerprint
        self.capture = capture
        self.search_paths = search_paths or _search_paths
        self.runner = runner
        self.maximum_evidence_bytes = maximum_evidence_bytes
        self.state = self.root / "harness/v2/state/negative-exact-probe"
        self.command = [str(self.toolchain_root / "bin/lake"), "env",
                        str(self.toolchain_root / "bin/lean"), "--stdin"]

    def identity(self) -> dict:
        git = os.environ.get("HARNESS_PI_GIT", "/usr/bin/git")
        dirty = subprocess.run([git, "-C", str(self.root), "status", "--porcelain=v1",
                                "--untracked-files=all"], check=True, stdout=subprocess.PIPE).stdout
        if dirty:
            raise CacheUnavailable("checkout is dirty")
        repository = self.capture(self.root, self.toolchain_root)
        if repository.get("clean") is not True or not repository.get("identity_sha256"):
            raise CacheUnavailable("repository identity is not clean")
        result = {
            "head": repository["head"], "tree": repository["tree"],
            "repository_identity_sha256": repository["identity_sha256"],
            "repo_root": str(self.root),
            "config_fingerprint": self.config_fingerprint,
            "config": _file_identity(self.config),
            "lean": _file_identity(self.toolchain_root / "bin/lean"),
            "lake": _file_identity(self.toolchain_root / "bin/lake"),
            "code": {str(path): _file_identity(path)["sha256"] for path in (
                Path(__file__).resolve(), Path(__file__).with_name("exact-completion-probe.sh").resolve(),
                Path(__file__).with_name("common.sh").resolve(), CODE_ROOT / "scripts/verification_receipts.py")},
            "probe_source_sha256": _sha256(PROBE_SOURCE.encode()),
        }
        return result

    def _prepare_state(self) -> None:
        # Only ignored repository state may hold this replaceable observation.
        check = subprocess.run([os.environ.get("HARNESS_PI_GIT", "/usr/bin/git"), "-C", str(self.root),
                                "check-ignore", "--quiet", str(self.state / "receipt.json")])
        if check.returncode != 0:
            raise CacheUnavailable("cache state is not ignored")
        self.state.mkdir(parents=True, exist_ok=True, mode=0o700)
        if self.state.resolve() != self.state:
            raise CacheUnavailable("cache state is redirected")
        for path in (self.state, self.state / "evidence"):
            path.mkdir(exist_ok=True, mode=0o700)
            info = path.lstat()
            if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid() or stat.S_IMODE(info.st_mode) != 0o700:
                raise CacheUnavailable("cache directory is not owned and private")

    @contextmanager
    def _lock(self):
        self._prepare_state()
        fd = os.open(self.state / "cache.lock", os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0), 0o600)
        try:
            info = os.fstat(fd)
            if not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid() or stat.S_IMODE(info.st_mode) != 0o600:
                raise CacheUnavailable("cache lock is unsafe")
            fcntl.flock(fd, fcntl.LOCK_EX)
            yield
        finally:
            os.close(fd)

    def _read_json(self, path: Path) -> dict:
        value = json.loads(_file_bytes(path, sealed=True, maximum=MAX_JSON_BYTES))
        if not isinstance(value, dict):
            raise CacheUnavailable("evidence is not an object")
        return value

    def _lookup(self, source_identity: dict) -> ProbeResult:
        receipt = self._read_json(self.state / "receipt.json")
        if set(receipt) != {"schema_version", "status", "identity", "evidence", "evidence_sha256"}:
            raise CacheUnavailable("invalid receipt fields")
        identity = receipt["identity"]
        if (receipt["schema_version"] != SCHEMA or type(receipt["status"]) is not int or receipt["status"] != 3 or
                not isinstance(identity, dict) or set(identity) != {"source", "artifacts"} or
                identity["source"] != source_identity):
            raise CacheUnavailable("receipt does not match exact negative inputs")
        artifacts = identity["artifacts"]
        snapshot = {}
        if (not isinstance(artifacts, dict) or set(artifacts) != {"manifest", "sha256", "file_count", "search_paths"} or
                imported_artifact_identity(self.root, self.toolchain_root, artifacts["manifest"],
                                           self.search_paths(self.root, self.toolchain_root), snapshot=snapshot) != artifacts):
            raise CacheUnavailable("compiled imports changed")
        relative = receipt["evidence"]
        if not isinstance(relative, str) or not re.fullmatch(r"evidence/[0-9a-f]{32}\.json", relative):
            raise CacheUnavailable("unsafe evidence path")
        path = self.state / relative
        raw = _file_bytes(path, sealed=True, maximum=MAX_JSON_BYTES)
        if _sha256(raw) != receipt["evidence_sha256"]:
            raise CacheUnavailable("evidence hash mismatch")
        evidence = json.loads(raw)
        expected = {"schema_version", "status", "classification", "identity", "timestamp",
                    "command", "probe_source_sha256", "transcript", "transcript_sha256", "transcript_size_bytes",
                    "lean_returncode", "execution"}
        if not isinstance(evidence, dict) or set(evidence) != expected:
            raise CacheUnavailable("invalid evidence fields")
        if (evidence["schema_version"] != SCHEMA or evidence["status"] != 3 or
                evidence["classification"] != "absent" or evidence["execution"] != "fresh" or
                evidence["identity"] != identity or evidence["command"] != self.command or
                evidence["probe_source_sha256"] != _sha256(PROBE_SOURCE.encode()) or
                type(evidence["lean_returncode"]) is not int or evidence["lean_returncode"] == 0):
            raise CacheUnavailable("evidence is not an exact fresh negative probe")
        if not isinstance(evidence["timestamp"], str) or not re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", evidence["timestamp"]):
            raise CacheUnavailable("invalid evidence timestamp")
        transcript_path = relative[:-5] + ".log"
        if evidence["transcript"] != transcript_path:
            raise CacheUnavailable("transcript path mismatch")
        transcript = _file_bytes(self.state / transcript_path, sealed=True, maximum=MAX_TRANSCRIPT_BYTES)
        if (_sha256(transcript) != evidence["transcript_sha256"] or
                len(transcript) != evidence["transcript_size_bytes"] or
                classify_probe(evidence["lean_returncode"], transcript.decode()) != ("absent", 3)):
            raise CacheUnavailable("transcript does not confirm exact absence")
        if _manifest_from_output(transcript.decode(), self.root) != artifacts["manifest"]:
            raise CacheUnavailable("transcript import provenance does not match receipt")
        return ProbeResult("absent", 3, "reused_negative", "", identity,
                           evidence["timestamp"], relative, artifact_snapshot=snapshot)

    def _write_sealed(self, path: Path, content: bytes) -> None:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0), 0o600)
        try:
            with os.fdopen(fd, "wb", closefd=False) as output:
                output.write(content)
                output.flush()
                os.fsync(fd)
            os.fchmod(fd, 0o400)
        finally:
            os.close(fd)

    def _publish(self, result: ProbeResult, lean_returncode: int) -> None:
        transcript = result.transcript.encode()
        if len(transcript) > MAX_TRANSCRIPT_BYTES:
            raise CacheUnavailable("transcript is too large to cache")
        unique = uuid.uuid4().hex
        relative = f"evidence/{unique}.json"
        evidence = {
            "schema_version": SCHEMA, "status": 3, "classification": "absent",
            "identity": result.identity, "timestamp": result.evidence_time,
            "command": self.command, "probe_source_sha256": _sha256(PROBE_SOURCE.encode()),
            "transcript": f"evidence/{unique}.log", "transcript_sha256": _sha256(transcript),
            "transcript_size_bytes": len(transcript), "lean_returncode": lean_returncode,
            "execution": "fresh",
        }
        raw = _json_bytes(evidence)
        if len(raw) > MAX_JSON_BYTES:
            raise CacheUnavailable("import evidence exceeds its bound")
        entries = list((self.state / "evidence").iterdir())
        if any(not path.is_file() or path.is_symlink() for path in entries):
            raise CacheUnavailable("evidence directory contains unsafe entries")
        if (len(entries) + 2 > MAX_EVIDENCE_FILES or
                sum(path.stat().st_size for path in entries) + len(raw) + len(transcript) > self.maximum_evidence_bytes):
            raise CacheUnavailable("append-only evidence quota reached")
        self._write_sealed(self.state / evidence["transcript"], transcript)
        self._write_sealed(self.state / relative, raw)
        receipt = {"schema_version": SCHEMA, "status": 3, "identity": result.identity,
                   "evidence": relative, "evidence_sha256": _sha256(raw)}
        temporary = self.state / f"receipt-{unique}.tmp"
        self._write_sealed(temporary, _json_bytes(receipt))
        os.replace(temporary, self.state / "receipt.json")
        for directory in (self.state / "evidence", self.state):
            fd = os.open(directory, os.O_RDONLY)
            try:
                os.fsync(fd)
            finally:
                os.close(fd)
        result.evidence_path = relative

    def run(self, *, fresh: bool = False) -> ProbeResult:
        started = time.monotonic()
        if fresh:
            # Independent final verification pays only for Lean. The caller's
            # existing append-only cycle evidence preserves this fresh result;
            # it neither reads nor updates a reusable negative observation.
            returncode, transcript = self.runner(self.root, self.command)
            classification, status = classify_probe(returncode, transcript)
            return ProbeResult(classification, status, "fresh", transcript,
                               evidence_time=datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                               cache_note="fresh requested; negative cache bypassed",
                               timings={"identity": 0.0, "cache_validation": 0.0,
                                        "lean_probe": time.monotonic() - started})
        identity = None
        note = None
        try:
            identity = self.identity()
        except (OSError, ValueError, ImportError, subprocess.SubprocessError) as exc:
            note = f"negative cache unavailable: {type(exc).__name__}"
        identity_seconds = time.monotonic() - started
        if identity is not None:
            try:
                with self._lock():
                    reused = self._lookup(identity)
                    if self.identity() != identity:
                        raise CacheUnavailable("inputs changed during cache validation")
                    _validate_artifact_snapshot(reused.artifact_snapshot,
                                                self.search_paths(self.root, self.toolchain_root))
                    reused.timings = {"identity": identity_seconds, "cache_validation": time.monotonic() - started - identity_seconds,
                                      "lean_probe": 0.0}
                    return reused
            except (OSError, ValueError, ImportError, subprocess.SubprocessError) as exc:
                note = f"negative cache miss: {type(exc).__name__}"
        inventory = None
        paths = None
        if identity is not None:
            try:
                paths = self.search_paths(self.root, self.toolchain_root)
                inventory = _artifact_inventory(paths)
            except (OSError, ValueError, subprocess.SubprocessError) as exc:
                note = f"artifact provenance unavailable: {type(exc).__name__}"
        before_lean = time.monotonic()
        returncode, transcript = self.runner(self.root, self.command)
        classification, status = classify_probe(returncode, transcript)
        result = ProbeResult(classification, status, "fresh", transcript, identity,
                             datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), cache_note=note,
                             timings={"identity": identity_seconds, "lean_probe": time.monotonic() - before_lean})
        if status == 3 and identity is not None and inventory is not None and paths is not None:
            try:
                with self._lock():
                    if self.identity() != identity:
                        raise CacheUnavailable("inputs changed during fresh probe")
                    if self.search_paths(self.root, self.toolchain_root) != paths:
                        raise CacheUnavailable("search path changed during fresh probe")
                    manifest = _manifest_from_output(transcript, self.root)
                    result.identity = {"source": identity, "artifacts": imported_artifact_identity(
                        self.root, self.toolchain_root, manifest, paths, before=inventory)}
                    self._publish(result, returncode)
            except (OSError, ValueError, ImportError, subprocess.SubprocessError) as exc:
                result.cache_note = f"negative result not cached: {type(exc).__name__}"
        return result


def _search_paths(root: Path, toolchain_root: Path) -> list[Path]:
    # Query Lake's actual environment without executing the Lean compiler.
    result = subprocess.run([str(toolchain_root / "bin/lake"), "env", sys.executable,
                             "-S", "-P", "-B", "-c",
                             "import json,os; print(json.dumps(os.environ.get('LEAN_PATH', '')))"]
                            , cwd=root, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            env=_probe_environment())
    value = json.loads(result.stdout)
    if not isinstance(value, str):
        raise CacheUnavailable("invalid Lake search path")
    paths = [Path(part) for part in value.split(os.pathsep) if part]
    paths.append(toolchain_root / "lib/lean")
    normalized = []
    for path in paths:
        path = (root / path).resolve() if not path.is_absolute() else path.resolve()
        # Unattested paths outside the source/toolchain boundary never enter a
        # reusable observation. External overrides still get a fresh probe.
        if not (path.is_relative_to(root) or path.is_relative_to(toolchain_root)):
            raise CacheUnavailable("import search path is outside attested inputs")
        if not path.is_dir():
            raise CacheUnavailable("import search directory is missing")
        normalized.append(path)
    return normalized


def _stat_key(path: Path) -> tuple:
    info = path.stat()
    if not stat.S_ISREG(info.st_mode):
        raise CacheUnavailable("compiled artifact is not regular")
    return (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def _artifact_inventory(paths: list[Path]) -> dict:
    # Cheap pre-probe metadata is needed to detect a compiler reading an artifact
    # concurrently replaced before the post-probe content fingerprint. Only
    # actual imported artifacts are subsequently read and hashed.
    keys = {}
    resolutions = {}
    for root in paths:
        for path in root.rglob("*"):
            if path.name.endswith((".olean", ".olean.server", ".olean.private", ".ir")):
                resolved = path.resolve(strict=True)
                if not any(resolved.is_relative_to(boundary) for boundary in paths):
                    raise CacheUnavailable("compiled artifact is redirected outside import roots")
                keys[str(resolved)] = _stat_key(resolved)
                resolutions[str(path)] = str(resolved)
    return {"keys": keys, "resolutions": resolutions}


def _manifest_from_output(output: str, root: Path) -> list[dict]:
    prefix = "POINCARE_NEGATIVE_PROBE_IMPORTS="
    lines = [line[len(prefix):] for line in output.splitlines() if line.startswith(prefix)]
    if len(lines) != 1:
        raise CacheUnavailable("fresh Lean import manifest is missing or ambiguous")
    manifest = json.loads(lines[0])
    if not isinstance(manifest, list) or not manifest or len(manifest) > 20000:
        raise CacheUnavailable("invalid import manifest")
    normalized = []
    seen = set()
    for item in manifest:
        if (not isinstance(item, dict) or set(item) != {"module", "olean"} or
                not isinstance(item["module"], str) or
                not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", item["module"]) or
                item["module"] in seen or not isinstance(item["olean"], str)):
            raise CacheUnavailable("invalid imported module")
        seen.add(item["module"])
        path = Path(item["olean"])
        path = path.resolve(strict=True) if path.is_absolute() else (root / path).resolve(strict=True)
        normalized.append({"module": item["module"], "olean": str(path)})
    if "Poincare" not in seen:
        raise CacheUnavailable("import manifest does not include root")
    return sorted(normalized, key=lambda entry: entry["module"])


def imported_artifact_identity(root: Path, toolchain_root: Path, manifest: list[dict],
                               search_paths: list[Path], *, before: dict | None = None,
                               snapshot: dict | None = None) -> dict:
    """Hash the actual closure captured by Lean; re-resolve to catch shadowing."""
    if not search_paths or any(not (path.is_relative_to(root) or path.is_relative_to(toolchain_root)) for path in search_paths):
        raise CacheUnavailable("unattested import search path")
    # Validate receipt-provided records using the same strict manifest parser.
    manifest = _manifest_from_output("POINCARE_NEGATIVE_PROBE_IMPORTS=" + json.dumps(manifest), root)
    digest = hashlib.sha256()
    count = 0
    hashed_keys = {}
    absent = []
    resolutions = {}
    for item in manifest:
        relative = Path(*item["module"].split(".")).with_suffix(".olean")
        path = next((boundary / relative for boundary in search_paths if (boundary / relative).is_file()), None)
        if path is None or str(path.resolve(strict=True)) != item["olean"]:
            raise CacheUnavailable("imported module is missing or newly shadowed")
        stem = str(path)[:-len(".olean")]
        for suffix in (".olean", ".olean.server", ".olean.private", ".ir"):
            candidate = Path(stem + suffix)
            record = {"module": item["module"], "suffix": suffix, "path": None, "sha256": None}
            if candidate.exists():
                resolved = candidate.resolve(strict=True)
                if not any(resolved.is_relative_to(boundary) for boundary in search_paths):
                    raise CacheUnavailable("import artifact is redirected outside inputs")
                key = _stat_key(resolved)
                if before is not None and (before["keys"].get(str(resolved)) != key or
                                           before["resolutions"].get(str(candidate)) != str(resolved)):
                    raise CacheUnavailable("import artifact or its resolution changed during fresh probe")
                record.update(_file_identity(resolved))
                if _stat_key(resolved) != key:
                    raise CacheUnavailable("import artifact changed during fingerprint")
                hashed_keys[str(resolved)] = key
                resolutions[str(candidate)] = str(resolved)
                count += 1
            elif before is not None and str(candidate) in before["resolutions"]:
                raise CacheUnavailable("optional import artifact disappeared during probe")
            else:
                absent.append(str(candidate))
            digest.update(_json_bytes(record))
    if any(_stat_key(Path(path)) != key for path, key in hashed_keys.items()):
        raise CacheUnavailable("import closure changed during fingerprint")
    if snapshot is not None:
        snapshot.update({"manifest": manifest, "search_paths": list(search_paths),
                         "keys": hashed_keys, "absent": absent, "resolutions": resolutions})
        _validate_artifact_snapshot(snapshot, search_paths)
    return {"manifest": manifest, "sha256": digest.hexdigest(), "file_count": count,
            "search_paths": [str(path) for path in search_paths]}


def _validate_artifact_snapshot(snapshot: dict | None, search_paths: list[Path]) -> None:
    # File ctime/inode/size metadata captured while hashing lets the final
    # source/config recheck reject artifact races without rereading gigabytes.
    if snapshot is None or snapshot["search_paths"] != search_paths:
        raise CacheUnavailable("import search path changed during cache validation")
    for item in snapshot["manifest"]:
        relative = Path(*item["module"].split(".")).with_suffix(".olean")
        path = next((root / relative for root in search_paths if (root / relative).is_file()), None)
        if path is None or str(path.resolve(strict=True)) != item["olean"]:
            raise CacheUnavailable("imported module changed during cache validation")
    if (any(str(Path(path).resolve(strict=True)) != resolved for path, resolved in snapshot["resolutions"].items()) or
            any(_stat_key(Path(path)) != key for path, key in snapshot["keys"].items()) or
            any(Path(path).exists() for path in snapshot["absent"])):
        raise CacheUnavailable("compiled import changed during cache validation")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fresh", action="store_true", help="always execute an independent Lean probe")
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--toolchain-root", required=True, type=Path)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--config-fingerprint", required=True)
    args = parser.parse_args()
    try:
        result = NegativeProbeCache(args.root, args.toolchain_root, args.config, args.config_fingerprint).run(fresh=args.fresh)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print("EXACT_DECLARATION_PROBE=invalid")
        print(f"exact probe failed: {type(exc).__name__}", file=sys.stderr)
        return 4
    result.emit()
    return result.exit_code


if __name__ == "__main__":
    raise SystemExit(main())
