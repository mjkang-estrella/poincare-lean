#!/usr/bin/env python3
"""Content-bound integration evidence; a receipt never certifies completion.

Reading receipts hashes source and checks Git/package/compiler identity. It does
not run Lake or Lean. Only write_status_summary.sh runs fresh integration gates.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import uuid

SCHEMA_VERSION = 1
DEFAULT_RECEIPT = "harness/v2/state/verification/latest.json"
STATUS_PATH = "CURRENT_STATUS.md"
SOURCE_SUFFIXES = {".lean", ".py", ".sh", ".json", ".toml", ".yaml", ".yml", ".md"}
PRUNED_DIRS = {".git", ".lake", "__pycache__", "node_modules"}
PHASES = [
    ("build", ["lake", "build"]),
    ("interface", ["sh", "scripts/interface_audit.sh"]),
    ("mathlib", ["sh", "scripts/mathlib_gap_audit.sh"]),
    ("shape", ["sh", "scripts/shape_contract_audit.sh"]),
    ("theorem", ["sh", "scripts/theorem_contract_audit.sh"]),
    ("semantic", ["sh", "scripts/semantic_surface_audit.sh"]),
    ("root_import", ["sh", "scripts/root_import_audit.sh"]),
    ("axiom", ["sh", "scripts/axiom_audit.sh"]),
    ("completion", ["env", "COMPLETION_AUDIT_SKIP_STATUS_SNAPSHOT=1",
                    "COMPLETION_AUDIT_GATE_RESULTS_DIR={phase_dir}",
                    "sh", "scripts/completion_audit.sh"]),
]
GATE_POLICY = {"version": 1, "phases": PHASES, "require_clean_for_reuse": True,
               "completion_certified_by_receipt": False,
               "source_scope": "tracked inputs and relevant untracked/ignored source; generated status/evidence excluded"}


class VerificationError(ValueError):
    pass


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def utc_now():
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z")


def run(root, argv):
    result = subprocess.run(argv, cwd=root, capture_output=True, check=False)
    if result.returncode:
        raise VerificationError(f"Identity command failed ({result.returncode}): {' '.join(argv)}")
    return result.stdout.decode("utf-8", errors="surrogateescape")


def excluded(name):
    return (name == STATUS_PATH or name == "CURRENT_STATUS.receipt.json" or
            name.startswith(("harness/reports/", "harness/v2/state/")) or
            any(part in PRUNED_DIRS for part in Path(name).parts))


def reject_index_flags(root):
    hidden = [entry[2:] for entry in run(root, ["git", "ls-files", "-v", "-z"]).split("\0")
              if entry and (entry[0].islower() or entry[0] == "S") and not excluded(entry[2:])]
    if hidden:
        raise VerificationError("Source inputs use assume-unchanged/skip-worktree index flags: " +
                                ", ".join(hidden[:5]))


def source_paths(root):
    reject_index_flags(root)
    tracked = set(filter(None, run(root, ["git", "ls-files", "-z"]).split("\0")))
    untracked = set(filter(None, run(root, ["git", "ls-files", "--others", "--exclude-standard", "-z"]).split("\0")))
    relevant = {name for name in untracked if Path(name).suffix in SOURCE_SUFFIXES}
    # Ignored modules can still be imported. Do not let .gitignore hide inputs.
    for directory, subdirs, filenames in os.walk(root):
        relative = Path(directory).relative_to(root)
        subdirs[:] = [name for name in subdirs if name not in PRUNED_DIRS and
                      not excluded((relative / name / "_").as_posix())]
        for name in filenames:
            if name.endswith(".lean"):
                relevant.add((relative / name).as_posix())
    return sorted(name for name in tracked | relevant if not excluded(name)), tracked


def file_sha256(path):
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def file_identity(path):
    try:
        before = path.lstat()
    except FileNotFoundError:
        return {"kind": "missing"}
    if stat.S_ISLNK(before.st_mode):
        target = os.readlink(path)
        if not path.is_file():
            raise VerificationError(f"Source symlink does not resolve to a regular file: {path}")
        result = {"kind": "symlink", "target": target, "sha256": file_sha256(path)}
    elif stat.S_ISREG(before.st_mode):
        result = {"kind": "file", "sha256": file_sha256(path),
                  "executable": bool(before.st_mode & 0o111)}
    else:
        raise VerificationError(f"Unsupported source input: {path}")
    after = path.lstat()
    if (before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
            after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
        raise VerificationError(f"Source changed during identity capture: {path}")
    return result


def compiler_identity(root, toolchain_root=None):
    """Resolve installed binaries without invoking a compiler or downloading it."""
    binaries = {}
    pinned_root = toolchain_root or os.environ.get("POINCARE_PI_TOOLCHAIN_ROOT")
    for name in ("lean", "lake"):
        if pinned_root:
            path = (Path(pinned_root) / "bin" / name).resolve(strict=True)
        elif shutil.which("elan"):
            path = Path(run(root, ["elan", "which", name]).strip()).resolve(strict=True)
        else:
            found = shutil.which(name)
            if not found:
                raise VerificationError(f"Installed {name} executable unavailable; no installation was attempted")
            path = Path(found).resolve(strict=True)
        binaries[name] = {"path": str(path), **file_identity(path)}
    overrides = {key: os.environ[key] for key in
                 ("ELAN_TOOLCHAIN", "LEAN", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT",
                  "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "LAKE_OVERRIDE_LAKE") if key in os.environ}
    roots = {str(Path(binary["path"]).parent.parent) for binary in binaries.values()}
    if len(roots) != 1:
        raise VerificationError("Lean and Lake executables come from different toolchain roots")
    installed_root = Path(next(iter(roots)))
    library_files = {}
    # Standard-library oleans and runtime shared libraries are compiler inputs.
    # Bind content, including same-size changes, rather than relying on mtimes.
    library_root = installed_root / "lib"
    if library_root.exists():
        for path in sorted(library_root.rglob("*")):
            if path.is_file() or path.is_symlink():
                library_files[path.relative_to(installed_root).as_posix()] = file_identity(path)
    for path in sorted((installed_root / "bin").iterdir()):
        if path.suffix in {".so", ".dylib", ".dll"}:
            library_files[path.relative_to(installed_root).as_posix()] = file_identity(path)
    return {"binaries": binaries, "environment": overrides,
            "library_files": library_files, "library_sha256": digest(library_files)}


def package_identities(root):
    manifest_path = root / "lake-manifest.json"
    if not manifest_path.is_file():
        raise VerificationError("lake-manifest.json is missing")
    try:
        manifest = json.loads(manifest_path.read_text())
        packages_dir = root / manifest.get("packagesDir", ".lake/packages")
        result = {}
        for entry in manifest.get("packages", []):
            name = entry["name"]
            if not isinstance(name, str) or Path(name).name != name or name in {".", ".."}:
                raise VerificationError("Invalid dependency package name")
            package = packages_dir / name
            if entry.get("type") == "path":
                package = root / entry["dir"]
            if not (package / ".git").exists():
                raise VerificationError(f"Dependency lacks Git provenance: {name}")
            head = run(package, ["git", "rev-parse", "HEAD"]).strip()
            tree = run(package, ["git", "rev-parse", "HEAD^{tree}"]).strip()
            dirty = run(package, ["git", "status", "--porcelain", "--untracked-files=no"])
            extra = run(package, ["git", "ls-files", "--others", "-z"]).split("\0")
            relevant_extra = sorted(n for n in extra if n and not excluded(n) and
                                    (Path(n).suffix in SOURCE_SUFFIXES or n == "lean-toolchain"))
            if dirty or relevant_extra:
                raise VerificationError(f"Dependency has dirty source inputs: {name}")
            if entry.get("type") == "git" and head != entry.get("rev"):
                raise VerificationError(f"Dependency revision differs from manifest: {name}")
            names, _ = source_paths(package)
            source_files = {path: file_identity(package / path) for path in names}
            reject_index_flags(package)
            if run(package, ["git", "status", "--porcelain", "--untracked-files=no"]):
                raise VerificationError(f"Dependency source changed during identity capture: {name}")
            result[name] = {"head": head, "tree": tree, "clean": True,
                            "source_sha256": digest(source_files), "source_files": source_files,
                            "manifest": entry, "path": str(package.resolve())}
        return result
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"Cannot establish package identity: {exc}") from exc


def capture_identity(root, toolchain_root=None):
    """JSON-serializable identity for cheap status and negative-only probe reuse.

    Dirty project source is represented by clean=False. Dependency/compiler
    provenance failures raise VerificationError instead of permitting reuse.
    """
    root = Path(root).resolve()
    head = run(root, ["git", "rev-parse", "HEAD"]).strip()
    tree = run(root, ["git", "rev-parse", "HEAD^{tree}"]).strip()
    names, tracked = source_paths(root)
    stamps = {name: (root / name).lstat() for name in names if (root / name).exists()}
    files = {name: file_identity(root / name) for name in names}
    # A second stat pass catches edits to early files while later files are read.
    for name, before in stamps.items():
        after = (root / name).lstat()
        if (before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
                after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
            raise VerificationError(f"Source changed during identity capture: {name}")
    changed = set(filter(None, run(root, ["git", "diff", "--name-only", "-z"]).split("\0")))
    changed.update(filter(None, run(root, ["git", "diff", "--cached", "--name-only", "-z", "HEAD"]).split("\0")))
    dirty_paths = sorted(name for name in changed | (set(names) - tracked) if not excluded(name))
    identity = {"head": head, "tree": tree, "files": files,
                "source_sha256": digest(files), "dirty_paths": dirty_paths,
                "clean": not dirty_paths, "packages": package_identities(root),
                "toolchain": compiler_identity(root, toolchain_root), "gate_policy_sha256": digest(GATE_POLICY)}
    if run(root, ["git", "rev-parse", "HEAD"]).strip() != head or source_paths(root)[0] != names:
        raise VerificationError("Source changed during identity capture")
    identity["identity_sha256"] = digest(identity)
    return identity


def same_identity(before, after):
    return before.get("identity_sha256") == after.get("identity_sha256")


def equivalent_source(before, after):
    """A generated-status-only commit changes HEAD, not the checked inputs.

    Preserve the original verified HEAD; do not claim compilation at the newer
    commit. Strict same_identity remains appropriate during gate execution.
    """
    ignored = {"head", "tree", "identity_sha256"}
    return ({k: v for k, v in before.items() if k not in ignored} ==
            {k: v for k, v in after.items() if k not in ignored})


def atomic_json(path, document):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(json.dumps(document, sort_keys=True, indent=2).encode() + b"\n")
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def status_date(content):
    for line in content.decode("utf-8").splitlines():
        if line.startswith("- Generated at: "):
            value = line.removeprefix("- Generated at: ")
            dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
            return value
    raise VerificationError("Status artifact has no parseable generation date")


def phase_results(phase_dir):
    result = {}
    for label, argv in PHASES:
        record = json.loads((phase_dir / f"{label}.timing.json").read_text())
        expected = [part.replace("{phase_dir}", str(phase_dir)) for part in argv]
        recorded_argv = record.get("argv")
        if isinstance(recorded_argv, list):
            recorded_argv = ["COMPLETION_AUDIT_GATE_RESULTS_DIR=" +
                             str(Path(part.split("=", 1)[1]).resolve())
                             if isinstance(part, str) and part.startswith("COMPLETION_AUDIT_GATE_RESULTS_DIR=")
                             else part for part in recorded_argv]
        if recorded_argv != expected or record.get("label") != label:
            raise VerificationError(f"Gate command differs from policy: {label}")
        code = record.get("exit_code")
        seconds = record.get("duration_seconds")
        if type(code) is not int or type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds < 0:
            raise VerificationError(f"Invalid phase result: {label}")
        if (phase_dir / f"{label}.status").read_text().strip() != str(code):
            raise VerificationError(f"Gate result and exit-status artifact disagree: {label}")
        record["output_sha256"] = hashlib.sha256((phase_dir / f"{label}.out").read_bytes()).hexdigest()
        result[label] = record
    return result


def seal_evidence(directory):
    for path in directory.iterdir():
        if path.is_file():
            path.chmod(0o400)
    directory.chmod(0o500)


def validate_evidence(root, receipt, receipt_checksum):
    path = receipt["evidence_directory"]
    if not isinstance(path, str):
        raise VerificationError("Invalid evidence directory")
    directory = (root / path).resolve(strict=True)
    allowed = (root / "harness/v2/state/verification/checkpoints").resolve()
    if not directory.is_relative_to(allowed) or directory == allowed:
        raise VerificationError("Evidence directory escapes checkpoint storage")
    saved = json.loads((directory / "receipt.json").read_text())
    if saved.pop("receipt_sha256", None) != receipt_checksum or saved != receipt:
        raise VerificationError("Archived receipt differs from latest receipt")
    if hashlib.sha256((directory / "status.md").read_bytes()).hexdigest() != receipt["status"]["sha256"]:
        raise VerificationError("Archived status artifact changed after verification")
    if json.loads((directory / "source-before.json").read_text()) != receipt["identity"]:
        raise VerificationError("Archived source identity changed after verification")
    phases = receipt["phases"]
    if not isinstance(phases, dict) or set(phases) != {label for label, _ in PHASES}:
        raise VerificationError("Receipt does not contain all required phases")
    for label, _ in PHASES:
        recorded = phases[label]
        if file_sha256(directory / f"{label}.out") != recorded["output_sha256"]:
            raise VerificationError(f"Archived gate output changed after verification: {label}")
        if (directory / f"{label}.status").read_text().strip() != str(recorded["exit_code"]):
            raise VerificationError(f"Archived gate exit status changed after verification: {label}")
        timing = json.loads((directory / f"{label}.timing.json").read_text())
        if timing != {key: value for key, value in recorded.items() if key != "output_sha256"}:
            raise VerificationError(f"Archived gate timing changed after verification: {label}")


def publish_receipt(root, before_path, status_candidate, phase_dir, receipt_path=None):
    """Preserve all fresh evidence, rejecting source changes before publication."""
    root, phase_dir = Path(root).resolve(), Path(phase_dir).resolve()
    before = json.loads(Path(before_path).read_text())
    phases = phase_results(phase_dir)
    content = Path(status_candidate).read_bytes()
    generated_at = status_date(content)
    evidence = root / "harness/v2/state/verification/checkpoints" / (
        generated_at.replace(":", "").replace("-", "") + "-" + uuid.uuid4().hex)
    evidence.mkdir(parents=True, exist_ok=False)
    for label, _ in PHASES:
        for suffix in ("out", "status", "timing.json"):
            name = f"{label}.{suffix}"
            shutil.copyfile(phase_dir / name, evidence / name)
    (evidence / "status.md").write_bytes(content)
    atomic_json(evidence / "source-before.json", before)
    after = capture_identity(root)
    if not same_identity(before, after):
        atomic_json(evidence / "rejected.json", {"reason": "Source changed during integration gates",
                                                "before": before, "after": after})
        seal_evidence(evidence)
        raise VerificationError(f"Source changed during integration gates; evidence preserved at {evidence}")
    receipt = {"schema_version": SCHEMA_VERSION, "recorded_at": utc_now(),
               "status_date": generated_at, "identity": before,
               "status": {"path": STATUS_PATH, "sha256": hashlib.sha256(content).hexdigest()},
               "phases": phases, "gate_policy": GATE_POLICY,
               "evidence_directory": str(evidence.relative_to(root)),
               "completion_certified": False}
    receipt["receipt_sha256"] = digest(receipt)
    # Status and receipt may briefly differ. Readers fail closed on their hashes.
    destination = root / STATUS_PATH
    with tempfile.NamedTemporaryFile(dir=root, delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(content)
    try:
        os.replace(temporary, destination)
    finally:
        temporary.unlink(missing_ok=True)
    if not same_identity(before, capture_identity(root)):
        atomic_json(evidence / "rejected.json", {"reason": "Source changed during status publication"})
        seal_evidence(evidence)
        raise VerificationError(f"Source changed during status publication; evidence preserved at {evidence}")
    atomic_json(evidence / "receipt.json", receipt)
    seal_evidence(evidence)
    atomic_json(Path(receipt_path) if receipt_path else root / DEFAULT_RECEIPT, receipt)
    return receipt


def check_receipt(root, receipt_path=None):
    """Return cached/fresh or stale evidence, always completion_certified=False."""
    root = Path(root).resolve()
    result = {"verification": "cached", "freshness": "stale", "reasons": [],
              "verified_head": None, "verified_source_sha256": None,
              "status_date": None, "current_head": None,
              "head_changed_since_verification": False, "completion_certified": False}
    path = Path(receipt_path) if receipt_path else root / DEFAULT_RECEIPT
    try:
        receipt = json.loads(path.read_text())
        if not isinstance(receipt, dict) or receipt.get("schema_version") != SCHEMA_VERSION:
            raise VerificationError("Unrecognized verification receipt")
        checksum = receipt.pop("receipt_sha256", None)
        if checksum != digest(receipt):
            raise VerificationError("Verification receipt checksum mismatch")
        if receipt.get("gate_policy") != json.loads(canonical(GATE_POLICY)) or receipt.get("completion_certified") is not False:
            raise VerificationError("Receipt gate policy differs from current policy")
        previous = receipt["identity"]
        if not isinstance(previous, dict) or type(previous.get("clean")) is not bool:
            raise VerificationError("Invalid receipt source identity")
        saved_sha = previous.get("identity_sha256")
        if saved_sha != digest({k: v for k, v in previous.items() if k != "identity_sha256"}):
            raise VerificationError("Receipt source identity checksum mismatch")
        result.update(verified_head=previous["head"], verified_source_sha256=previous["source_sha256"],
                      status_date=receipt["status_date"])
        status = receipt["status"]
        if status["path"] != STATUS_PATH:
            raise VerificationError("Receipt refers to an unexpected status artifact")
        content = (root / STATUS_PATH).read_bytes()
        if hashlib.sha256(content).hexdigest() != status["sha256"] or status_date(content) != receipt["status_date"]:
            raise VerificationError("Status artifact changed after verification")
        validate_evidence(root, receipt, checksum)
        current = capture_identity(root)
        if not previous["clean"] or not current["clean"]:
            result["reasons"].append("Project source is dirty; cached evidence cannot be attributed to a clean HEAD")
        result["current_head"] = current["head"]
        result["head_changed_since_verification"] = previous["head"] != current["head"]
        if not equivalent_source(previous, current):
            result["reasons"].append("Source, dependency, toolchain, environment or gate policy changed")
        if not same_identity(current, capture_identity(root)):
            result["reasons"].append("Source changed while reading cached evidence")
        if not result["reasons"]:
            result["freshness"] = "fresh"
    except (VerificationError, OSError, KeyError, TypeError, ValueError) as exc:
        result["reasons"].append(str(exc))
    return result


def run_phase(label, phase_dir, argv):
    phase_dir = Path(phase_dir)
    phase_dir.mkdir(parents=True, exist_ok=True)
    started_at, started = utc_now(), time.monotonic()
    with (phase_dir / f"{label}.out").open("wb") as output:
        try:
            code = subprocess.run(argv, stdout=output, stderr=subprocess.STDOUT, check=False).returncode
        except OSError as exc:
            output.write(str(exc).encode() + b"\n")
            code = 127
    record = {"label": label, "argv": argv, "exit_code": code,
              "duration_seconds": round(time.monotonic() - started, 6),
              "started_at": started_at, "finished_at": utc_now()}
    (phase_dir / f"{label}.status").write_text(str(code) + "\n")
    atomic_json(phase_dir / f"{label}.timing.json", record)
    # A failing audit is evidence to report, so do not abort the other phases.
    return record


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    sub = parser.add_subparsers(dest="command", required=True)
    pinned = sub.add_parser("toolchain-path")
    pinned.add_argument("--snapshot", type=Path, required=True)
    snapshot = sub.add_parser("snapshot")
    snapshot.add_argument("--out", type=Path, required=True)
    read = sub.add_parser("read")
    read.add_argument("--receipt", type=Path)
    read.add_argument("--json", action="store_true")
    phase = sub.add_parser("run-phase")
    phase.add_argument("--label", required=True, choices=[label for label, _ in PHASES])
    phase.add_argument("--phase-dir", type=Path, required=True)
    phase.add_argument("argv", nargs=argparse.REMAINDER)
    publish = sub.add_parser("publish")
    publish.add_argument("--before", type=Path, required=True)
    publish.add_argument("--status", type=Path, required=True)
    publish.add_argument("--phase-dir", type=Path, required=True)
    publish.add_argument("--receipt", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "toolchain-path":
            identity = json.loads(args.snapshot.read_text())
            directories = {str(Path(value["path"]).parent) for value in identity["toolchain"]["binaries"].values()}
            if len(directories) != 1:
                raise VerificationError("Snapshot does not pin one toolchain bin directory")
            print(next(iter(directories)))
        elif args.command == "snapshot":
            atomic_json(args.out, capture_identity(args.root))
        elif args.command == "run-phase":
            run_phase(args.label, args.phase_dir, args.argv[1:] if args.argv[:1] == ["--"] else args.argv)
        elif args.command == "publish":
            receipt = publish_receipt(args.root, args.before, args.status, args.phase_dir, args.receipt)
            print(f"Wrote {STATUS_PATH}; full gate evidence: {receipt['evidence_directory']}")
        elif args.command == "read":
            result = check_receipt(args.root, args.receipt)
            if args.json:
                print(json.dumps(result, sort_keys=True, indent=2))
            else:
                print(f"Verification: cached ({result['freshness']})")
                print(f"Verified HEAD: {result['verified_head'] or 'unavailable'}")
                if result["head_changed_since_verification"]:
                    print(f"Current HEAD: {result['current_head']} (same checked source; no fresh compilation at this HEAD)")
                print(f"Verified source SHA256: {result['verified_source_sha256'] or 'unavailable'}")
                print(f"Status date: {result['status_date'] or 'unavailable'}")
                for reason in result["reasons"]:
                    print(f"Stale: {reason}")
                print("Completion: not certified by cached evidence; use a fresh exact theorem probe and full completion gate.")
            return int(result["freshness"] != "fresh")
    except (VerificationError, OSError, KeyError, TypeError, ValueError) as exc:
        print(f"Verification error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
