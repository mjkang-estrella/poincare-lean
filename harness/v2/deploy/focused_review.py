from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Sequence

from harness.v2.runtime.store import HarnessStore
from harness.v2.runtime.validation import statement_contract_probe_source


HEX40 = re.compile(r"[0-9a-f]{40}")
LEAN_COMMAND_PREFIX = ("env", "LEAN_NUM_THREADS=1", "lake", "env", "lean")
DECLARATION_PROBE_ARGV = [
    "env",
    "LEAN_NUM_THREADS=1",
    "lake",
    "env",
    "lean",
    "--stdin",
]


class FocusedReviewError(RuntimeError):
    pass


def _sha256_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def _write_once(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        offset = 0
        while offset < len(content):
            offset += os.write(descriptor, content[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.chmod(path, 0o400)


def _git(git: Path, worktree: Path, *arguments: str) -> str:
    result = subprocess.run(
        [str(git), "-C", str(worktree), *arguments],
        check=False,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        env={
            "PATH": "/usr/bin:/bin",
            "LANG": "C.UTF-8",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_ATTR_NOSYSTEM": "1",
            "GIT_PAGER": "cat",
            "PAGER": "cat",
        },
    )
    if result.returncode != 0:
        raise FocusedReviewError(
            f"git {' '.join(arguments)} failed ({result.returncode}): "
            f"{result.stderr[:512].strip()}"
        )
    return result.stdout.strip()


def _safe_lean_path(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or path.suffix != ".lean"
        or path == PurePosixPath("Poincare.lean")
        or not path.parts
        or path.parts[0] != "Poincare"
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise FocusedReviewError(f"non-focused Lean target is forbidden: {value!r}")
    return path


def _acceptance_kind(command: Sequence[str]) -> tuple[str, PurePosixPath | None]:
    if tuple(command[:5]) == LEAN_COMMAND_PREFIX and len(command) == 6:
        return "lean", _safe_lean_path(command[5])
    if len(command) == 4 and tuple(command[:2]) == ("rg", "--files-without-match"):
        if not command[2]:
            raise FocusedReviewError("forbidden-token scan requires a pattern")
        return "rg", _safe_lean_path(command[3])
    if len(command) == 5 and tuple(command[:3]) == (
        "rg",
        "--files-without-match",
        "-e",
    ):
        if not command[3]:
            raise FocusedReviewError("forbidden-token scan requires a pattern")
        return "rg", _safe_lean_path(command[4])
    if tuple(command[:3]) in {
        ("git", "diff", "--check"),
        ("git", "diff", "--quiet"),
    }:
        return "git", None
    if "lake" in command or "Poincare.lean" in command:
        raise FocusedReviewError(
            f"broad or unscoped acceptance command is forbidden: {list(command)!r}"
        )
    raise FocusedReviewError(f"unsupported focused acceptance command: {list(command)!r}")


def _cache_metadata(cache: Path, base_commit: str, base_tree: str) -> dict[str, Any]:
    manifest_path = cache / ".harness-cache.json"
    overrides_path = cache / ".harness-package-overrides.json"
    if cache.is_symlink() or not cache.is_dir():
        raise FocusedReviewError(f"immutable exact-base cache is missing: {cache}")
    for required in ("build", "config", "packages"):
        child = cache / required
        if child.is_symlink() or not child.is_dir():
            raise FocusedReviewError(f"immutable cache lacks real {required}/")
    try:
        raw = manifest_path.read_bytes()
        manifest = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise FocusedReviewError(f"cannot read immutable cache manifest: {error}") from error
    if (
        manifest.get("schema_version") != "poincare-lake-cache-v1"
        or manifest.get("base_commit") != base_commit
        or manifest.get("base_tree") != base_tree
    ):
        raise FocusedReviewError("immutable cache does not match the Job base commit/tree")
    try:
        overrides = overrides_path.read_bytes()
    except OSError as error:
        raise FocusedReviewError(f"cannot read immutable package overrides: {error}") from error
    if _sha256_bytes(overrides) != manifest.get("package_overrides_sha256"):
        raise FocusedReviewError("immutable package override digest mismatch")
    return json.loads(overrides)


def _materialize_package_overrides(
    document: dict[str, Any], cache: Path, destination: Path
) -> None:
    packages = document.get("packages")
    if not isinstance(packages, list) or not packages:
        raise FocusedReviewError("immutable package override manifest has no packages")
    rewritten = json.loads(json.dumps(document))
    for package in rewritten["packages"]:
        directory = package.get("dir")
        if not isinstance(directory, str) or not directory.startswith("/work/.lake/packages/"):
            raise FocusedReviewError("immutable package override has an unexpected path")
        package["dir"] = directory.replace("/work/.lake", str(cache), 1)
    _write_once(
        destination,
        (json.dumps(rewritten, sort_keys=True, separators=(",", ":")) + "\n").encode(),
    )


def _symlink_projection(source: Path, destination: Path) -> None:
    if source.is_symlink() or not source.is_dir():
        raise FocusedReviewError("cache has no real Poincare olean tree")
    destination.mkdir(parents=True, mode=0o700)
    for root, directories, files in os.walk(source, followlinks=False):
        relative = Path(root).relative_to(source)
        target_root = destination / relative
        target_root.mkdir(exist_ok=True, mode=0o700)
        for directory in directories:
            (target_root / directory).mkdir(exist_ok=True, mode=0o700)
        for filename in files:
            source_file = Path(root) / filename
            if source_file.is_symlink() or not source_file.is_file():
                raise FocusedReviewError(f"unsafe cached olean projection entry: {source_file}")
            os.symlink(source_file, target_root / filename)


def _run(
    argv: Sequence[str],
    *,
    cwd: Path,
    environment: dict[str, str],
    timeout_seconds: int,
) -> tuple[int, bytes, bytes]:
    try:
        result = subprocess.run(
            list(argv),
            cwd=cwd,
            env=environment,
            check=False,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
        )
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout if isinstance(error.stdout, bytes) else b""
        stderr = error.stderr if isinstance(error.stderr, bytes) else b""
        return 124, stdout, stderr + b"\nfocused review command timed out\n"


def _run_forbidden_token_scan(
    command: Sequence[str], *, cwd: Path
) -> tuple[int, bytes, bytes]:
    if len(command) == 4:
        pattern, relative = command[2], command[3]
    elif len(command) == 5:
        pattern, relative = command[3], command[4]
    else:  # The allowlist must have rejected this before execution.
        raise FocusedReviewError("invalid forbidden-token scan command")
    target = cwd / _safe_lean_path(relative)
    try:
        source = target.read_text(encoding="utf-8")
        compiled = re.compile(pattern)
    except (OSError, UnicodeDecodeError, re.error) as error:
        return 2, b"", f"forbidden-token scan failed: {error}\n".encode()
    if compiled.search(source) is not None:
        return 1, b"", b""
    return 0, f"{relative}\n".encode(), b""


def _command_environment() -> dict[str, str]:
    return {
        "PATH": "/usr/bin:/bin",
        "LANG": "C.UTF-8",
        "HOME": os.environ.get("HOME", "/nonexistent"),
        "LEAN_NUM_THREADS": "1",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_ATTR_NOSYSTEM": "1",
        "GIT_PAGER": "cat",
        "PAGER": "cat",
    }


def _record_streams(
    review_dir: Path, relative_prefix: str, stdout: bytes, stderr: bytes
) -> tuple[str, str]:
    stdout_relative = f"{relative_prefix}.stdout"
    stderr_relative = f"{relative_prefix}.stderr"
    _write_once(review_dir / stdout_relative, stdout)
    _write_once(review_dir / stderr_relative, stderr)
    return stdout_relative, stderr_relative


def _declaration_source(task: dict[str, Any], index: int, symbol: str) -> str:
    if task.get("schema_version") == "2.1":
        return statement_contract_probe_source(task["statement_contract"], [symbol])
    lines = ["import Poincare", f"#check {symbol}"]
    if index == 0:
        frozen_type = task["objective"].get("frozen_lean_type")
        if not isinstance(frozen_type, str) or not frozen_type.strip():
            raise FocusedReviewError("first declaration probe requires a frozen Lean type")
        lines.append(f"#check ({symbol} : {frozen_type})")
    return "\n".join(lines) + "\n"


def run_focused_review(job_id: str, reviewer: str, timeout_seconds: int) -> dict[str, str]:
    state = Path(os.environ["POINCARE_STATE_DIR"])
    integration = Path(os.environ["POINCARE_REPO_ROOT"])
    worktree_root = Path(os.environ["POINCARE_WORKTREE_ROOT"])
    cache_root = Path(os.environ["POINCARE_PI_LAKE_CACHE_ROOT"])
    toolchain = Path(os.environ["POINCARE_PI_TOOLCHAIN_ROOT"])
    git = Path(os.environ["HARNESS_PI_GIT"])
    store = HarnessStore(
        state,
        worktree_root=worktree_root,
        integration_root=integration,
        git_executable=git,
        git_sha256=os.environ.get("HARNESS_PI_GIT_SHA256"),
    )
    payload = store.get_job(job_id)
    job = payload["job"]
    runtime = payload["runtime"]
    if job["state"] != "reviewing":
        raise FocusedReviewError("focused review requires a reviewing Job")
    current_worker_owners = {
        scope["owner"] for scope in runtime.get("scopes", []) if scope.get("owner")
    }
    if reviewer in current_worker_owners:
        raise FocusedReviewError("Codex reviewer identity must differ from worker identities")
    task = store.get_task(job["task_id"], job["task_revision"])["task"]
    worktree = Path(job["workspace"]["worktree"]).resolve(strict=True)
    artifact_dir = Path(runtime["artifact_directory"]).resolve(strict=True)
    if worktree.parent != worktree_root.resolve(strict=True):
        raise FocusedReviewError("Job worktree is outside the configured worktree root")
    if _git(git, worktree, "status", "--porcelain=v1", "--untracked-files=all"):
        raise FocusedReviewError("reviewed Job worktree must be clean")
    accepted_commit = _git(git, worktree, "rev-parse", "HEAD^{commit}")
    accepted_tree = _git(git, worktree, "rev-parse", "HEAD^{tree}")
    if HEX40.fullmatch(accepted_commit) is None or HEX40.fullmatch(accepted_tree) is None:
        raise FocusedReviewError("reviewed Git identity is invalid")
    base_commit = task["base_commit"]
    base_tree = _git(git, integration, "rev-parse", f"{base_commit}^{{tree}}")
    if subprocess.run(
        [
            str(git),
            "-C",
            str(worktree),
            "merge-base",
            "--is-ancestor",
            base_commit,
            accepted_commit,
        ],
        check=False,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ).returncode != 0:
        raise FocusedReviewError("reviewed commit does not descend from the Task base")

    commands = task["acceptance"]["commands"]
    classified = [_acceptance_kind(command) for command in commands]
    changed_lean = {
        PurePosixPath(line)
        for line in _git(git, worktree, "diff", "--name-only", base_commit, "--").splitlines()
        if line.endswith(".lean")
    }
    lean_targets = [target for kind, target in classified if kind == "lean" and target]
    if not changed_lean or not changed_lean.issubset(set(lean_targets)):
        raise FocusedReviewError(
            "every changed Lean file must have an ordered focused acceptance command"
        )

    cache = cache_root / base_commit
    package_document = _cache_metadata(cache, base_commit, base_tree)
    lake = toolchain / "bin/lake"
    lean = toolchain / "bin/lean"
    if not lake.is_file() or lake.is_symlink() or not lean.is_file() or lean.is_symlink():
        raise FocusedReviewError("pinned Lean toolchain executables are unavailable")
    lake_link = worktree / ".lake"
    if os.path.lexists(lake_link):
        raise FocusedReviewError(
            "Job worktree already has a mutable or stale .lake; create a fresh Job worktree"
        )

    review_dir = Path(
        tempfile.mkdtemp(
            prefix=f"codex-focused-review-{accepted_commit[:12]}-",
            dir=artifact_dir,
        )
    )
    os.chmod(review_dir, 0o700)
    review_name = review_dir.name
    scratch = Path(tempfile.mkdtemp(prefix=f"poincare-{job_id}-focused-"))
    try:
        overrides = scratch / "package-overrides.json"
        _materialize_package_overrides(package_document, cache, overrides)
        os.symlink(cache, lake_link)
        environment = _command_environment()
        path_result = subprocess.run(
            [str(lake), f"--packages={overrides}", "env", "printenv", "LEAN_PATH"],
            cwd=worktree,
            env=environment,
            check=False,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=60,
        )
        if path_result.returncode != 0 or not path_result.stdout.strip():
            raise FocusedReviewError(
                f"could not derive cache-backed LEAN_PATH: {path_result.stderr[:512].strip()}"
            )
        base_lean_path = path_result.stdout.strip()
        overlay = scratch / "overlay"
        _symlink_projection(cache / "build/lib/lean/Poincare", overlay / "Poincare")
        projected_lean_path = f"{overlay}:{base_lean_path}"
        command_results: list[dict[str, Any]] = []
        actual_commands: list[dict[str, Any]] = []
        for index, (command, (kind, target)) in enumerate(zip(commands, classified, strict=True)):
            if kind == "lean":
                assert target is not None
                temporary_olean = scratch / f"command-{index}.olean"
                actual_argv = [str(lean), target.as_posix(), "-o", str(temporary_olean)]
                actual_environment = {**environment, "LEAN_PATH": projected_lean_path}
            elif kind == "rg":
                actual_argv = ["<internal-forbidden-token-scan>", *command[1:]]
                actual_environment = environment
            else:
                actual_argv = list(command)
                actual_environment = environment
            if kind == "rg":
                exit_code, stdout, stderr = _run_forbidden_token_scan(
                    command, cwd=worktree
                )
            else:
                exit_code, stdout, stderr = _run(
                    actual_argv,
                    cwd=worktree,
                    environment=actual_environment,
                    timeout_seconds=timeout_seconds,
                )
            stdout_path, stderr_path = _record_streams(
                review_dir, f"acceptance-commands/{index}", stdout, stderr
            )
            command_results.append(
                {
                    "argv": command,
                    "status": "passed" if exit_code == 0 else "failed",
                    "exit_code": exit_code,
                    "stdout_path": f"{review_name}/{stdout_path}",
                    "stderr_path": f"{review_name}/{stderr_path}",
                }
            )
            actual_commands.append(
                {
                    "contract_argv": command,
                    "executed_argv": [
                        item.replace(str(scratch), "<ephemeral-review>")
                        for item in actual_argv
                    ],
                    "exit_code": exit_code,
                    "stdout_path": f"{review_name}/{stdout_path}",
                    "stderr_path": f"{review_name}/{stderr_path}",
                }
            )
            if exit_code != 0:
                raise FocusedReviewError(
                    f"focused acceptance command {index} failed with exit {exit_code}; "
                    f"evidence: {review_name}/{stderr_path}"
                )
            if kind == "lean":
                assert target is not None
                projected_olean = overlay / target.with_suffix(".olean")
                if projected_olean.is_symlink():
                    projected_olean.unlink()
                projected_olean.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
                os.replace(temporary_olean, projected_olean)

        required_declarations = task["acceptance"].get("required_declarations", [])
        root_overlay: dict[str, Any] | None = None
        if required_declarations:
            root_olean = scratch / "Poincare.olean"
            root_exit, root_stdout, root_stderr = _run(
                [str(lean), "Poincare.lean", "-o", str(root_olean)],
                cwd=worktree,
                environment={**environment, "LEAN_PATH": projected_lean_path},
                timeout_seconds=timeout_seconds,
            )
            root_stdout_path, root_stderr_path = _record_streams(
                review_dir, "root-overlay/root", root_stdout, root_stderr
            )
            if root_exit != 0:
                raise FocusedReviewError(
                    f"focused root overlay failed with exit {root_exit}; "
                    f"evidence: {review_name}/{root_stderr_path}"
                )
            os.replace(root_olean, overlay / "Poincare.olean")
            root_overlay = {
                "argv": [str(lean), "Poincare.lean", "-o", "<ephemeral-overlay>"],
                "exit_code": root_exit,
                "stdout_path": f"{review_name}/{root_stdout_path}",
                "stderr_path": f"{review_name}/{root_stderr_path}",
            }

        declarations: list[dict[str, Any]] = []
        for index, symbol in enumerate(required_declarations):
            source = _declaration_source(task, index, symbol)
            try:
                probe = subprocess.run(
                    [str(lean), "--stdin"],
                    cwd=worktree,
                    env={**environment, "LEAN_PATH": projected_lean_path},
                    check=False,
                    input=source.encode(),
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=timeout_seconds,
                )
                exit_code, stdout, stderr = probe.returncode, probe.stdout, probe.stderr
            except subprocess.TimeoutExpired as error:
                exit_code = 124
                stdout = error.stdout if isinstance(error.stdout, bytes) else b""
                stderr = (error.stderr if isinstance(error.stderr, bytes) else b"") + (
                    b"\nfocused declaration probe timed out\n"
                )
            stdout_path, stderr_path = _record_streams(
                review_dir, f"declaration-probes/{index}", stdout, stderr
            )
            if exit_code != 0:
                raise FocusedReviewError(
                    f"declaration probe {index} failed with exit {exit_code}; "
                    f"evidence: {review_name}/{stderr_path}"
                )
            declarations.append(
                {
                    "symbol": symbol,
                    "source": source,
                    "source_sha256": _sha256_bytes(source.encode()),
                    "argv": DECLARATION_PROBE_ARGV,
                    "status": "passed",
                    "exit_code": 0,
                    "stdout_path": f"{review_name}/{stdout_path}",
                    "stdout_sha256": _sha256_bytes(stdout),
                    "stderr_path": f"{review_name}/{stderr_path}",
                    "stderr_sha256": _sha256_bytes(stderr),
                }
            )

        manifest = {
            "schema_version": "poincare.focused-review.v1",
            "job_id": job_id,
            "reviewer": reviewer,
            "base_commit": base_commit,
            "accepted_commit": accepted_commit,
            "accepted_tree": accepted_tree,
            "cache": str(cache),
            "lean_targets": [target.as_posix() for target in lean_targets],
            "commands": actual_commands,
            "root_overlay": root_overlay,
        }
        _write_once(
            review_dir / "focused-review.json",
            (json.dumps(manifest, sort_keys=True, separators=(",", ":")) + "\n").encode(),
        )
        gate = {
            "schema_version": "2.0",
            "status": "passed",
            "accepted_commit": accepted_commit,
            "accepted_tree": accepted_tree,
            "commands": command_results,
            "declarations": declarations,
        }
        gate_path = review_dir / "gate.json"
        _write_once(
            gate_path,
            (json.dumps(gate, sort_keys=True, separators=(",", ":")) + "\n").encode(),
        )
        return {
            "accepted_commit": accepted_commit,
            "gate_result": gate_path.relative_to(artifact_dir).as_posix(),
            "review_manifest": (review_dir / "focused-review.json")
            .relative_to(artifact_dir)
            .as_posix(),
        }
    finally:
        if lake_link.is_symlink():
            lake_link.unlink()
        shutil.rmtree(scratch, ignore_errors=True)


def main() -> int:
    os.umask(0o077)
    parser = argparse.ArgumentParser(
        description="Run one cache-backed Codex-owned focused Job review gate"
    )
    parser.add_argument("job_id")
    parser.add_argument("--reviewer", required=True)
    parser.add_argument("--timeout-seconds", type=int, default=900)
    arguments = parser.parse_args()
    if not 30 <= arguments.timeout_seconds <= 3600:
        parser.error("--timeout-seconds must be between 30 and 3600")
    try:
        result = run_focused_review(
            arguments.job_id, arguments.reviewer, arguments.timeout_seconds
        )
    except (FocusedReviewError, KeyError, OSError, ValueError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}, sort_keys=True))
        return 1
    print(json.dumps({"status": "passed", **result}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
