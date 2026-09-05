"""Small, dependency-free validators for Harness v2 records.

The committed JSON Schemas remain the public contract.  These validators
implement the subset needed by the executable runtime without depending on a
third-party JSON Schema package.
"""

from __future__ import annotations

import math
import hashlib
import json
import os
import re
import stat
from datetime import datetime
from fnmatch import fnmatchcase
from pathlib import Path, PurePosixPath
from typing import Any, Iterable
from urllib.parse import parse_qsl, urlsplit


TASK_ID_RE = re.compile(r"^[a-z0-9][a-z0-9._-]{2,79}$")
JOB_ID_RE = re.compile(r"^[a-z0-9][a-z0-9._-]{2,119}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
RFC3339_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$"
)
LEAN_DECLARATION_PREFIX_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|theorem|lemma|axiom|opaque|abbrev|structure|inductive|class|instance|example)\b"
)
LEAN_NAME_RE = re.compile(r"^[A-Za-z_\u0080-\uffff][A-Za-z0-9_'\u0080-\uffff]*(?:\.[A-Za-z_\u0080-\uffff][A-Za-z0-9_'\u0080-\uffff]*)*$")
ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

TASK_STATES = {
    "proposed",
    "ready",
    "active",
    "accepted",
    "blocked",
    "superseded",
}
JOB_STATES = {
    "queued",
    "preparing",
    "running",
    "reviewing",
    "passed",
    "rejected",
    "blocked",
    "interrupted",
}
GATE_STATES = {"not_run", "passed", "failed"}


class RecordValidationError(ValueError):
    """Raised when a Task or Job record violates the v2 data contract."""


def _fail(path: str, message: str) -> None:
    raise RecordValidationError(f"{path}: {message}")


def _object(value: Any, path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        _fail(path, "must be an object")
    return value


def _exact_keys(
    value: dict[str, Any],
    path: str,
    required: Iterable[str],
    optional: Iterable[str] = (),
) -> None:
    required_set = set(required)
    allowed = required_set | set(optional)
    missing = sorted(required_set - value.keys())
    extra = sorted(value.keys() - allowed)
    if missing:
        _fail(path, f"missing required fields: {', '.join(missing)}")
    if extra:
        _fail(path, f"unknown fields: {', '.join(extra)}")


def _string(value: Any, path: str, *, nonempty: bool = True) -> str:
    if not isinstance(value, str):
        _fail(path, "must be a string")
    if nonempty and not value.strip():
        _fail(path, "must not be empty")
    return value


def _integer(value: Any, path: str, *, minimum: int = 1) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        _fail(path, "must be an integer")
    if value < minimum:
        _fail(path, f"must be at least {minimum}")
    return value


def _array(value: Any, path: str, *, min_items: int = 0) -> list[Any]:
    if not isinstance(value, list):
        _fail(path, "must be an array")
    if len(value) < min_items:
        _fail(path, f"must contain at least {min_items} item(s)")
    return value


def _string_array(value: Any, path: str, *, min_items: int = 0) -> list[str]:
    result = _array(value, path, min_items=min_items)
    for index, item in enumerate(result):
        _string(item, f"{path}[{index}]")
    return result


def _matches(value: Any, path: str, pattern: re.Pattern[str]) -> str:
    text = _string(value, path)
    if pattern.fullmatch(text) is None:
        _fail(path, "has an invalid format")
    return text


def _date_time(value: Any, path: str) -> str:
    text = _string(value, path)
    if RFC3339_RE.fullmatch(text) is None:
        _fail(path, "must be an RFC 3339 date-time")
    try:
        parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        _fail(path, "must be an RFC 3339 date-time")
    if parsed.tzinfo is None:
        _fail(path, "must include a timezone")
    return text


def _relative_path(value: Any, path: str, *, allow_glob: bool) -> str:
    text = _string(value, path)
    if "\x00" in text or "\\" in text:
        _fail(path, "must be a POSIX path without NUL or backslash")
    if text.startswith(("/", "~")):
        _fail(path, "must be repository-relative")
    parts = text.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        _fail(path, "must not contain empty, '.' or '..' segments")
    if not allow_glob and any(char in text for char in "*?["):
        _fail(path, "must not contain glob metacharacters")
    # PurePosixPath catches a few odd path spellings while preserving globs.
    if PurePosixPath(text).is_absolute():
        _fail(path, "must be repository-relative")
    return text


_SENSITIVE_KEYS = {
    "apikey",
    "secret",
    "password",
    "authorization",
    "accesstoken",
    "refreshtoken",
    "bearertoken",
    "privatekey",
    "clientsecret",
    "token",
    "apitoken",
    "authtoken",
    "githubtoken",
    "xapikey",
}
_SECRET_TEXT = re.compile(
    r"(?:"
    r"\bsk-[A-Za-z0-9_-]{16,}"
    r"|\bhf_[A-Za-z0-9]{16,}"
    r"|\bgh[pousr]_[A-Za-z0-9]{20,}"
    r"|\bgithub_pat_[A-Za-z0-9_]{20,}"
    r"|\bglpat-[A-Za-z0-9_-]{16,}"
    r"|\beyJ[A-Za-z0-9_-]{8,}\.[A-Za-z0-9_-]{8,}\.[A-Za-z0-9_-]{8,}"
    r"|\bBearer\s+[A-Za-z0-9._~-]{16,}"
    r")"
)


def reject_secrets(value: Any, path: str = "record") -> None:
    """Reject common credential shapes before a record reaches disk."""

    if isinstance(value, dict):
        for key, child in value.items():
            normalized = re.sub(r"[^a-z0-9]", "", str(key).lower())
            if normalized in _SENSITIVE_KEYS:
                _fail(f"{path}.{key}", "secret-bearing fields are forbidden")
            reject_secrets(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_secrets(child, f"{path}[{index}]")
    elif isinstance(value, str) and _SECRET_TEXT.search(value):
        _fail(path, "looks like a credential and will not be stored")


def _validate_endpoint(value: Any, path: str) -> None:
    endpoint = _string(value, path)
    parsed = urlsplit(endpoint)
    if parsed.username is not None or parsed.password is not None:
        _fail(path, "must not contain URL credentials")
    for key, _ in parse_qsl(parsed.query, keep_blank_values=True):
        normalized = re.sub(r"[^a-z0-9]", "", key.lower())
        if normalized in _SENSITIVE_KEYS | {"token", "key"}:
            _fail(path, "must not contain credential query parameters")


def statement_contract_snapshot(contract: dict[str, Any]) -> str:
    """Digest the exact reviewed statements and source bytes, not review metadata."""
    snapshot = {key: contract[key] for key in ("imports", "declarations", "definition_files")}
    return hashlib.sha256(json.dumps(
        snapshot, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")).hexdigest()


def validate_statement_contract(contract: Any) -> dict[str, Any]:
    path = "statement_contract"
    contract = _object(contract, path)
    _exact_keys(contract, path, {"imports", "declarations", "definition_files", "author", "review"})
    imports = _string_array(contract["imports"], f"{path}.imports", min_items=1)
    for item in imports:
        _matches(item, f"{path}.imports", LEAN_NAME_RE)
    if len(imports) != len(set(imports)):
        _fail(f"{path}.imports", "must not contain duplicates")
    names = []
    for i, declaration in enumerate(_array(contract["declarations"], f"{path}.declarations", min_items=1)):
        label = f"{path}.declarations[{i}]"
        declaration = _object(declaration, label)
        _exact_keys(declaration, label, {"name", "lean_type"}, {"universes"})
        names.append(_matches(declaration["name"], f"{label}.name", LEAN_NAME_RE))
        frozen_type = _string(declaration["lean_type"], f"{label}.lean_type").strip()
        if LEAN_DECLARATION_PREFIX_RE.match(frozen_type) or frozen_type.startswith(("#", "import ")):
            _fail(f"{label}.lean_type", "must be a Lean type expression")
        if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", frozen_type):
            _fail(f"{label}.lean_type", "must not contain forbidden proof escapes")
        universes = _string_array(declaration.get("universes", []), f"{label}.universes")
        if len(universes) != len(set(universes)):
            _fail(f"{label}.universes", "must not contain duplicates")
        for level in universes:
            _matches(level, f"{label}.universes", LEAN_NAME_RE)
            if "." in level:
                _fail(f"{label}.universes", "must be simple names")
    if len(names) != len(set(names)):
        _fail(f"{path}.declarations", "must cover each declaration exactly once")
    paths = []
    for i, entry in enumerate(_array(contract["definition_files"], f"{path}.definition_files", min_items=1)):
        label = f"{path}.definition_files[{i}]"
        entry = _object(entry, label)
        _exact_keys(entry, label, {"path", "sha256"})
        paths.append(_relative_path(entry["path"], f"{label}.path", allow_glob=False))
        _matches(entry["sha256"], f"{label}.sha256", SHA256_RE)
    if len(paths) != len(set(paths)):
        _fail(f"{path}.definition_files", "must not contain duplicate paths")
    _string(contract["author"], f"{path}.author")
    review = _object(contract["review"], f"{path}.review")
    _exact_keys(review, f"{path}.review", {
        "reviewer", "method", "snapshot_sha256", "report_path", "report_sha256", "verdict"
    })
    _string(review["reviewer"], f"{path}.review.reviewer")
    if review["reviewer"].strip() == contract["author"].strip():
        _fail(f"{path}.review.reviewer", "must differ from statement author")
    if review["method"] != "blind-readback" or review["verdict"] != "approved":
        _fail(f"{path}.review", "requires an approved blind-readback review")
    _matches(review["snapshot_sha256"], f"{path}.review.snapshot_sha256", SHA256_RE)
    if review["snapshot_sha256"] != statement_contract_snapshot(contract):
        _fail(f"{path}.review.snapshot_sha256", "does not match every frozen statement and definition")
    _relative_path(review["report_path"], f"{path}.review.report_path", allow_glob=False)
    _matches(review["report_sha256"], f"{path}.review.report_sha256", SHA256_RE)
    reject_secrets(contract, path)
    return contract


def validate_statement_readback(contract: dict[str, Any], raw: bytes) -> None:
    """Check evidence integrity and explicit review decisions; not mathematical truth."""
    review = contract["review"]
    if hashlib.sha256(raw).hexdigest() != review["report_sha256"]:
        _fail("statement_readback", "report hash does not match reviewed bytes")
    try:
        report = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        _fail("statement_readback", f"invalid JSON: {error}")
    report = _object(report, "statement_readback")
    _exact_keys(report, "statement_readback", {
        "schema_version", "reviewer", "method", "snapshot_sha256", "verdict", "readback", "findings"
    })
    if report["schema_version"] != "1.0":
        _fail("statement_readback.schema_version", "must equal '1.0'")
    for key in ("reviewer", "method", "snapshot_sha256", "verdict"):
        if report[key] != review[key]:
            _fail(f"statement_readback.{key}", "does not match the frozen review")
    if report["findings"] != []:
        _fail("statement_readback.findings", "approved review must have no unresolved findings")
    names = []
    for entry in _array(report["readback"], "statement_readback.readback", min_items=1):
        entry = _object(entry, "statement_readback.readback")
        _exact_keys(entry, "statement_readback.readback", {"name", "mathematical_statement"})
        names.append(_string(entry["name"], "statement_readback.readback.name"))
        _string(entry["mathematical_statement"], "statement_readback.readback.mathematical_statement")
    if names != [item["name"] for item in contract["declarations"]]:
        _fail("statement_readback.readback", "must interpret every frozen declaration in order")
    reject_secrets(report, "statement_readback")


def validate_statement_context_bytes(contract: dict[str, Any], contents: dict[str, bytes]) -> None:
    """Validate exactly the bytes about to enter a worker prompt snapshot."""
    for entry in contract["definition_files"]:
        raw = contents.get(entry["path"])
        if raw is not None and hashlib.sha256(raw).hexdigest() != entry["sha256"]:
            _fail("statement_contract.definition_files", f"changed source: {entry['path']}")
    report = contents.get(contract["review"]["report_path"])
    if report is None:
        _fail("statement_contract.review", "missing blind readback report")
    validate_statement_readback(contract, report)


def validate_statement_pinned_sources(contract: dict[str, Any], root: Path) -> None:
    """Hash trusted frozen sources without exposing their bytes as worker context.

    Each read has the store's 8 MiB limit and forbids symlink components. The
    existing 2 MiB prompt-file cap and broker read scope remain unchanged.
    """
    maximum = 8 * 1024 * 1024
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    file_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    for entry in contract["definition_files"]:
        relative = _relative_path(entry["path"], "statement_contract.definition_files.path", allow_glob=False)
        path = root / relative
        parent = None
        descriptor = None
        try:
            parent = os.open(path.anchor, directory_flags)
            for component in path.parts[1:-1]:
                child = os.open(component, directory_flags, dir_fd=parent)
                os.close(parent)
                parent = child
            descriptor = os.open(path.parts[-1], file_flags, dir_fd=parent)
            before = os.fstat(descriptor)
            if not stat.S_ISREG(before.st_mode) or before.st_size > maximum:
                _fail("statement_contract.definition_files", f"source must be a regular file no larger than {maximum} bytes: {relative}")
            digest = hashlib.sha256()
            total = 0
            while True:
                chunk = os.read(descriptor, min(1024 * 1024, maximum + 1 - total))
                if not chunk:
                    break
                digest.update(chunk)
                total += len(chunk)
                if total > maximum:
                    _fail("statement_contract.definition_files", f"source exceeds {maximum} bytes: {relative}")
            after = os.fstat(descriptor)
            current = os.lstat(path)
            stable = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
            if (any(getattr(before, key) != getattr(after, key) for key in stable)
                    or stat.S_ISLNK(current.st_mode)
                    or (current.st_dev, current.st_ino) != (after.st_dev, after.st_ino)):
                _fail("statement_contract.definition_files", f"source changed while hashing: {relative}")
            if digest.hexdigest() != entry["sha256"]:
                _fail("statement_contract.definition_files", f"missing or changed source: {relative}")
        except OSError as error:
            _fail("statement_contract.definition_files", f"cannot safely read pinned source {relative}: {error}")
        finally:
            if descriptor is not None:
                os.close(descriptor)
            if parent is not None:
                os.close(parent)


def axiom_probe_source(names: list[str], imports: list[str]) -> str:
    """Lean-side fail-closed footprint check, also suitable for the final endpoint."""
    for value in names + imports:
        _matches(value, "probe.name", LEAN_NAME_RE)
    if not names:
        _fail("probe.names", "must not be empty")
    lines = [f"import {name}" for name in dict.fromkeys(["Lean"] + imports)]
    lines += ["open Lean Elab Command Meta", "set_option autoImplicit false"]
    allowed = ", ".join(json.dumps(name) + ".toName" for name in ALLOWED_AXIOMS)
    for name in names:
        literal = json.dumps(name, ensure_ascii=False)
        lines += [
            "run_cmd do",
            f"  let name := {literal}.toName",
            "  let _ ← getConstInfo name",
            "  let environment := (← getEnv).setExporting false",
            "  let mut pending : List Name := [name]",
            "  let mut seen : NameSet := {}",
            "  while !pending.isEmpty do",
            "    let current := pending.head!",
            "    pending := pending.tail!",
            "    if !seen.contains current then",
            "      seen := seen.insert current",
            "      let some info := environment.find? current |",
            '        throwError "missing dependency {current} in {name}"',
            "      if info.isUnsafe || info.isPartial then",
            '        throwError "unsafe or partial declaration {current} in {name}"',
            "      pending := info.getUsedConstantsAsSet.toList ++ pending",
            "      match info with",
            "      | .recInfo value =>",
            "        for rule in value.rules do",
            "          pending := rule.rhs.getUsedConstants.toList ++ pending",
            "      | .inductInfo value => pending := value.ctors ++ pending",
            "      | _ => pure ()",
            f"  let allowed : List Name := [{allowed}]",
            "  let footprint ← collectAxioms name",
            "  for dependency in footprint do",
            "    unless allowed.contains dependency do",
            '      throwError "forbidden axiom {dependency} in {name}"',
            f'  logInfo "AXIOM_CONTRACT_OK: {name}"',
        ]
    return "\n".join(lines) + "\n"


def statement_contract_probe_source(contract: dict[str, Any], names: list[str] | None = None) -> str:
    """Compare unapplied constant types at rigid universes, without coercions."""
    selected = contract["declarations"]
    if names is not None:
        selected = [entry for entry in selected if entry["name"] in names]
        if {entry["name"] for entry in selected} != set(names):
            _fail("probe.names", "contains a declaration outside the frozen contract")
    source = axiom_probe_source([entry["name"] for entry in selected], contract["imports"])
    levels = list(dict.fromkeys(level for entry in selected for level in entry.get("universes", [])))
    if levels:
        source += "universe " + " ".join(levels) + "\n"
    for entry in selected:
        literal = json.dumps(entry["name"], ensure_ascii=False)
        frozen = json.dumps(entry["lean_type"], ensure_ascii=False)
        universes = ", ".join(f"Level.param {json.dumps(level)}.toName" for level in entry.get("universes", []))
        source += "\n".join([
            "run_cmd liftTermElabM do",
            f"  let info ← getConstInfo {literal}.toName",
            f"  let levels : List Level := [{universes}]",
            "  unless info.levelParams.length == levels.length do",
            '    throwError "frozen universe arity mismatch for {info.name}"',
            f"  let parsedType ← match Parser.runParserCategory (← getEnv) `term {frozen} with",
            "    | .ok parsedType => pure parsedType",
            "    | .error error => throwError error",
            "  let expected ← Term.elabType parsedType",
            "  Term.synthesizeSyntheticMVarsNoPostponing",
            "  let expected ← instantiateMVars expected",
            "  if expected.hasMVar || expected.hasLevelMVar then",
            '    throwError "unresolved metavariables in frozen type for {info.name}"',
            "  let actual := info.type.instantiateLevelParams info.levelParams levels",
            "  unless ← isDefEq actual expected do",
            '    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"',
            f'  logInfo "FROZEN_CONTRACT_OK: {entry["name"]}"',
        ]) + "\n"
    return source


def validate_task(record: Any) -> dict[str, Any]:
    task = _object(record, "task")
    _exact_keys(
        task,
        "task",
        {
            "schema_version",
            "id",
            "revision",
            "status",
            "base_commit",
            "objective",
            "scope",
            "context",
            "acceptance",
            "stop_conditions",
            "budget",
        },
        {"supersedes", "accepted_commit", "statement_contract"},
    )
    if _string(task["schema_version"], "task.schema_version") not in {"2.0", "2.1"}:
        _fail("task.schema_version", "must equal '2.0' or '2.1'")
    strict = task["schema_version"] == "2.1"
    if not strict and "statement_contract" in task:
        _fail("task.statement_contract", "requires schema_version '2.1'")
    _matches(task["id"], "task.id", TASK_ID_RE)
    _integer(task["revision"], "task.revision")
    if task["status"] not in TASK_STATES:
        _fail("task.status", "is not a Harness v2 Task state")
    _matches(task["base_commit"], "task.base_commit", COMMIT_RE)

    objective = _object(task["objective"], "task.objective")
    _exact_keys(
        objective,
        "task.objective",
        {"title", "statement", "deliverables"},
        {"frozen_lean_type"},
    )
    _string(objective["title"], "task.objective.title")
    _string(objective["statement"], "task.objective.statement")
    _string_array(objective["deliverables"], "task.objective.deliverables", min_items=1)
    if "frozen_lean_type" in objective:
        frozen_type = _string(
            objective["frozen_lean_type"], "task.objective.frozen_lean_type"
        ).strip()
        if LEAN_DECLARATION_PREFIX_RE.match(frozen_type) or frozen_type.startswith(
            ("#", "import ", "namespace ", "section ")
        ):
            _fail(
                "task.objective.frozen_lean_type",
                "must be a Lean type expression, not declaration or command syntax",
            )

    scope = _object(task["scope"], "task.scope")
    _exact_keys(scope, "task.scope", {"allowed_paths", "forbidden_paths"})
    allowed = _string_array(scope["allowed_paths"], "task.scope.allowed_paths", min_items=1)
    forbidden = _string_array(scope["forbidden_paths"], "task.scope.forbidden_paths")
    for index, item in enumerate(allowed):
        _relative_path(item, f"task.scope.allowed_paths[{index}]", allow_glob=True)
    for index, item in enumerate(forbidden):
        _relative_path(item, f"task.scope.forbidden_paths[{index}]", allow_glob=True)
    if len(set(allowed)) != len(allowed):
        _fail("task.scope.allowed_paths", "must not contain duplicates")

    context = _object(task["context"], "task.context")
    _exact_keys(context, "task.context", {"files", "symbols", "depends_on"})
    context_files = _string_array(context["files"], "task.context.files")
    for index, item in enumerate(context_files):
        _relative_path(item, f"task.context.files[{index}]", allow_glob=False)
    _string_array(context["symbols"], "task.context.symbols")
    dependencies = _string_array(context["depends_on"], "task.context.depends_on")
    for index, dependency in enumerate(dependencies):
        _matches(dependency, f"task.context.depends_on[{index}]", TASK_ID_RE)
    if task["id"] in dependencies:
        _fail("task.context.depends_on", "a Task cannot depend on itself")

    acceptance = _object(task["acceptance"], "task.acceptance")
    _exact_keys(
        acceptance,
        "task.acceptance",
        {"commands", "forbidden_added_tokens"},
        {"required_declarations"},
    )
    commands = _array(acceptance["commands"], "task.acceptance.commands", min_items=1)
    for command_index, command in enumerate(commands):
        arguments = _array(
            command,
            f"task.acceptance.commands[{command_index}]",
            min_items=1,
        )
        for argument_index, argument in enumerate(arguments):
            _string(
                argument,
                f"task.acceptance.commands[{command_index}][{argument_index}]",
                nonempty=False,
            )
        if not arguments[0].strip():
            _fail(
                f"task.acceptance.commands[{command_index}][0]",
                "command executable must not be empty",
            )
    _string_array(
        acceptance["forbidden_added_tokens"],
        "task.acceptance.forbidden_added_tokens",
        min_items=1,
    )
    if "required_declarations" in acceptance:
        required_declarations = _string_array(
            acceptance["required_declarations"],
            "task.acceptance.required_declarations",
        )
        if required_declarations and not strict and not objective.get("frozen_lean_type", "").strip():
            _fail(
                "task.objective.frozen_lean_type",
                "is required when acceptance.required_declarations is nonempty",
            )

    if strict:
        contract = validate_statement_contract(task.get("statement_contract"))
        names = [entry["name"] for entry in contract["declarations"]]
        if names != acceptance.get("required_declarations"):
            _fail("task.acceptance.required_declarations", "must match every frozen declaration in order")
        if "frozen_lean_type" in objective:
            _fail("task.objective.frozen_lean_type", "use statement_contract declarations for schema 2.1")
        frozen_paths = [entry["path"] for entry in contract["definition_files"]]
        frozen_paths.append(contract["review"]["report_path"])
        for path in frozen_paths:
            if any(scopes_overlap(path, scope) for scope in allowed):
                _fail("task.scope.allowed_paths", f"must not permit edits to frozen context {path}")
        if contract["review"]["report_path"] not in context_files:
            _fail("task.context.files", "must include the pinned review report")

    _string_array(task["stop_conditions"], "task.stop_conditions", min_items=1)
    budget = _object(task["budget"], "task.budget")
    _exact_keys(
        budget,
        "task.budget",
        {"max_attempts", "wall_clock_minutes", "max_output_tokens", "disk_mb"},
    )
    for name in ("max_attempts", "wall_clock_minutes", "max_output_tokens", "disk_mb"):
        _integer(budget[name], f"task.budget.{name}")

    if "supersedes" in task:
        _matches(task["supersedes"], "task.supersedes", TASK_ID_RE)
    if "accepted_commit" in task:
        _matches(task["accepted_commit"], "task.accepted_commit", COMMIT_RE)
    if task["status"] == "accepted" and "accepted_commit" not in task:
        _fail("task.accepted_commit", "is required for an accepted Task")
    reject_secrets(task, "task")
    return task


def validate_job(record: Any) -> dict[str, Any]:
    job = _object(record, "job")
    _exact_keys(
        job,
        "job",
        {
            "schema_version",
            "id",
            "task_id",
            "task_revision",
            "attempt",
            "state",
            "backend",
            "workspace",
            "artifacts",
            "gate",
        },
        {"started_at", "heartbeat_at", "finished_at", "exit_reason", "accepted_commit"},
    )
    if job["schema_version"] != "2.0":
        _fail("job.schema_version", "must equal '2.0'")
    _matches(job["id"], "job.id", JOB_ID_RE)
    _matches(job["task_id"], "job.task_id", TASK_ID_RE)
    _integer(job["task_revision"], "job.task_revision")
    _integer(job["attempt"], "job.attempt")
    if job["state"] not in JOB_STATES:
        _fail("job.state", "is not a Harness v2 Job state")

    backend = _object(job["backend"], "job.backend")
    _exact_keys(
        backend,
        "job.backend",
        {"kind", "model", "model_revision", "endpoint", "sampling"},
    )
    if backend["kind"] != "leanstral":
        _fail("job.backend.kind", "must equal 'leanstral'")
    _string(backend["model"], "job.backend.model")
    _string(backend["model_revision"], "job.backend.model_revision")
    _validate_endpoint(backend["endpoint"], "job.backend.endpoint")
    sampling = _object(backend["sampling"], "job.backend.sampling")
    _exact_keys(
        sampling,
        "job.backend.sampling",
        {"max_tokens", "temperature"},
    )
    _integer(sampling["max_tokens"], "job.backend.sampling.max_tokens")
    temperature = sampling["temperature"]
    if (
        isinstance(temperature, bool)
        or not isinstance(temperature, (int, float))
        or not math.isfinite(float(temperature))
        or not 0 <= float(temperature) <= 2
    ):
        _fail(
            "job.backend.sampling.temperature",
            "must be a finite number between 0 and 2",
        )

    workspace = _object(job["workspace"], "job.workspace")
    _exact_keys(
        workspace,
        "job.workspace",
        {"base_commit", "worktree", "branch", "lease_owner", "lease_expires_at"},
    )
    _matches(workspace["base_commit"], "job.workspace.base_commit", COMMIT_RE)
    _string(workspace["worktree"], "job.workspace.worktree")
    branch = _string(workspace["branch"], "job.workspace.branch")
    if not branch.startswith("codex/"):
        _fail("job.workspace.branch", "must start with 'codex/'")
    _string(workspace["lease_owner"], "job.workspace.lease_owner")
    _date_time(workspace["lease_expires_at"], "job.workspace.lease_expires_at")

    artifacts = _object(job["artifacts"], "job.artifacts")
    _exact_keys(
        artifacts,
        "job.artifacts",
        {"directory", "prompt_sha256", "context_sha256"},
        {"patch_sha256"},
    )
    _relative_path(artifacts["directory"], "job.artifacts.directory", allow_glob=False)
    _matches(artifacts["prompt_sha256"], "job.artifacts.prompt_sha256", SHA256_RE)
    _matches(artifacts["context_sha256"], "job.artifacts.context_sha256", SHA256_RE)
    if "patch_sha256" in artifacts:
        _matches(artifacts["patch_sha256"], "job.artifacts.patch_sha256", SHA256_RE)

    for name in ("started_at", "heartbeat_at", "finished_at"):
        if name in job:
            _date_time(job[name], f"job.{name}")
    if "exit_reason" in job:
        _string(job["exit_reason"], "job.exit_reason", nonempty=False)

    gate = _object(job["gate"], "job.gate")
    _exact_keys(gate, "job.gate", {"status"}, {"result_path"})
    if gate["status"] not in GATE_STATES:
        _fail("job.gate.status", "must be not_run, passed, or failed")
    if "result_path" in gate:
        _relative_path(gate["result_path"], "job.gate.result_path", allow_glob=False)
    if "accepted_commit" in job:
        _matches(job["accepted_commit"], "job.accepted_commit", COMMIT_RE)
    if job["state"] == "passed" and gate["status"] != "passed":
        _fail("job.gate.status", "must be passed when Job state is passed")
    reject_secrets(job, "job")
    return job


def normalize_scope(scope: str) -> tuple[str, str]:
    """Return the canonical scope and its conservative literal prefix."""

    _relative_path(scope, "scope", allow_glob=True)
    normalized = str(PurePosixPath(scope))
    wildcard_index = len(normalized)
    for marker in ("*", "?", "["):
        index = normalized.find(marker)
        if index >= 0:
            wildcard_index = min(wildcard_index, index)
    literal = normalized[:wildcard_index]
    prefix = literal.rstrip("/")
    if (
        wildcard_index != len(normalized)
        and literal
        and not literal.endswith("/")
        and "/" in prefix
    ):
        prefix = prefix.rsplit("/", 1)[0]
    return normalized, prefix


def scopes_overlap(left: str, right: str) -> bool:
    """Conservatively decide whether two repository-relative scopes overlap."""

    left_scope, left_prefix = normalize_scope(left)
    right_scope, right_prefix = normalize_scope(right)
    if left_scope == right_scope:
        return True
    left_glob = any(marker in left_scope for marker in "*?[")
    right_glob = any(marker in right_scope for marker in "*?[")
    # Determining whether two arbitrary glob languages intersect is subtle.
    # Leases must never miss a possible collision, so two glob scopes always
    # conflict. False positives only reduce concurrency; false negatives can
    # permit concurrent edits to the same file.
    if left_glob and right_glob:
        return True
    if left_glob and not right_glob and fnmatchcase(right_scope, left_scope):
        return True
    if right_glob and not left_glob and fnmatchcase(left_scope, right_scope):
        return True

    def contains(parent: str, child: str) -> bool:
        return child == parent or child.startswith(parent + "/")

    if not left_prefix or not right_prefix:
        return True
    return contains(left_prefix, right_prefix) or contains(right_prefix, left_prefix)
