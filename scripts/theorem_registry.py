#!/usr/bin/env python3
"""Read checked Lean declarations and keep planned obligations separate."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


EXPORTER = Path(__file__).resolve().parent / "lean" / "TheoremRegistry.lean"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
DECLARATION_NAME = re.compile(r"[^\s.\x00-\x1f]+(?:\.[^\s.\x00-\x1f]+)*\Z")


class RegistryError(ValueError):
    pass


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def run(root, args):
    result = subprocess.run(args, cwd=root, text=True, capture_output=True,
                            env={**os.environ, "LEAN_NUM_THREADS": "1"})
    if result.returncode:
        raise RegistryError(f"Command failed ({result.returncode}): {' '.join(args)}\n"
                            f"{result.stdout}{result.stderr}")
    return result.stdout


def source_identity(root):
    """Pin all local Lean inputs, including untracked source and this exporter.

    Dependency revisions are fixed by lake-manifest.json. Dirty package trees
    are rejected so those revisions cannot silently describe different source.
    """
    root = Path(root).resolve()
    paths = run(root, ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"]).split("\0")
    # Ignored scratch modules can still be imported by Lean. Include their
    # bytes as well, while keeping Lake artifacts and git internals out.
    for directory, subdirectories, filenames in os.walk(root):
        subdirectories[:] = [name for name in subdirectories if name not in {".lake", ".git"}]
        paths.extend(str((Path(directory) / name).relative_to(root))
                     for name in filenames if name.endswith(".lean"))
    files = {}
    for name in sorted(set(paths)):
        if not name or not (name.endswith(".lean") or name in {
                "lean-toolchain", "lake-manifest.json", "lakefile.toml"}):
            continue
        path = root / name
        files[name] = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else "missing"
    packages = {}
    package_dir = root / ".lake" / "packages"
    if package_dir.exists():
        for package in sorted(package_dir.iterdir()):
            if not (package / ".git").exists():
                raise RegistryError(f"Package lacks git provenance: {package}")
            changed = run(package, ["git", "status", "--porcelain", "--untracked-files=no"])
            if changed:
                raise RegistryError(f"Package has modified tracked inputs: {package.name}")
            untracked = run(package, ["git", "ls-files", "--others", "-z", "--", "*.lean", "*.toml",
                                      "lean-toolchain", "lake-manifest.json"]).split("\0")
            if any(name and ".lake" not in Path(name).parts for name in untracked):
                raise RegistryError(f"Package has untracked source inputs: {package.name}")
            packages[package.name] = run(package, ["git", "rev-parse", "HEAD"]).strip()
    identity = {
        "commit": run(root, ["git", "rev-parse", "HEAD"]).strip(),
        "files": files, "packages": packages,
        "exporter_sha256": hashlib.sha256(EXPORTER.read_bytes()).hexdigest(),
        "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "lean_version": run(root, ["lake", "env", "lean", "--version"]).strip(),
    }
    identity["sha256"] = digest(identity)
    return identity


def fresh_export(root, modules, names=(), checks=(), include_module_declarations=True):
    if not modules or any(not MODULE_NAME.fullmatch(m) for m in modules):
        raise RegistryError("Provide valid Lean module names")
    before = source_identity(root)
    # This is a focused module build. Importing old oleans alone is not evidence
    # that the current source has these declarations.
    run(root, ["lake", "build", *modules])
    request = {"modules": modules, "names": list(names), "checks": list(checks),
               "includeModuleDeclarations": include_module_declarations}
    with tempfile.TemporaryDirectory(prefix="poincare-registry-") as temporary:
        config = Path(temporary) / "request.json"
        config.write_bytes(canonical(request))
        text = run(root, ["lake", "env", "lean", "--run", str(EXPORTER), str(config)])
    after = source_identity(root)
    if before != after:
        raise RegistryError("Source identity changed during export; discard the evidence")
    try:
        result = json.loads(text)
    except json.JSONDecodeError as exc:
        raise RegistryError(f"Lean exporter did not return JSON: {text[:2000]}") from exc
    result["source_identity"] = after
    result["requested_modules"] = modules
    return result


def save_catalog(root, modules, names, output):
    result = fresh_export(root, modules, names)
    result["artifact_sha256"] = digest(result)
    path = Path(output)
    path.parent.mkdir(parents=True, exist_ok=True)
    # A snapshot is append-only evidence. Choose a new filename to refresh it.
    with path.open("x") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    return result


def validate_catalog(root, catalog):
    payload = {key: value for key, value in catalog.items() if key != "artifact_sha256"}
    if catalog.get("artifact_sha256") != digest(payload):
        raise RegistryError("Catalog contents do not match its artifact digest")
    if catalog.get("source_identity") != source_identity(root):
        raise RegistryError("Catalog source identity is stale; create a new snapshot")


def search_catalog(catalog, query, limit=20):
    tokens = re.findall(r"\w+", query.casefold())
    if not tokens:
        raise RegistryError("Search query must contain words or symbols")
    found = []
    for record in catalog["declarations"]:
        if not record.get("present"):
            continue
        fields = [(record["name"], 5), (record.get("description", ""), 3),
                  (record["type"], 2), (" ".join(record["statement_dependencies"]), 1)]
        scores = [sum(weight for text, weight in fields if token in text.casefold()) for token in tokens]
        if all(scores):
            found.append({"score": sum(scores), **record})
    return sorted(found, key=lambda x: (-x["score"], x["name"]))[:limit]


def check_keys(obj, allowed, required, location):
    if not isinstance(obj, dict):
        raise RegistryError(f"{location} must be an object")
    unknown, missing = set(obj) - set(allowed), set(required) - set(obj)
    if unknown or missing:
        raise RegistryError(f"Invalid {location} fields: unknown={sorted(unknown)}, missing={sorted(missing)}")


def validate_mission(mission, require_pins=True):
    check_keys(mission,
               {"schema_version", "id", "base_commit", "modules", "endpoint", "nodes", "references", "description"},
               {"schema_version", "id", "modules", "endpoint", "nodes"}, "mission")
    if mission["schema_version"] != 1:
        raise RegistryError("Unsupported mission schema")
    if not isinstance(mission["id"], str) or not mission["id"]:
        raise RegistryError("Mission id must be nonempty")
    if "base_commit" in mission and (not isinstance(mission["base_commit"], str)
                                    or not re.fullmatch(r"[0-9a-f]{40}", mission["base_commit"])):
        raise RegistryError("Mission base_commit must be a full git commit id")
    if not isinstance(mission["modules"], list) or not mission["modules"] or any(
            not isinstance(m, str) or not MODULE_NAME.fullmatch(m) for m in mission["modules"]):
        raise RegistryError("Mission modules must be Lean module names")
    check_keys(mission["endpoint"], {"name", "type_symbol"}, {"name", "type_symbol"}, "endpoint")
    nodes = {}
    for node in mission["nodes"]:
        check_keys(node, {"id", "kind", "declaration", "description", "depends_on", "expected_type_symbol",
                          "expected_statement_sha256", "references"},
                   {"id", "kind", "description", "depends_on"}, "node")
        identifier = node["id"]
        if not isinstance(identifier, str) or not identifier or identifier in nodes:
            raise RegistryError(f"Invalid or duplicate node id: {identifier}")
        if node["kind"] not in {"checked", "obligation"}:
            raise RegistryError(f"Invalid node kind: {identifier}")
        if not isinstance(node["depends_on"], list) or any(not isinstance(x, str) for x in node["depends_on"]):
            raise RegistryError(f"Invalid dependencies for {identifier}")
        declaration = node.get("declaration")
        if declaration is not None and (not isinstance(declaration, str) or not DECLARATION_NAME.fullmatch(declaration)):
            raise RegistryError(f"Invalid Lean declaration for {identifier}")
        if node["kind"] == "checked" and not declaration:
            raise RegistryError(f"Checked node {identifier} must name its declaration")
        if node["kind"] == "obligation":
            if not isinstance(node.get("expected_type_symbol"), str) or not DECLARATION_NAME.fullmatch(node["expected_type_symbol"]):
                raise RegistryError(f"Obligation {identifier} needs an expected proposition symbol")
            pin = node.get("expected_statement_sha256")
            if require_pins and (not isinstance(pin, str) or not re.fullmatch(r"[0-9a-f]{64}", pin)):
                raise RegistryError(f"Obligation {identifier} needs a reviewed expected_statement_sha256")
        nodes[identifier] = node
    visiting, visited = set(), set()

    def visit(identifier):
        if identifier not in nodes:
            raise RegistryError(f"Dangling planned dependency: {identifier}")
        if identifier in visiting:
            raise RegistryError(f"Cycle in planned dependencies at {identifier}")
        if identifier in visited:
            return
        visiting.add(identifier)
        for dependency in nodes[identifier]["depends_on"]:
            visit(dependency)
        visiting.remove(identifier)
        visited.add(identifier)

    for identifier in nodes:
        visit(identifier)
    endpoints = [node for node in nodes.values() if node.get("declaration") == mission["endpoint"]["name"]
                 and node["kind"] == "obligation"
                 and node["expected_type_symbol"] == mission["endpoint"]["type_symbol"]]
    if len(endpoints) != 1:
        raise RegistryError("Mission must contain exactly one obligation for the exact endpoint and type")
    return nodes, endpoints[0]["id"]


def semantic_fingerprint(export, name):
    records = {record["name"]: record for record in export["semantic_declarations"]}
    seen = set()
    pending = [name]
    while pending:
        symbol = pending.pop()
        if symbol in seen:
            continue
        if symbol not in records:
            raise RegistryError(f"Missing semantic declaration {symbol}")
        if records[symbol].get("is_unsafe", True) or records[symbol].get("is_partial", True):
            raise RegistryError(f"Unsafe or partial declaration in expected statement: {symbol}")
        seen.add(symbol)
        pending.extend(records[symbol]["dependencies"])
    return digest([records[symbol] for symbol in sorted(seen)])


def mission_export(root, mission, require_pins=True):
    nodes, endpoint = validate_mission(mission, require_pins=require_pins)
    if "base_commit" in mission:
        run(root, ["git", "merge-base", "--is-ancestor", mission["base_commit"], "HEAD"])
    checks = [{"id": node["id"], "candidate": node.get("declaration") or "",
               "expected": node["expected_type_symbol"]}
              for node in nodes.values() if node["kind"] == "obligation"]
    names = [node["declaration"] for node in nodes.values() if node.get("declaration")]
    export = fresh_export(root, mission["modules"], names, checks, include_module_declarations=False)
    return export, nodes, endpoint


def graph_from_export(mission, export):
    """Only call with a fresh exporter result, never user-supplied evidence JSON."""
    nodes, endpoint_id = validate_mission(mission)
    records = {record["name"]: record for record in export["declarations"]}
    checks = {check["id"]: check for check in export["matches"]}
    output = []
    for identifier, node in nodes.items():
        record = records.get(node.get("declaration"), {})
        present = record.get("present", False)
        proof = (present and not record.get("is_unsafe", True) and not record.get("is_partial", True)
                 and record.get("is_proposition")
                 and record.get("kind") in {"theorem", "definition", "opaque"})
        permitted = proof and set(record.get("axioms", [])) <= ALLOWED_AXIOMS
        if node["kind"] == "obligation":
            actual_pin = semantic_fingerprint(export, node["expected_type_symbol"])
            if actual_pin != node["expected_statement_sha256"]:
                raise RegistryError(f"Frozen statement changed for {identifier}")
            check = checks.get(identifier)
            if not check or check["candidate"] != (node.get("declaration") or "") or check["expected"] != node["expected_type_symbol"]:
                raise RegistryError(f"Missing or mismatched Lean evidence for {identifier}")
            closed = bool(permitted and check["candidate_present"] and check["exact_type_match"])
            state = "discharged" if closed else "open"
        else:
            closed = False  # Conditional reductions do not discharge planned obligations.
            if not present:
                raise RegistryError(f"Checked declaration is absent: {node['declaration']}")
            if not permitted:
                raise RegistryError(f"Checked declaration lacks an allowed proof: {node['declaration']}")
            state = "checked_with_hypotheses" if any(b["is_proposition"] for b in record["binders"]) else "checked"
        output.append({**node, "state": state, "discharged": closed,
                       "checked_declaration": record if present else None})
    open_nodes = [node["id"] for node in output if node["kind"] == "obligation" and not node["discharged"]]
    endpoint_verified = next(node["discharged"] for node in output if node["id"] == endpoint_id)
    return {"schema_version": 1, "mission": mission["id"], "mission_sha256": digest(mission),
            "source_identity": export["source_identity"], "nodes": output,
            "planned_edges": [{"from": n["id"], "to": d} for n in nodes.values() for d in n["depends_on"]],
            "checked_dependencies": [{"declaration": r["name"],
                                      "statement_dependencies": r["statement_dependencies"],
                                      "proof_dependencies": r["proof_dependencies"]}
                                     for r in records.values() if r.get("present")],
            "open_obligations": open_nodes, "endpoint_verified": endpoint_verified,
            "all_obligations_discharged": not open_nodes,
            "project_complete": False,
            "completion_note": "Registry evidence does not replace the clean-HEAD completion audit."}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    sub = parser.add_subparsers(dest="command", required=True)
    snapshot = sub.add_parser("snapshot", help="Build selected modules and save an append-only catalog")
    snapshot.add_argument("--module", action="append", required=True)
    snapshot.add_argument("--name", action="append", default=[])
    snapshot.add_argument("--output", type=Path, required=True)
    search = sub.add_parser("search", help="Search current catalog names, math descriptions, types, and dependencies")
    search.add_argument("catalog", type=Path)
    search.add_argument("query")
    search.add_argument("--limit", type=int, default=20)
    for command in ("graph", "fingerprint"):
        p = sub.add_parser(command)
        p.add_argument("--mission", type=Path, required=True)
        if command == "graph":
            p.add_argument("--require-closed", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.command == "snapshot":
            catalog = save_catalog(args.root, args.module, args.name, args.output)
            print(json.dumps({"path": str(args.output), "declarations": len(catalog["declarations"]),
                              "source_identity": catalog["source_identity"]["sha256"]}))
            return 0
        if args.command == "search":
            catalog = json.loads(args.catalog.read_text())
            validate_catalog(args.root, catalog)
            print(json.dumps(search_catalog(catalog, args.query, args.limit), ensure_ascii=False, indent=2))
            return 0
        mission = json.loads(args.mission.read_text())
        export, nodes, _ = mission_export(args.root, mission, require_pins=args.command != "fingerprint")
        if args.command == "fingerprint":
            print(json.dumps({"mission_sha256": digest(mission), "source_identity": export["source_identity"],
                              "pins": {n["id"]: semantic_fingerprint(export, n["expected_type_symbol"])
                                       for n in nodes.values() if n["kind"] == "obligation"}}, indent=2))
            return 0
        result = graph_from_export(mission, export)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 2 if args.require_closed and not result["all_obligations_discharged"] else 0
    except (RegistryError, OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"theorem registry: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
