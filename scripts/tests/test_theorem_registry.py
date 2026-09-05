"""Regression checks include a real, isolated Lean fixture with no dependencies."""

import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "theorem_registry.py"
SPEC = importlib.util.spec_from_file_location("theorem_registry", SCRIPT)
registry = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(registry)


class MissionValidationTests(unittest.TestCase):
    def mission(self):
        return {"schema_version": 1, "id": "test", "modules": ["Fixture"],
                "endpoint": {"name": "Fixture.endpoint", "type_symbol": "Fixture.Goal"},
                "nodes": [{"id": "endpoint", "kind": "obligation", "declaration": "Fixture.endpoint",
                           "description": "Prove the full statement", "depends_on": [],
                           "expected_type_symbol": "Fixture.Goal", "expected_statement_sha256": "0" * 64}]}

    def test_valid_mission(self):
        nodes, endpoint = registry.validate_mission(self.mission())
        self.assertEqual(endpoint, "endpoint")
        self.assertEqual(len(nodes), 1)

    def test_cannot_claim_verification_in_json(self):
        for field in ["verified", "discharged", "status", "proof", "closed"]:
            mission = self.mission()
            mission["nodes"][0][field] = True
            with self.assertRaises(registry.RegistryError):
                registry.validate_mission(mission)

    def test_cycle_dangling_duplicate_and_missing_endpoint(self):
        for change in ["cycle", "dangling", "duplicate", "endpoint"]:
            mission = self.mission()
            if change == "cycle":
                mission["nodes"][0]["depends_on"] = ["endpoint"]
            elif change == "dangling":
                mission["nodes"][0]["depends_on"] = ["nonexistent"]
            elif change == "duplicate":
                mission["nodes"].append(copy.deepcopy(mission["nodes"][0]))
            else:
                mission["endpoint"]["name"] = "Fixture.other"
            with self.assertRaises(registry.RegistryError):
                registry.validate_mission(mission)

    def test_unpinned_statement_rejected(self):
        mission = self.mission()
        del mission["nodes"][0]["expected_statement_sha256"]
        with self.assertRaises(registry.RegistryError):
            registry.validate_mission(mission)

    def test_invalid_base_commit_rejected(self):
        mission = self.mission()
        mission["base_commit"] = "main"
        with self.assertRaisesRegex(registry.RegistryError, "full git commit"):
            registry.validate_mission(mission)


class LeanExporterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="poincare-registry-test-")
        cls.root = Path(cls.temporary.name)
        cls.fixture = '''namespace Fixture
/-- Reflexivity holds for every natural number. -/
def Goal : Prop := ∀ n : Nat, n = n
theorem helper (n : Nat) : n = n := rfl
theorem candidate : Goal := helper
theorem identity₃ : Goal := helper
theorem reduction (h : Goal) : Goal := h
def Impossible : Prop := ∀ _n : Nat, False
unsafe def unsafeCandidate (n : Nat) : False := unsafeCandidate n
def Dependency : Prop := True
def OtherGoal : Prop := Dependency
theorem endpoint : OtherGoal := True.intro
end Fixture
'''
        (cls.root / "Fixture.lean").write_text(cls.fixture)
        (cls.root / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage registryFixture\nlean_lib Fixture\n")
        (cls.root / "lean-toolchain").write_bytes((SCRIPT.parents[1] / "lean-toolchain").read_bytes())
        (cls.root / ".gitignore").write_text(".lake/\n")
        cls.command(["git", "init", "-q"])
        cls.command(["git", "add", "."])
        cls.command(["git", "-c", "user.name=Registry tests", "-c", "user.email=registry@example.invalid",
                     "commit", "-qm", "Freeze the independent exporter fixture"])
        # Lake creates its manifest on first build. Subsequent identity checks
        # then see one stable source tree before and after the exporter runs.
        cls.command(["lake", "build", "Fixture"])
        cls.mission = {"schema_version": 1, "id": "real-lean-fixture", "modules": ["Fixture"],
                       "endpoint": {"name": "Fixture.missing", "type_symbol": "Fixture.Goal"},
                       "nodes": [
                           {"id": "endpoint", "kind": "obligation", "declaration": "Fixture.missing",
                            "description": "Reserved endpoint remains absent", "depends_on": ["candidate"],
                            "expected_type_symbol": "Fixture.Goal"},
                           {"id": "candidate", "kind": "obligation", "declaration": "Fixture.candidate",
                            "description": "A complete checked proof", "depends_on": [],
                            "expected_type_symbol": "Fixture.Goal"},
                           {"id": "conditional", "kind": "obligation", "declaration": "Fixture.reduction",
                            "description": "Conditional reduction must remain open", "depends_on": [],
                            "expected_type_symbol": "Fixture.Goal"},
                           {"id": "dependent", "kind": "obligation", "declaration": "Fixture.endpoint",
                            "description": "Freeze a transitive definition", "depends_on": [],
                            "expected_type_symbol": "Fixture.OtherGoal"},
                           {"id": "checked-reduction", "kind": "checked", "declaration": "Fixture.reduction",
                            "description": "A checked theorem with an open mathematical hypothesis", "depends_on": []},
                           {"id": "unicode", "kind": "checked", "declaration": "Fixture.identity₃",
                            "description": "Unicode theorem names remain searchable", "depends_on": []},
                           {"id": "unsafe", "kind": "obligation", "declaration": "Fixture.unsafeCandidate",
                            "description": "Unsafe recursion is not a checked proof", "depends_on": [],
                            "expected_type_symbol": "Fixture.Impossible"},
                       ]}
        cls.export, _, _ = registry.mission_export(cls.root, cls.mission, require_pins=False)
        for node in cls.mission["nodes"]:
            if node["kind"] == "obligation":
                node["expected_statement_sha256"] = registry.semantic_fingerprint(cls.export, node["expected_type_symbol"])

    @classmethod
    def command(cls, command):
        result = subprocess.run(command, cwd=cls.root, text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return result.stdout

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_real_proof_dependencies_and_hypotheses(self):
        records = {record["name"]: record for record in self.export["declarations"]}
        self.assertIn("Fixture.helper", records["Fixture.candidate"]["proof_dependencies"])
        self.assertIn("Fixture.Goal", records["Fixture.candidate"]["statement_dependencies"])
        self.assertEqual(records["Fixture.reduction"]["binders"][0]["name"], "h")
        self.assertTrue(records["Fixture.reduction"]["binders"][0]["is_proposition"])
        self.assertEqual(records["Fixture.reduction"]["module"], "Fixture")
        self.assertIn("forallE", records["Fixture.reduction"]["type_expr"])
        self.assertEqual(records["Fixture.candidate"]["axioms"], [])

    def test_conditional_proof_and_missing_endpoint_do_not_close_graph(self):
        graph = registry.graph_from_export(self.mission, self.export)
        states = {node["id"]: node["state"] for node in graph["nodes"]}
        self.assertEqual(states["candidate"], "discharged")
        self.assertEqual(states["conditional"], "open")
        self.assertEqual(states["checked-reduction"], "checked_with_hypotheses")
        self.assertEqual(states["endpoint"], "open")
        self.assertFalse(graph["endpoint_verified"])
        self.assertFalse(graph["project_complete"])
        self.assertFalse(graph["all_obligations_discharged"])
        self.assertNotEqual(graph["planned_edges"], graph["checked_dependencies"])

    def test_unexpected_foundational_dependency_cannot_discharge(self):
        export = copy.deepcopy(self.export)
        candidate = next(record for record in export["declarations"] if record["name"] == "Fixture.candidate")
        candidate["axioms"] = ["Untrusted.fact"]
        graph = registry.graph_from_export(self.mission, export)
        self.assertIn("candidate", graph["open_obligations"])

    def test_unsafe_definition_and_unicode_declaration(self):
        graph = registry.graph_from_export(self.mission, self.export)
        records = {record["name"]: record for record in self.export["declarations"]}
        self.assertTrue(records["Fixture.unsafeCandidate"]["is_unsafe"])
        self.assertIn("unsafe", graph["open_obligations"])
        self.assertEqual(registry.search_catalog(self.export, "identity₃")[0]["name"], "Fixture.identity₃")

    def test_search_mathematical_description_and_type(self):
        results = registry.search_catalog(self.export, "reflexivity natural")
        self.assertEqual(results[0]["name"], "Fixture.Goal")
        self.assertTrue(registry.search_catalog(self.export, "Fixture.Goal"))

    def test_stale_and_tampered_catalog_rejected(self):
        catalog = copy.deepcopy(self.export)
        catalog["artifact_sha256"] = registry.digest(catalog)
        registry.validate_catalog(self.root, catalog)
        tampered = copy.deepcopy(catalog)
        tampered["declarations"][0]["type"] = "True"
        with self.assertRaisesRegex(registry.RegistryError, "artifact digest"):
            registry.validate_catalog(self.root, tampered)
        path = self.root / "Fixture.lean"
        path.write_text(self.fixture + "\n-- Source changes must invalidate cached evidence.\n")
        try:
            with self.assertRaisesRegex(registry.RegistryError, "stale"):
                registry.validate_catalog(self.root, catalog)
        finally:
            path.write_text(self.fixture)

    def test_ignored_lean_input_is_fingerprinted(self):
        before = registry.source_identity(self.root)
        ignored = self.root / "Ignored.lean"
        ignore_file = self.root / ".gitignore"
        previous = ignore_file.read_text()
        ignore_file.write_text(previous + "Ignored.lean\n")
        ignored.write_text("def ignoredInput : Nat := 1\n")
        try:
            after = registry.source_identity(self.root)
            self.assertNotEqual(before, after)
            self.assertIn("Ignored.lean", after["files"])
        finally:
            ignored.unlink()
            ignore_file.write_text(previous)

    def test_untracked_and_ignored_dependency_sources_rejected(self):
        packages = self.root / ".lake" / "packages"
        packages.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="untracked-package-", dir=packages) as temporary:
            package = Path(temporary)
            (package / ".gitignore").write_text("Ignored.lean\n")
            for command in [["git", "init", "-q"], ["git", "add", "."],
                            ["git", "-c", "user.name=Registry tests", "-c", "user.email=registry@example.invalid",
                             "commit", "-qm", "Record package provenance"]]:
                subprocess.run(command, cwd=package, check=True, capture_output=True)
            for name in ["Untracked.lean", "Ignored.lean"]:
                source = package / name
                source.write_text("def untrackedInput : Nat := 1\n")
                with self.assertRaisesRegex(registry.RegistryError, "untracked source inputs"):
                    registry.source_identity(self.root)
                source.unlink()

    def test_transitive_definition_change_rejected(self):
        export = copy.deepcopy(self.export)
        dependency = next(r for r in export["semantic_declarations"] if r["name"] == "Fixture.Dependency")
        dependency["value_expr"] = "different meaning"
        with self.assertRaisesRegex(registry.RegistryError, "Frozen statement changed"):
            registry.graph_from_export(self.mission, export)

    def test_source_rebuild_detects_changed_definition_under_same_name(self):
        path = self.root / "Fixture.lean"
        path.write_text(self.fixture.replace("def Dependency : Prop := True", "def Dependency : Prop := ∀ n : Nat, n = n")
                        .replace("theorem endpoint : OtherGoal := True.intro", "theorem endpoint : OtherGoal := helper"))
        try:
            changed, _, _ = registry.mission_export(self.root, self.mission)
            self.assertNotEqual(registry.semantic_fingerprint(self.export, "Fixture.OtherGoal"),
                                registry.semantic_fingerprint(changed, "Fixture.OtherGoal"))
            with self.assertRaisesRegex(registry.RegistryError, "Frozen statement changed"):
                registry.graph_from_export(self.mission, changed)
        finally:
            path.write_text(self.fixture)
            self.command(["lake", "build", "Fixture"])

    def test_graph_cli_rebuilds_and_rejects_actual_conditional_source(self):
        mission_path = self.root / "mission.json"
        mission_path.write_text(json.dumps(self.mission))
        result = subprocess.run(["python3", str(SCRIPT), "--root", str(self.root), "graph",
                                 "--mission", str(mission_path), "--require-closed"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertFalse(json.loads(result.stdout)["endpoint_verified"])


if __name__ == "__main__":
    unittest.main()
