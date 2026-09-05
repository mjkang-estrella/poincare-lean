"""Regressions for the legacy shape-name convention, not mathematical proofs."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "shape_contract_audit.sh"


@unittest.skipUnless(shutil.which("rg"), "shape audit requires ripgrep")
class ShapeContractAuditTests(unittest.TestCase):
    def audit(self, source):
        with tempfile.TemporaryDirectory(prefix="poincare-shape-audit-") as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            (root / "Poincare").mkdir()
            shutil.copyfile(SCRIPT, root / "scripts" / SCRIPT.name)
            (root / "Poincare" / "Fixture.lean").write_text(source)
            return subprocess.run(
                ["sh", "scripts/shape_contract_audit.sh"], cwd=root,
                text=True, capture_output=True, check=False,
            )

    def test_method_is_not_misread_as_its_owning_type(self):
        result = self.audit(
            "structure Record where\n  witness : True\n"
            "def Record.ofSource (w : True) : Record := ⟨w⟩\n"
            "noncomputable def Record.toWitness (r : Record) : True := r.witness\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("qualified definition Record.ofSource", result.stdout)
        self.assertNotIn("missing record_eq", result.stdout)

    def test_unqualified_shape_still_requires_its_companion(self):
        result = self.audit("def Shape : Prop := True\n")
        self.assertEqual(result.returncode, 1)
        self.assertIn("missing shape_eq", result.stdout)

    def test_existing_shape_companion_passes(self):
        result = self.audit(
            "def Shape : Prop := True\n"
            "theorem shape_eq : Shape = True := rfl\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_method_does_not_hide_a_missing_real_shape_contract(self):
        result = self.audit(
            "def Shape : Prop := True\n"
            "def Shape.ofSource (h : Shape) : Shape := h\n"
        )
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout.count("missing shape_eq"), 1)


if __name__ == "__main__":
    unittest.main()
