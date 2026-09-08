"""Protect legacy payload contents, coverage sets, and shell failure mapping."""
from __future__ import annotations

import contextlib
import io
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import audit_payload_equivalence as payload


class AuditPayloadTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.blocks = payload.legacy_blocks(payload.LEGACY_REF)
        cls.legacy = {name: payload.git_show(payload.LEGACY_REF, f'scripts/{name}.sh')
                      for name in payload.LEGACY_SCRIPTS}

    def test_archived_payload_equivalence(self):
        self.assertEqual(payload.check(payload.LEGACY_REF, ROOT / 'audit', out=io.StringIO()), [])
        for name in payload.LEGACY_SCRIPTS:
            self.assertNotIn("<<'EOF'", (ROOT / f'scripts/{name}.sh').read_text())

    def test_generator_places_imports_first_and_round_trips(self):
        with tempfile.TemporaryDirectory() as tmp:
            with contextlib.redirect_stdout(io.StringIO()):
                payload.write(payload.LEGACY_REF, Path(tmp))
            self.assertEqual(payload.check(payload.LEGACY_REF, Path(tmp), out=io.StringIO()), [])
            for module in payload.MODULES:
                text = (Path(tmp) / module).read_text()
                self.assertTrue(text.startswith('import '))
                self.assertNotRegex(text[text.index('/-!'):], r'(?m)^import ')

    def test_removed_or_changed_contract_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / 'audit'
            shutil.copytree(ROOT / 'audit', target)
            path = target / 'PoincareAudit/Completion/DependencyContract.lean'
            original = path.read_text()
            for broken in [original.replace('  T2Space Poincare.ThreeSphere)', '  CompactSpace Poincare.ThreeSphere)', 1),
                           re.sub(r'^#guard_msgs.*\n', '', original, count=1, flags=re.M)]:
                with self.subTest(kind=broken[:40]):
                    self.assertNotEqual(broken, original)
                    path.write_text(broken)
                    problems = payload.check(payload.LEGACY_REF, target, out=io.StringIO())
                    self.assertTrue(any('DependencyContract.lean:' in p for p in problems), problems)

    def test_comment_only_manual_marker_is_not_dropped(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / 'audit'
            shutil.copytree(ROOT / 'audit', target)
            path = target / 'PoincareAudit/Semantic/Surface.lean'
            path.write_text(path.read_text().replace(
                '-- #check Poincare.mfderivWithin_extChartAt_symm_target_eq_range\n', ''))
            problems = payload.check(payload.LEGACY_REF, target, out=io.StringIO())
            self.assertTrue(any('manual coverage markers' in p for p in problems), problems)

    def test_per_audit_canonical_route_universes_match_legacy(self):
        pattern = r'Poincare\.canonical_completion_(?:payload|target|criterion)_of_completion_certificate_of_[A-Za-z0-9_]+'
        for script, group in [('axiom_audit', 'Axiom'), ('root_import_audit', 'Root'),
                              ('semantic_surface_audit', 'Semantic'), ('completion_audit', 'Completion')]:
            with self.subTest(script=script):
                modules = '\n'.join(p.read_text() for p in (ROOT / f'audit/PoincareAudit/{group}').glob('*.lean'))
                self.assertEqual(set(re.findall(pattern, self.legacy[script])), set(re.findall(pattern, modules)))

    def test_semantic_route_coverage_keeps_legacy_declarations(self):
        env = os.environ.copy()
        if not shutil.which('rg'):
            env['PATH'] = str(ROOT / 'scripts/bin') + ':' + env['PATH']
        source = (ROOT / 'scripts/semantic_surface_audit.sh').read_text()
        start = source.index("rg -P --no-filename -o '^(?:@")
        end = source.index(' > "$audit_surface_declarations"', start)
        result = subprocess.run(['sh', '-c', source[start:end]], cwd=ROOT, env=env,
                                capture_output=True, text=True, check=True)
        declarations = set(result.stdout.splitlines())
        old_tokens = set(re.findall(r'[A-Za-z0-9_]+', self.legacy['semantic_surface_audit']))
        modules = '\n'.join(p.read_text() for p in (ROOT / 'audit/PoincareAudit/Semantic').glob('*.lean'))
        new_tokens = set(re.findall(r'[A-Za-z0-9_]+', modules))
        self.assertGreater(len(declarations), 1000)
        self.assertEqual(declarations & old_tokens, declarations & new_tokens)
        # The scripts must actually consume those modules, not their own comments.
        self.assertIn("'[A-Za-z0-9_]+' audit/PoincareAudit/Semantic/*.lean", source)
        self.assertNotIn('"$0" |', source)

    def test_completion_explicit_route_tokens_match_appended_legacy_checks(self):
        legacy = "\n".join(self.blocks['completion.routes'])
        expected = set(re.findall(
            r"^[ \t]*#check (?:Poincare\.)?([A-Za-z0-9_]+)", legacy, flags=re.M))
        source = (ROOT / 'scripts/completion_audit.sh').read_text()
        end = source.index(' > "$explicit_check_tokens"')
        start = source.rfind('  rg -P ', 0, end)
        pipeline = source[start:end]
        env = os.environ.copy()
        if not shutil.which('rg'):
            env['PATH'] = str(ROOT / 'scripts/bin') + ':' + env['PATH']
        with tempfile.TemporaryDirectory() as tmp:
            generated = Path(tmp) / 'generated.lean'
            generated.write_text('import Poincare\n#check generated_declaration\n')
            env['explicit_check_file'] = str(generated)
            result = subprocess.run(['sh', '-c', pipeline], cwd=ROOT, env=env,
                                    capture_output=True, text=True, check=True)
        self.assertIn('#check coverage', legacy)
        self.assertEqual(set(result.stdout.splitlines()), expected | {'generated_declaration'})
        self.assertNotIn('coverage', result.stdout.splitlines())

    def test_completion_public_coverage_detects_a_missing_module_route(self):
        source = (ROOT / 'scripts/completion_audit.sh').read_text()
        start = source.index('  collect_canonical_completion_certificate_routes() {')
        end = source.index('\n}\n\ncheck_audit_surface_coverage', start)
        fragment = source[start:end]
        env = os.environ.copy()
        if not shutil.which('rg'):
            env['PATH'] = str(ROOT / 'scripts/bin') + ':' + env['PATH']
        with tempfile.TemporaryDirectory() as tmp:
            scratch = Path(tmp)
            route = 'canonical_completion_payload_of_completion_certificate_of_example'
            for group in ['Semantic', 'Completion', 'Root', 'Axiom']:
                directory = scratch / 'audit/PoincareAudit' / group
                directory.mkdir(parents=True)
                (directory / 'Checks.lean').write_text('#check Poincare.' + route + '\n')
            variables = re.findall(r'^  (canonical_[a-z_]+)=', source, flags=re.M)
            setup = '\n'.join(f'{name}="{scratch}/{name}"' for name in variables)
            for missing in [False, True]:
                if missing:
                    (scratch / 'audit/PoincareAudit/Root/Checks.lean').write_text(
                        '#check Poincare.' + route + '_different\n')
                result = subprocess.run(['sh', '-c', 'set -eu\nstatus=0\n' + setup + '\n' +
                                         fragment + '\nexit "$status"'], cwd=scratch, env=env,
                                        text=True, capture_output=True)
                self.assertEqual(result.returncode, int(missing), result.stderr)
                if missing:
                    self.assertIn('FAIL: canonical completion certificate routes lack public root import audit exposure', result.stdout)
                    self.assertIn('MISSING: ' + route, result.stdout)
                else:
                    self.assertIn('PASS: canonical completion certificate routes have public root import audit exposure', result.stdout)

    def axiom_result(self, error: str, code: int):
        text = (ROOT / 'scripts/axiom_audit.sh').read_text()
        tail = text[text.index('if ! lake build PoincareAudit.Axiom.Footprint'):]
        env = os.environ.copy()
        if not shutil.which('rg'):
            env['PATH'] = str(ROOT / 'scripts/bin') + ':' + env['PATH']
        env.update(ERROR=error, CODE=str(code))
        with tempfile.TemporaryDirectory() as tmp:
            env['output_file'] = str(Path(tmp) / 'build.log')
            return subprocess.run(['sh', '-c', '''set -eu
lake() { printf '%s\n' "$ERROR" >&2; return "$CODE"; }
sh() { return 0; }
''' + tail], env=env, capture_output=True, text=True)

    def test_axiom_build_errors_preserve_failure_classification_and_output(self):
        for error in ["nonstandard axiom 'sorryAx'", 'uses _sorry', 'proof_wanted',
                      'error: Poincare.poincare_conjecture unavailable']:
            with self.subTest(error=error):
                result = self.axiom_result(error, 1)
                self.assertEqual(result.returncode, 1)
                self.assertIn('FAIL: proof-placeholder or final-theorem dependency found in axiom footprint\n', result.stdout)
                self.assertIn(error, result.stdout)
                self.assertNotIn('AXIOMS:', result.stdout)
        for error in ['unknown constant Poincare.deleted', "nonstandard axiom 'custom'",
                      'error in Poincare.poincare_conjecture_extra']:
            with self.subTest(error=error):
                result = self.axiom_result(error, 7)
                self.assertEqual(result.returncode, 1)
                self.assertIn('FAIL: nonstandard axiom footprint detected\n', result.stdout)
                self.assertIn(error, result.stdout)

    def test_cached_axiom_success_has_same_sentinel_without_lake_noise(self):
        result = self.axiom_result('Build completed successfully.', 0)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, 'AXIOMS: local proof-bearing assembly surface uses only standard mathlib axioms\n')


if __name__ == '__main__':
    unittest.main()
