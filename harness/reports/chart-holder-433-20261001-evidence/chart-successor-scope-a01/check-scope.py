#!/usr/bin/env python3
"""Byte guard for the proposed chart API+h2 plus nine local proof regions.

No Lean check or proof acceptance is performed. Immutable original API spellings
and the exact previous h2 repair are replayed before matching the nine regions.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

FILE = 'Poincare/ChartIdentification.lean'
BASE = 'ff3ca4b6dce6499f44ab09a0d3ef8dd80a9417dc'
ORIGINAL = '55e4859b54acb9044d7966a12df7a12afa8b52fd'
ORIGINAL_SHA = 'efb4f9099267c5196736abf95201373f869cb16aad57c8395caee282430e42eb'
STARTING_SHA = '2e9280becdc909776f0fc3e216d74118b10b4f8ce155565e47210a9838539ac1'
APPLICATIONS = {88: ('I', 1), 110: ('I', 1), 170: ('I', 1), 211: ('I', 1),
  259: ("I'", 1), 342: ("I'", 1), 396: ("I'", 2), 430: ("I'", 1),
  474: ("I'", 1), 475: ("I'", 2), 476: ("I'", 2), 511: ("I'", 2), 516: ("I'", 1)}
UNFOLDINGS = {98: 1, 150: 1, 385: 1}
REGIONS = [(90, 90, 'extDerivFun_apply_chart.h1'),
  (93, 94, 'extDerivFun_apply_chart.h2'),
  (198, 201, 'isLocallyConstant_of_extDerivFun_eq_zero.hInv'),
  (211, 211, 'isLocallyConstant_of_extDerivFun_eq_zero.hzro_prime'),
  (269, 270, 'extDerivFun_apply_mlieBracket_chart.heq'),
  (306, 308, 'extDerivFun_apply_mlieBracket_chart.model_reduction'),
  (349, 350, 'extDerivFun_section_eventually_chart.heq'),
  (403, 404, 'extDerivFun_extDerivFun_chart.heq'),
  (480, 481, 'extDerivFun_apply_mlieBracket.heq')]
OLD = re.compile(rb"(?<![A-Za-z0-9_'])extDerivFun(?![A-Za-z0-9_'])")
NEW = re.compile(rb"(?<![A-Za-z0-9_'])mvfderiv(?![A-Za-z0-9_'])")
COMMAND = re.compile(rb'(?m)^[ \t]*(?:import|namespace|section|end|theorem|lemma|def|abbrev|opaque|axiom|constant|instance|variable|universe|attribute|export|initialize|elab|macro|syntax|set_option|local)\b')
FORBIDDEN = re.compile(rb"(?<![A-Za-z0-9_'])(?:sorry|admit|axiom|postulate|native_decide|set_option|letI|haveI)(?![A-Za-z0-9_'])")

class ScopeError(ValueError): pass

def require(test, message):
  if not test: raise ScopeError(message)

def source_at(root, commit):
  return subprocess.check_output(['git', '-C', str(root), 'show', commit + ':' + FILE])

def freeze(root):
  base = source_at(root, BASE)
  require(base == source_at(root, ORIGINAL), 'original/base source differs')
  require(hashlib.sha256(base).hexdigest() == ORIGINAL_SHA, 'original frozen hash differs')
  lines = base.splitlines(keepends=True)
  require(len(lines) == 610, 'original line count differs')
  a = u = 0
  for line, (model, wanted) in APPLICATIONS.items():
    lines[line-1], found = OLD.subn(('mvfderiv ' + model).encode(), lines[line-1])
    require(found == wanted, 'applied-operator manifest differs at line ' + str(line))
    a += found
  for line, wanted in UNFOLDINGS.items():
    lines[line-1], found = OLD.subn(b'mvfderiv', lines[line-1])
    require(found == wanted, 'unfolding manifest differs at line ' + str(line))
    u += found
  require((a, u) == (17, 3), '17+3 normalization inventory differs')
  starting = b''.join(lines[:61]) + b'    exact mfderivWithin_range_extChartAt_symm (I := I) (x := x)\n' + b''.join(lines[65:])
  require(hashlib.sha256(starting).hexdigest() == STARTING_SHA, 'normalized prior h2 candidate differs')
  lines = starting.splitlines(keepends=True)
  segments = []
  original_bodies = []
  last = 0
  for first, final, owner in REGIONS:
    segments.append(b''.join(lines[last:first-1]))
    original_bodies.append(b''.join(lines[first-1:final]))
    last = final
  segments.append(b''.join(lines[last:]))
  pattern = rb'\A' + re.escape(segments[0])
  for i, segment in enumerate(segments[1:]):
    pattern += rb'(?P<body' + str(i).encode() + rb'>[\s\S]*?)' + re.escape(segment)
  pattern += rb'\Z'
  return starting, segments, original_bodies, re.compile(pattern)

def check(candidate, frozen):
  _, _, _, pattern = frozen
  match = pattern.fullmatch(candidate)
  require(match is not None, 'a byte outside the nine local proof regions changed')
  for i, (_, _, owner) in enumerate(REGIONS):
    body = match.group('body' + str(i))
    require(body.strip(), 'empty proof region: ' + owner)
    require(body.endswith(b'\n'), 'proof region lacks final newline: ' + owner)
    require(b'--' not in body and b'/-' not in body, 'comment inserted into proof region: ' + owner)
    require(COMMAND.search(body) is None, 'declaration/scope command inserted: ' + owner)
    require(FORBIDDEN.search(body) is None, 'forbidden token, option or replacement instance inserted: ' + owner)
  require(len(OLD.findall(candidate)) == 1 and len(NEW.findall(candidate)) == 20,
    'exact old/new scalar operator inventory differs')


def replacements():
  return [b'    exact hf.mfderiv\n', b'    rfl\n',
    b'      simpa only [L] using!\n        (isInvertible_mfderiv_extChartAt (I := I) (x := x) (y := y) hySrc :\n          (mfderiv I ð(â, E)\n            ((extChartAt I x : PartialEquiv M E) : M â E) y).IsInvertible)\n',
    b'      simpa only [F, L] using! hzro\n', b'      rfl\n',
    """  simp only [I'.range_eq_univ, mpullbackWithin_univ]
  have hbr := congrFun (lieBracketWithin_univ (𝕜 := ℝ)
    (V := (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm X : E' → E'))
    (W := (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm Y : E' → E')))
    (extChartAt I' x x)
  rw [hbr, fderiv_apply_lieBracket_of_isSymmSndFDerivAt hFc hsymm
    (hpull Y hY) (hpull X hX), hc X, hc Y]
""".encode(), b'      rfl\n', b'      rfl\n', b'      rfl\n']

def join(segments, bodies):
  result = segments[0]
  for body, segment in zip(bodies, segments[1:]): result += body + segment
  return result

def selftest(frozen):
  starting, segments, bodies, _ = frozen
  positive = join(segments, replacements())
  tests = [('starting_retained_api_h2_candidate', starting, True),
    ('positive_all_nine_repairs', positive, True),
    ('missing_api_normalization', positive.replace(b'mvfderiv I f', b'extDerivFun f', 1), False),
    ('wrong_supplied_model', positive.replace(b'mvfderiv I f', b"mvfderiv I' f", 1), False),
    ('changed_h2_prior_repair', positive.replace(b'exact mfderivWithin_range_extChartAt_symm (I := I) (x := x)', b'rfl', 1), False),
    ('changed_public_header', positive.replace(b'theorem extDerivFun_apply_chart', b'theorem ChangedChart', 1), False),
    ('changed_local_header', positive.replace(b'have h1 : mfderiv% f x =', b'have h1 : mfderiv% f x + 0 =', 1), False),
    ('changed_import', positive.replace(b'import Poincare.FlatModelConnection', b'import Poincare.RiemannCurvatureOperator', 1), False),
    ('changed_untouched_proof', positive.replace(b'  exact key _\n', b'  rfl\n', 1), False)]
  for i, (_, _, owner) in enumerate(REGIONS):
    altered = list(replacements()); altered[i] = b'  set_option backward.isDefEq.respectTransparency false in\n' + altered[i]
    tests.append(('option_in_' + owner, join(segments, altered), False))
    altered = list(replacements()); altered[i] = b'  letI : Prop := True\n' + altered[i]
    tests.append(('replacement_instance_in_' + owner, join(segments, altered), False))
  altered = list(replacements()); altered[0] = b'    -- new comment\n' + altered[0]
  tests.append(('comment_inserted', join(segments, altered), False))
  altered = list(replacements()); altered[0] = b'theorem escaped : True := by trivial\n'
  tests.append(('declaration_escape', join(segments, altered), False))
  result = []
  for name, source, wanted in tests:
    try: check(source, frozen); accepted = True; reason = 'accepted'
    except ScopeError as error: accepted = False; reason = str(error)
    result.append(dict(case=name, expected_accept=wanted, accepted=accepted,
      passed=accepted == wanted, diagnostic=reason, candidate_sha256=hashlib.sha256(source).hexdigest()))
  return result

def main():
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument('root', nargs='?', type=Path, default=Path.cwd())
  parser.add_argument('--self-test', action='store_true')
  args = parser.parse_args()
  try:
    root = args.root.resolve(); frozen = freeze(root)
    result = dict(root=str(root), base=BASE, original=ORIGINAL, file=FILE,
      original_sha256=ORIGINAL_SHA, starting_dirty_source_sha256=STARTING_SHA,
      applied_operator_changes=17, unfolding_changes=3,
      prior_h2_body='exact mfderivWithin_range_extChartAt_symm (I := I) (x := x)',
      regions=[dict(first=a, last=b, owner=c) for a,b,c in REGIONS],
      lean_invoked=False, mode='self-test' if args.self_test else 'source-check')
    if args.self_test:
      result['cases'] = selftest(frozen)
      result['passed'] = all(r['passed'] for r in result['cases'])
    else:
      source=(root/FILE).read_bytes(); check(source, frozen)
      result.update(passed=True, candidate_sha256=hashlib.sha256(source).hexdigest())
    print(json.dumps(result, indent=2, sort_keys=True)); return 0 if result['passed'] else 1
  except (ScopeError, OSError, subprocess.CalledProcessError) as error:
    print(json.dumps(dict(passed=False,error=str(error)),sort_keys=True));return 1
if __name__ == '__main__': raise SystemExit(main())
