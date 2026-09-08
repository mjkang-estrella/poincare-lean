# Supplied restricted development: worker result

Date: 2026-09-08. Branch: `worker/supplied-restricted-development`.
Base: `7f689ff43383cd2091786f7768997466a15cce90`.
Verified proof head: `1251d1b0d3b0e388928af622fb965a1fcfccb9c6`.

All four task-18 targets are proved in the new
`Poincare/Global/CartanSuppliedRestrictedDevelopment.lean`. This is a worker
result awaiting independent orchestrator review, not acceptance or integration.

## Mathematical result

`development R` is exactly the target of the chosen rooted terminal state.
The fallback terminal germ contains its anchor and takes that target value,
by the supplied anchor laws and the landed endpoint anchor theorem.

For each `x`, intersect the short-path neighborhood with the terminal germ
source. For each `z` in that intersection, H1 supplies an actual terminal
`Data` witness at `z` in the fallback interpretation. The landed short-path
theorem identifies its full successor state with the realized short-path
endpoint. Concatenation transports from the actual terminal state at `x`,
using `q.cast hs rfl`. Source simple connectivity then compares the
concatenated rooted path with the chosen rooted path at `z`. Taking the
target projection proves equality of the total development and terminal germ
on the open neighborhood, with the required source inclusion.

Choosing these neighborhoods gives the restricted atlas. Both germs equal
`development R` on each overlap, so compatibility is derived. Restricting
each partial homeomorphism to its chosen open domain proves the diagonal
is a local homeomorphism. Its equality with `development R` gives the final
target. The purely topological diagonal theorem omits unused manifold,
separation, compactness, and connectedness section variables.

No geometric compatibility premise was added. The definitions and four
signatures retain the frozen contract. No maximal-source equality, global
selector continuity, or additional patch-coverage claim is used. Unit
recognition and unconditional Poincare completion are not asserted.

## Scope and commits

Only the named new Lean file and this report were added. Existing Lean files,
`Poincare.lean`, audit wiring, task files, and ledgers were not edited.
`HANDOFF.md` was read but not edited, following this task's narrower file scope.
The supplied isolated worker branch was retained as explicitly requested.
Initial status was clean; worktree inventory and HEAD were checked before editing.

Each lemma was committed after successful direct Lean elaboration, an empty
prohibited-token scan, and `git diff --check`:

| Commit | Verified lemma |
| --- | --- |
| `005cae54` | `terminal_anchor_laws` |
| `cb4bd9a4` | `development_eqOn_terminal_neighborhood` |
| `1cee2227` | `exists_restrictedAtlas` |
| `f97fedb7` | `isLocalHomeomorph_diagonal` |
| `1251d1b0` | `isLocalHomeomorph_development` |

## Commands and actual results

Run in `/private/tmp/poincare-workers/supplied-restricted-development`:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedRestrictedDevelopment.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedRestrictedDevelopment.lean
git diff --check
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedRestrictedDevelopment
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-restricted-development-evidence/signatures.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-restricted-development-evidence/axioms.lean
```

Final direct Lean: exit 0, no output (`lean-07.log`). Token scan: exit 1,
no matches. Diff check: exit 0, no output. Focused build: exit 0. It replayed
existing dependency warnings; the final lines were:

```text
✔ [3627/3627] Built Poincare.Global.CartanSuppliedRestrictedDevelopment (2.8s)
Build completed successfully (3627 jobs).
```

The four `example` probes use the signatures extracted from task 18 in
`harness/reports/parametrization-plan-3.md`, with each named theorem as its
proof body and `autoImplicit false`. They all passed, exit 0 with no output.
The reproducible extraction script is below.

The axiom command prints all five theorem closures and scans every public
module declaration using `Lean.collectAxioms`. It exits 0 with actual output:

```text
'Poincare.CartanSuppliedRestrictedDevelopment.terminal_anchor_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedRestrictedDevelopment.development_eqOn_terminal_neighborhood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedRestrictedDevelopment.exists_restrictedAtlas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedRestrictedDevelopment.isLocalHomeomorph_diagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedRestrictedDevelopment.isLocalHomeomorph_development' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
GATE_SCAN declarations=27 nonstandard=[]

```

Root build and root integration audits were not run; these remain the
orchestrator's integration checkpoint.

## Compiler attempts and evidence

All output is retained under `/tmp/supplied-restricted-development-evidence/`.
`proof.diff` is the complete proof diff from the recorded base. The source
and report commits provide the durable reviewable result.

| Log | Exit | Result |
| --- | --- | --- |
| `lean-01.log` | 0 | Anchor lemma, no output. |
| `lean-02.log` | 1 | Missing expected type for an inline tactic term. |
| `lean-03.log` | 0 | Neighborhood theorem after adding the explicit distance type. |
| `lean-04.log` | 0 | Atlas constructor, no output. |
| `lean-05.log` | 0 | Diagonal theorem, unused-section-variable warning. |
| `lean-06.log` | 0 | Diagonal theorem with unused section variables omitted, no output. |
| `lean-07.log` | 0 | All targets, no output. |
| `build.log` | 0 | Focused build, 3627 jobs. |
| `signatures.log` | 0 | Four frozen-signature probes, no output. |
| `axioms.log` | 0 | Five standard closures and 27 declarations, no nonstandard dependencies. |

The failed compiler output was exactly:

```text
Poincare/Global/CartanSuppliedRestrictedDevelopment.lean:101:11: error: invalid 'by' tactic, expected type has not been provided

```

The correction gave `hzend : dist z x < S.mesh` an explicit type before
applying `.trans_le hstep`; no statement was changed. The later warning
was resolved using `omit` on the purely topological theorem.

## Reproduce the frozen-signature probes

```sh
python3 - <<'PYPROBE'
from pathlib import Path
import re
report = Path('harness/reports/parametrization-plan-3.md').read_text()
section = report.split('## 18. ')[1].split('## 19. ')[0].split('```lean\n')[1].split('```')[0]
targets = section[section.index('theorem development_eqOn_terminal_neighborhood'):]
targets = targets.split('end CartanSuppliedRestrictedDevelopment')[0]
targets = re.sub(r'theorem (\w+)(.*?)(?=\n\ntheorem |\Z)',
    lambda m: 'example' + m[2].rstrip() + ' :=\n  ' + m[1] + '\n',
    targets, flags=re.S)
source = Path('Poincare/Global/CartanSuppliedRestrictedDevelopment.lean').read_text()
header = 'import Poincare.Global.CartanSuppliedRestrictedDevelopment\n\n'
header += source[source.index('set_option autoImplicit'):source.index('structure RestrictedAtlas')]
Path('/tmp/supplied-restricted-development-signatures.lean').write_text(
    header + targets + '\nend CartanSuppliedRestrictedDevelopment\nend Poincare\n')
PYPROBE
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-restricted-development-signatures.lean
```

Exact first orchestrator action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedRestrictedDevelopment.lean
```

Then independently inspect the diff from the recorded base, rerun the frozen
signatures and axiom scan, and decide acceptance before task 19 is dispatched.
