# Supplied differential transfer completed

Date: 2026-09-08. Branch: `worker/supplied-differential-transfer`.
Frozen checkout base: `27dd5c7fb5c4912af8e7f050244051ce42e9a4c3`.
Verified proof head: `fdfe6c7ab5747425a01fef761a76a3aebbe38961`.

All ten frozen task-7 targets compile in
`Poincare/Global/CartanSuppliedDifferentialTransfer.lean`. The focused build,
module-wide public-declaration scan, independent frozen-signature probe,
prohibited-token scan, and whitespace checks pass. Every target has exactly
`[propext, Classical.choice, Quot.sound]` as its axiom closure.

This meets the task's exact successful stop condition and M5-glob-69 stop
condition (a). The result awaits independent orchestrator review. This worker
has not merged the branch or marked the task accepted.

The initial checkout was clean at the recorded base. `git worktree list
--porcelain` identified the assigned isolated branch at that commit; `main`
was also at that commit. The current checkout, rather than an older prose
ledger, fixed the base for this attempt.

## Mathematical result

`data_of_coordinateData` constructs the alignment from the stored metric
pullback. The old coordinate differential is the arbitrary framed equivalence
`(A.symm.trans (linear Q s)).trans B`. Invertible source and target chart
transition derivatives transport it to the successor anchors. The existing
chart-metric transport theorem proves that the resulting equivalence preserves
the anchor bilinear forms. The derivative chain rule and local inverse-chart
identities identify this operator with the actual supplied reanchored map.
No alignment premise is added.

`alignment_clm_eq_of_eventuallyEq`, `successor_eq_of_eqOn_open`, and
`successor_eq` use derivative uniqueness and equality of the dependent geometric
state. Open map agreement is transported through the successor's inverse chart
before comparing derivatives.

`ofGeneric` and `toGeneric` construct all fields of the existential adapters.
The additional host-chart composition cancels locally on its inverse domains;
strict endpoint derivatives transfer across that local equality. The inverse
function and chain rules reconstruct the Cartan-chart derivative. The original
metric pullback transfers at the identified coordinate points. Both adapters
preserve the normal vector and successor, without asserting equality of
selected source sets or analytic witnesses.

`patch_germ_eventuallyEq_generic` applies the retained normal comparison to
both patches. Its inverse-germ lemma pulls a neighborhood back through the
inverse target frame and normal chart, retains the second normal's source,
and applies the two partial inverse laws on their domains.

`generic_interval_equality` applies the old fixed-anchor theorem through
`toGeneric`, preserving the vector bound. Its output neighborhood also retains
the old predecessor and successor sources. `local_equality_transfer` shrinks
the neighborhood using the two stated map agreements and the old source
memberships. `patch_successor_at_anchor` combines the two-patch comparison,
`ofGeneric`, successor congruence, and `DifferentialSuccessorZero.anchorData_successor`.
It makes no anchor-successor claim for arbitrary interpretations.

The file contains ten public target theorems and nine private proof helpers,
with no new definitions. Only this new Lean file and this report are changed.
Existing Lean files, `Poincare.lean`, `HANDOFF.md`, and audit wiring are outside
this task's allowed scope and were not edited. H1/H2, mesh construction, and
recognition remain separate tasks.

## Verified commits

Each commit followed successful direct Lean elaboration of the cumulative
file. Every successful compiler log listed below is empty, exit 0.
All evidence paths in this report are under
`/tmp/supplied-differential-transfer-evidence/`.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialTransfer.lean
```

| Commit | Verified addition | Compiler log |
| --- | --- | --- |
| `528bff29` | Prove inverse chart-transition derivative composition for supplied transfer | `01-reverse.log` |
| `7b6fb217` | Identify reverse chart derivative with inverse framed equivalence | `02-inverse.log` |
| `0d6b3b99` | Prove supplied chart map identity on the explicit host source | `03-host-clean.log` |
| `f5c36206` | Construct supplied differential data from coordinate metric pullback | `04-constructor-clean.log` |
| `aeaf3365` | Prove cross-interpretation uniqueness of the derivative operator | `05-independence.log` |
| `28381d1b` | Prove geometric state equality from target and alignment operator equality | `06-state-ext.log` |
| `ff73637a` | Identify supplied differential successors under open map agreement | `07-open-equality-02.log` |
| `59e2653b` | Prove supplied successor witness independence | `08-successor-eq.log` |
| `c5962a8b` | Compare generic supplied endpoints with old exponential germs on their domains | `09-endpoint-comparison.log` |
| `b6b2a9bf` | Derive supplied chart strict differential from endpoint inverse and chain rules | `10-chart-chain-rule.log` |
| `26f51a86` | Identify old and supplied generic successor derivatives | `11-generic-successor-eq.log` |
| `f5448ea2` | Adapt old generic differential data to the supplied interpretation | `12-ofGeneric-02.log` |
| `a7280d3e` | Adapt supplied generic differential data back to old data | `13-toGeneric-01.log` |
| `f348770c` | Prove framed normal inverse germ comparison using local inverse domains | `14-inverse-germ-clean.log` |
| `805aab7c` | Identify retained patch frames with chart-transition derivatives | `15-patch-frame.log` |
| `2289efcb` | Prove two-patch Cartan germ agreement with the generic interpretation | `16-patch-germ-02.log` |
| `0384afeb` | Transfer the fixed-anchor interval equality to supplied generic successors | `17-generic-interval-01.log` |
| `7c26bf24` | Transfer local successor germ equality under explicit neighborhood agreements | `18-local-transfer-01.log` |
| `fdfe6c7a` | Prove the retained patch successor at its anchor is the predecessor | `19-patch-anchor-01.log` |

## Focused build and axiom gate

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh \
  /private/tmp/poincare-workers/supplied-differential-transfer \
  Poincare.Global.CartanSuppliedDifferentialTransfer \
  Poincare.CartanSuppliedDifferentialTransfer.data_of_coordinateData \
  Poincare.CartanSuppliedDifferentialTransfer.alignment_clm_eq_of_eventuallyEq \
  Poincare.CartanSuppliedDifferentialTransfer.successor_eq_of_eqOn_open \
  Poincare.CartanSuppliedDifferentialTransfer.successor_eq \
  Poincare.CartanSuppliedDifferentialTransfer.ofGeneric \
  Poincare.CartanSuppliedDifferentialTransfer.toGeneric \
  Poincare.CartanSuppliedDifferentialTransfer.patch_germ_eventuallyEq_generic \
  Poincare.CartanSuppliedDifferentialTransfer.generic_interval_equality \
  Poincare.CartanSuppliedDifferentialTransfer.local_equality_transfer \
  Poincare.CartanSuppliedDifferentialTransfer.patch_successor_at_anchor
```

Exit 0. Actual output from `gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/CartanSuppliedDifferentialTransfer.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.CartanSuppliedDifferentialTransfer ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3607/3607] Built Poincare.Global.CartanSuppliedDifferentialTransfer (7.2s)
Build completed successfully (3607 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=10 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.CartanSuppliedDifferentialTransfer.data_of_coordinateData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.alignment_clm_eq_of_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.successor_eq_of_eqOn_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.successor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.ofGeneric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.toGeneric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.patch_germ_eventuallyEq_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.generic_interval_equality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.local_equality_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.patch_successor_at_anchor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```

The warning is from an unchanged dependency. The new file's final direct
compiler check emitted no warnings. The scan counts the ten public declarations;
its implementation excludes private names. Each named target's transitive axiom
closure includes the private helpers used by its proof.

The focused build was serial. No full root build, integration audit, or
completion claim was made by this worker.

## Independent frozen-signature probe

The probe imports the built new module and checks each target as an `example`
at its full type extracted from the task-7 block of
`harness/reports/parametrization-plan-2.md`. Quantifier order and all frozen
premises remain unchanged. No implementation body is substituted for a target
in this probe. Each example's proof is the corresponding named theorem.

The generator is preserved as `make-probe.py`, and the complete generated
probe is `frozen-signatures.lean`. Reproduction:

```sh
python3 /tmp/supplied-differential-transfer-evidence/make-probe.py
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-differential-transfer-evidence/frozen-signatures.lean
```

Generator exit 0, actual output:

```text
Extracted all 10 frozen signatures verbatim as examples.
```

Lean exit 0. Actual output from `frozen-signatures.log`:

```text
'Poincare.CartanSuppliedDifferentialTransfer.data_of_coordinateData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.alignment_clm_eq_of_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.successor_eq_of_eqOn_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.successor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.ofGeneric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.toGeneric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.patch_germ_eventuallyEq_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.generic_interval_equality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.local_equality_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialTransfer.patch_successor_at_anchor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The generator can be reconstructed from the following exact code:

```python
from pathlib import Path
import re
report=Path('harness/reports/parametrization-plan-2.md').read_text()
blocks=re.findall(r'```lean\n(.*?)\n```',report,re.S)
preamble=blocks[0]
preamble=re.sub(r'^import .*\n','',preamble,flags=re.M)
block=next(b for b in blocks if b.startswith('namespace CartanSuppliedDifferentialTransfer\n'))
names=[]
def convert(m):
    name,typ=m.group(1),m.group(2)
    names.append(name)
    return f'example :{typ} := {name}\n\n#print axioms Poincare.CartanSuppliedDifferentialTransfer.{name}\n'
block=re.sub(r'theorem (\w+) :(.*?)(?=\n-- TARGET|\nend CartanSuppliedDifferentialTransfer)',convert,block,flags=re.S)
assert len(names)==10, names
probe='import Poincare.Global.CartanSuppliedDifferentialTransfer\n'+preamble+'\n'+block+'\nend Poincare\n'
Path('/tmp/supplied-differential-transfer-evidence/frozen-signatures.lean').write_text(probe)
Path('/tmp/supplied-differential-transfer-evidence/names.txt').write_text('\n'.join('Poincare.CartanSuppliedDifferentialTransfer.'+n for n in names)+'\n')
print('Extracted all 10 frozen signatures verbatim as examples.')
```

## Toolchain and source checks

```sh
lake env lean --version
```

Exit 0, actual output:

```text
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedDifferentialTransfer.lean
git diff --check
git diff 27dd5c7fb5c4912af8e7f050244051ce42e9a4c3 --check
```

Token scan: exit 1, no matches. Both whitespace checks: exit 0, no output.
The proof diff adds exactly one 723-line Lean file, with the two requested
imports. It is preserved as `proof.diff` and can be regenerated:

```sh
git diff 27dd5c7fb5c4912af8e7f050244051ce42e9a4c3 fdfe6c7ab5747425a01fef761a76a3aebbe38961 -- Poincare/Global/CartanSuppliedDifferentialTransfer.lean
```

## Compiler retries retained

All failed compiler output is preserved, including the contexts printed by
Lean. Every issue below was resolved before the corresponding proof commit.

| Log | Exit | Resolved issue |
| --- | --- | --- |
| `03-host.log` | 0 | Unused Hausdorff instance warning; omitted from the helper. |
| `04-constructor-01.log` | 1 | Structure-field layout, inverse-chart type inference, and use of `open_source` on a `PartialEquiv`. |
| `04-constructor-02.log` | 1 | Named-argument syntax conflicted with local `I` notation. |
| `04-constructor-03.log` | 0 | Simplification and unused-instance warnings; cleaned before commit. |
| `07-open-equality.log` | 1 | Composed map hypothesis needed `Function.comp_def` before rewriting. |
| `12-ofGeneric-01.log` | 1 | Strict derivative congruence takes the opposite equality orientation to ordinary derivative congruence. |
| `14-inverse-germ-01.log` | 0 | Unused manifold-instance warnings; omitted from the topological helper. |
| `16-patch-germ-01.log` | 1 | Composition evaluation and continuous-linear-map/equivalence coercions needed explicit normalization. |

There is no remaining unclosed chart-transition, metric-pullback, or
inverse-germ goal. No failed proof attempt remains in the delivered Lean file.

Exact first review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialTransfer.lean
```

Then independently rerun the focused gate and frozen-signature probe against
the recorded base and proof head. Acceptance and root integration belong to
the orchestrator.
