# Supplied patch policy worker result

Date: 2026-09-08. Branch: `worker/supplied-patch-policy`.
Frozen base: `101296215861401937ee215c750bf42019807d83`. Verified proof head: `849eed3e`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`, pinned Mathlib, cloned Lake cache.

All four task-13 targets are proved in the single new file
`Poincare/Global/CartanSuppliedPatchPolicy.lean`. This is a worker result
awaiting independent orchestrator review, not acceptance or integration.

## What was proved

- `select_valid` uses both covering witnesses when the preferred pair is
  invalid. The four definitions `fallback`, `select`, `policy`, and `Sticky`
  match the frozen task text exactly.
- `stepAvailable` promotes core membership to buffer membership and applies
  the landed H1 to the actual state's alignment. It holds for every
  node-anchored state and arbitrary target, including states outside the
  realized history.
- `exists_sticky_chain` recurses on a node-anchored state together with its
  external preferred label. Each step chooses actual supplied data and
  carries the selected label to the next stage. The initial preference and
  displayed retention recurrence hold by definitional equality. It assumes
  no permanent target-core membership and no pre-existing chain.
- `chains_eq` inducts on equal prefix states, applies landed switch control
  at the common state, and puts the next node in that open switch ball using
  the mesh bound. `successor_eq_of_eqOn_open` then identifies full successor
  states, including their alignments. The conclusion concerns the same node
  sequence, exactly as specified.

The new file imports `CartanSuppliedBufferedPairAgreement`, which imports
both earlier cover/switch modules and exposes the landed unconditional
curvature-facing `exists_switchControl`, and `CartanSuppliedReachableChain`.
No landed theorem was re-proved. No existing Lean file, root import, audit
wiring, task file, or `HANDOFF.md` was changed. This report supplies the
handoff within the task's explicit file scope. Global development,
subdivision transport, and Poincare completion are not asserted here.

## Verified commits

Each lemma was committed after direct Lean exited 0, in dependency order.

```text
f0b1a353 Prove supplied patch selection has valid core anchors
e8fbeb59 Prove supplied patch policy step availability for all anchored states
97b50871 Construct supplied chain and sticky preference schedule by joint recursion
849eed3e Prove supplied chain state equality across preferred label schedules
```

## Commands and actual results

Commands were run with `LEAN_NUM_THREADS=1`. A Python subprocess recorder
saved stdout/stderr and exit codes under
`/tmp/supplied-patch-policy-evidence/`; it did not alter the commands' results.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedPatchPolicy.lean
```

Four incremental runs, after each new theorem, all exited 0 with no output.
Logs: `select-01.log`, `step-01.log`, `sticky-01.log`, `chains-01.log`.
The final run contained all four proofs. There were no failed compiler attempts.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedPatchPolicy
```

Exit 0. Actual final lines:

```text
✔ [3622/3622] Built Poincare.Global.CartanSuppliedPatchPolicy (2.8s)
Build completed successfully (3622 jobs).
```

The full `build-01.log` preserves replayed warnings from existing dependencies.
The new module emitted no warnings.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-patch-policy-evidence/signatures.lean
```

Exit 0. The probe checks each theorem against its frozen displayed signature,
with `autoImplicit false`, and checks its dependency closure. Actual output:

```text
'Poincare.CartanSuppliedPatchPolicy.select_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedPatchPolicy.stepAvailable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedPatchPolicy.exists_sticky_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedPatchPolicy.chains_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.CartanSuppliedUniformPatchSwitch.exists_switchControl.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  {g : Poincare.ClosedSmoothRiemannianMetric 3 M} [T2Space M] [CompactSpace M] [ConnectedSpace M] :
  Poincare.HasConstantSectionalCurvature3 g 1 →
    ∀ (B : Poincare.CartanSuppliedFinitePatchCover.QuantitativeCover g),
      Nonempty (Poincare.CartanSuppliedUniformPatchSwitch.SwitchControl B)
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedPatchPolicy.lean
```

No matches, exit 1. Log: `token-scan.log`.

```sh
git diff 101296215861401937ee215c750bf42019807d83 --check
```

No output, exit 0. Log: `diff-check.log`. The final proof diff is preserved
as `/tmp/supplied-patch-policy-evidence/final-proof.diff`.

`git diff --check` also exited 0 with no output after writing this report;
the log is `final-diff-check.log`.

The exact signature probe is reproduced below so review does not depend on
retaining temporary artifacts. Its proposition signatures were extracted
from task 13 of `harness/reports/parametrization-plan-3.md`.

```lean
import Poincare.Global.CartanSuppliedPatchPolicy

/-!
# Core selection and sticky supplied chains

The preferred label is external to the geometric state. Selection retains it
exactly while both anchors belong to its cores, and otherwise uses the cover.
The resulting policy supplies steps even at states outside its realized history.
-/

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain

namespace CartanSuppliedPatchPolicy
open CartanSuppliedFinitePatchCover CartanSuppliedUniformPatchSwitch

example : ∀ (B : QuantitativeCover g) (a : B.Label)
  (s : CartanChain.ChainState g), B.Valid (select B a s) s := select_valid

example : ∀ (S : System g) (a : ℕ → S.cover.Label) (nodes : ℕ → M),
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  StepAvailable (policy S.cover a) nodes := stepAvailable

example : ∀ (S : System g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g), initial.anchor = nodes 0 →
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  ∃ (a : ℕ → S.cover.Label)
    (c : ReachableChain (policy S.cover a) nodes initial),
    a 0 = fallback S.cover initial ∧ Sticky S.cover a nodes initial c := exists_sticky_chain

example : ∀ (S : System g) (a b : ℕ → S.cover.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g),
  initial.anchor = nodes 0 →
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  ∀ (c : ReachableChain (policy S.cover a) nodes initial)
    (d : ReachableChain (policy S.cover b) nodes initial), ∀ n, c.state n = d.state n := chains_eq

end CartanSuppliedPatchPolicy
end Poincare
#print axioms Poincare.CartanSuppliedPatchPolicy.select_valid
#print axioms Poincare.CartanSuppliedPatchPolicy.stepAvailable
#print axioms Poincare.CartanSuppliedPatchPolicy.exists_sticky_chain
#print axioms Poincare.CartanSuppliedPatchPolicy.chains_eq
#check Poincare.CartanSuppliedUniformPatchSwitch.exists_switchControl
```

No root build, root integration audits, merge, or task-acceptance update was
performed by this worker.

Exact first orchestrator action:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedPatchPolicy.lean`
on the proof commits above the recorded base, followed by the frozen gate
and independent diff/signature review.
