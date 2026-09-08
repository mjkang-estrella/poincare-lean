# Supplied whole-cell realization completed

Date: 2026-09-08. Branch: `worker/supplied-whole-cell-realization`.
Frozen base: `b36d267ffeeca7802cc871c61f281c66c88f24de`.
Verified proof head: `13dbedc92c728c7c159331e9c22726a9609ebfb8`.

All four task-14 targets compile at the displayed signatures in
`harness/reports/parametrization-plan-3.md`. This is a worker result awaiting
independent orchestrator review, not acceptance or integration.

The only new Lean file is `Poincare/Global/CartanSuppliedWholeCellRealization.lean`.
No existing Lean file, root import, audit wiring, or source definition changed.
The task-specific file scope takes precedence over the general HANDOFF update
instruction; this report contains the dated handoff instead.

## Mathematical result

- `endpoint_anchor` uses `state_anchor_eq_node`, the terminal time equation,
  and the path target equation to identify the reached state's anchor.
- `exists_subdivision` works for every path and every prescribed positive
  radius. It subordinates cells to path balls of half that radius, erases zero
  from the finite time set, and uses the landed sorted-sequence lemmas for
  strictness and the terminal tail. Bracketing each new cell in an old cell
  and the triangle inequality give control of every pair of its points.
  Degenerate terminal cells use positivity and zero distance.
- `exists_realization` first fixes that geometric subdivision at `S.mesh`.
  Its whole-cell bound supplies endpoint step bounds to the landed
  `exists_sticky_chain`. The returned realization stores the actual preferred
  schedule and `ReachableChain`, including supplied `Data` at every step.
- `exists_rootedRealization_with_wholeCellMesh` chooses these arbitrary-path
  realizations for the existing common rooted skeleton.

`Realization` does not require sticky policies, so later comparisons can quantify
across all valid realizations. Existence additionally returns the exact `Sticky`
property. No curvature, simple-connectivity, legacy generic-data certificate,
or chain-dependent mesh premise was added to these targets.

## Proof commits

Each lemma was committed after direct Lean verification.

```text
c3d838e4 Prove supplied realization endpoint anchor
992c6915 Construct strict whole-cell subdivisions for arbitrary paths
6427839d Realize supplied sticky chains on fixed whole-cell subdivisions
13dbedc9 Realize the common rooted skeleton with supplied whole-cell chains
```

## Verification and actual output

After each of the four proof additions:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedWholeCellRealization.lean
```

All four runs exited 0 with no output. Logs are `lean-01.log` through
`lean-04.log` under `/tmp/supplied-whole-cell-realization-evidence`.
There were no failed compiler attempts.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedWholeCellRealization
```

Exit 0. Final output:

```text
✔ [3623/3623] Built Poincare.Global.CartanSuppliedWholeCellRealization (2.0s)
Build completed successfully (3623 jobs).
```

The full `build.log` also contains replayed warnings from existing dependencies.
The new module emitted no warnings.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-whole-cell-realization-evidence/contracts.lean
```

Exit 0. This scratch file imports only the new module, enables
`autoImplicit false`, checks each displayed target as an `example` whose body
is the corresponding theorem, and prints every new theorem's axiom closure.
Actual output:

```text
'Poincare.CartanSuppliedWholeCellRealization.endpoint_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedWholeCellRealization.exists_subdivision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedWholeCellRealization.exists_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedWholeCellRealization.exists_rootedRealization_with_wholeCellMesh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Reproduce the exact probe after building the module:

```lean
import Poincare.Global.CartanSuppliedWholeCellRealization

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
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization
example : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R : Realization S initial p),
  R.endpoint.anchor = y := endpoint_anchor

#print axioms Poincare.CartanSuppliedWholeCellRealization.endpoint_anchor

example : ∀ {x y : M} (p : Path x y) (r : ℝ),
  0 < r → Nonempty (Subdivision (g := g) p r) := exists_subdivision

#print axioms Poincare.CartanSuppliedWholeCellRealization.exists_subdivision

example : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y),
  ∃ R : Realization S initial p,
    Sticky S.cover R.preferred (fun n => p (R.subdivision.time n)) initial R.chain := exists_realization

#print axioms Poincare.CartanSuppliedWholeCellRealization.exists_realization

example : ∀ (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g),
  Nonempty (RootedRealization S skeleton) := exists_rootedRealization_with_wholeCellMesh

#print axioms Poincare.CartanSuppliedWholeCellRealization.exists_rootedRealization_with_wholeCellMesh

end Poincare
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedWholeCellRealization.lean
git diff --check
git diff --check b36d267ffeeca7802cc871c61f281c66c88f24de HEAD
```

Token scan: exit 1, no output. Both diff checks: exit 0, no output.
The proof diff is retained at
`/tmp/supplied-whole-cell-realization-evidence/proof.diff`.
Full-project builds and root audits remain the orchestrator's integration gate.

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedWholeCellRealization.lean
```

After independent acceptance, freeze a commit containing this module before
dispatching task 15's subdivision transport. No Poincare completion claim is made.
