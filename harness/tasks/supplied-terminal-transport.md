# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-terminal-transport`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-terminal-transport_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-terminal-transport
Landed prerequisites on main: tasks 11-15 (`CartanSuppliedFinitePatchCover.lean`, `CartanSuppliedUniformPatchSwitch.lean` + `CartanSuppliedBufferedPairAgreement.lean` (`exists_switchControl` unconditional), `CartanSuppliedPatchPolicy.lean` (`policy`, `Sticky`, `stepAvailable`, `exists_sticky_chain`, `chains_eq`), `CartanSuppliedWholeCellRealization.lean` (`Subdivision`, `Realization`, `RootedRealization`, `endpoint_anchor`, `exists_subdivision`, `exists_realization`, `exists_rootedRealization_with_wholeCellMesh`), `CartanSuppliedSubdivisionTransport.lean` (`block_state_eq`, `refinement_chain_state_eq` for arbitrary monotone sampled chains, `refinement_state_eq`, `state_eq_of_constant_nodes`, `endpoint_eq_same_path`)). Task 16 (homotopy endpoints) is NOT landed and is NOT needed here; do not import or wait for it. Import and use the landed modules; do not re-prove landed theorems.

## Two necessary qualifications

“One patch per chart” is not a consequence of S6 or S7. Starting with one arbitrarily chosen patch at a representative of each member of a finite atlas need not cover the other points of those charts. The executable contract below instead constructs a finite refinement: choose a patch centered at every point, then a finite subcover of smaller open anchor neighborhoods. On the controlled source, every host `chartAt E (center i)` still belongs to the given finite atlas, but a host chart may be used by several patches. On the sphere, use the existing sphere instance and take a finite patch subcover in the same way. If exactly one patch per original chart is a frozen requirement, stop at that coverage gap; do not assert `ball_cover` from S7. This qualification follows from the exact `exists_patch` and `Patch.anchors` types in S6.

Likewise, H1/H2 is uniform on compact anchor sets, not on their whole surrounding open patch. Use an operating core `core i` and a larger compact buffer with `core i ⊆ interior (buffer i) ⊆ buffer i ⊆ anchors`. The policy retains a label while both current anchors remain in its operating cores; when either leaves, it switches. This is the precise quantitative meaning of re-anchoring within a patch until leaving its operating anchor set. Waiting until the boundary of the full open `Patch.anchors` would have no uniform H1 justification. S3/S4 also only retain the target in an open set unless the stronger `exists_uniform_domain_radius_into_open` clause is used.

A policy of type `ℕ → ChainState → Interpretation` cannot read a previous label from `ChainState`. Task 13 gives it an external preferred-label schedule, constructed together with one chain by recursion. For off-history states it has a covering fallback, so `StepAvailable` still holds for every state anchored at the node, as S5 requires. No patch label is added to geometric state equality.


## Shared dispatch contract

Task 11 starts at the base above. For task `n > 11`, freeze a new exact commit containing its accepted prerequisites before dispatch; this report does not invent future hashes. Each task owns only its named new file. All existing Lean files, `Poincare.lean`, other tasks' files, audit wiring and source definitions are forbidden. Dependencies are `11 → 12 → 13 → 14 → 15 → 16`, with `17` using 13–15, `18` using 16–17, and `19` using 11–18 plus S7/S13/S14. A serial 11–19 dispatch is valid.

Each section specifies imports, proof templates, new work, and its stop condition. The common gate below means the exact command printed in that section plus a no-match prohibited-token scan and `git diff --check`. Require exit 0 for Lean and the diff check; require no matches, normally exit 1, for the scan. Independently probe every named target at its displayed signature and inspect its axiom closure. Only the standard logical dependencies are acceptable. Build accepted dependencies serially if their oleans are missing. These are worker gates, not acceptance or merge authority; root build/audits remain the orchestrator's integration checkpoint.

The Lean blocks are the complete proposed definitions and target signatures. A target has no proof body here. The reproducible probe converts each `theorem name : P` into a definition whose body is the proposition `P`; binder-bearing signatures are preserved. `autoImplicit false` prevents a misspelled interface from becoming an invented variable. The broad import envelope is only for the combined scratch probe. Each new implementation file uses the narrower imports listed in its task and the relevant common notation/variables.

```lean
import Poincare.Global.FixedChartMappedGeodesicAssembly
import Poincare.Global.CartanSuppliedReachableChain
import Poincare.Global.CartanTwoNeighborhoodDevelopment
import Poincare.Global.ConnectionInstanceNaturality

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
```


## 17. `Poincare/Global/CartanSuppliedTerminalTransport.lean`

Namespace: `Poincare.CartanSuppliedTerminalTransport`.

Imports: task 15. Task 16 is not needed for these targets.

Objective: prove the short-terminal-path and concatenation laws needed to identify a developing map with a terminal germ. `exists_short_paths` uses local path connectedness of a manifold, as established in S9 by `ChartedSpace.locPathConnectedSpace`, to choose an open path connected neighborhood inside the positive mesh ball. Alternatively, S16 supplies short smooth terminal curves, followed by their distance/diameter estimates. This task does not need any metric regularity of the patch policy.

For `short_path_endpoint`, all path points remain within one mesh of the initial anchor. Supply direct data from the initial fallback patch to each point by H1, and compare the realized chain with those direct successors using task 12 and S2. This is the supplied version of the short-terminal comparisons consumed in S8's restricted-atlas proof. The conclusion compares full states to every actual terminal datum, not merely target values.

For `endpoint_trans`, realize the concatenation with times scaled into its first and second halves, attaching the two actual reached chains at the middle state. Compare it with `C` by task 15. The endpoint anchor equation from task 14 provides `h`; `q.cast h rfl` only changes its endpoint proof and is the existing `Path.cast` in Mathlib's `Topology/Path.lean`. S11's finite reparameterization/refinement geometry and S8's direct-boundary construction are the templates. Supplying the dependent chain at the middle state and proving its samples follow `p.trans q` are new. No path-homotopy invariance is used to establish concatenation.

```lean
namespace CartanSuppliedTerminalTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

theorem exists_short_paths : ∀ (S : System g) (x : M),
  ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
    ∀ z ∈ W, ∃ q : Path x z,
      letI : MetricSpace M := g.toMetricSpace
      ∀ t : unitInterval, dist (q t) x < S.mesh

theorem short_path_endpoint : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (q : Path initial.anchor y) (R : Realization S initial q),
  (letI : MetricSpace M := g.toMetricSpace
   ∀ t : unitInterval, dist (q t) initial.anchor < S.mesh) →
  ∀ d : Data (S.cover.interp (fallback S.cover initial)) initial y,
    R.endpoint = d.successor

theorem endpoint_trans : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {x y : M} (p : Path initial.anchor x) (q : Path x y)
    (R : Realization S initial p) (h : R.endpoint.anchor = x)
    (T : Realization S R.endpoint (q.cast h rfl))
    (C : Realization S initial (p.trans q)), C.endpoint = T.endpoint
end CartanSuppliedTerminalTransport
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedTerminalTransport.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedTerminalTransport.lean
git diff --check
```

Exact stop condition: All three targets compile, especially the every-datum short-path state equality and concatenation with its exact dependent start state. A path-existence lemma alone, a value-only equality without the needed successor comparison, or an assumed concatenation law is partial progress.

