# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-whole-cell-realization`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-whole-cell-realization_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-whole-cell-realization
Landed prerequisites on main: tasks 11-13 (`CartanSuppliedFinitePatchCover.lean`, `CartanSuppliedUniformPatchSwitch.lean` + `CartanSuppliedBufferedPairAgreement.lean` (`exists_switchControl` unconditional), `CartanSuppliedPatchPolicy.lean` (`policy`, `Sticky`, `stepAvailable`, `exists_sticky_chain`, `chains_eq`)). Import and use them; do not re-prove landed theorems.

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


## 14. `Poincare/Global/CartanSuppliedWholeCellRealization.lean`

Namespace: `Poincare.CartanSuppliedWholeCellRealization`.

Imports: task 13, `Poincare.Global.CartanAtlasRootedPathSkeleton`, `Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition`.

Objective: choose strict eventually terminal whole-cell subdivisions, then realize supplied chains on them, for every path and for the common rooted skeleton. The whole-cell clause bounds all pairs of points in each parameter cell, not just its endpoint nodes. `Realization` stores the actual schedule and reached-chain data; it allows non-sticky policies so later comparisons cover every valid choice. The existence target additionally returns the sticky property.

Reuse the geometric part of S8.`exists_genericRootedRealization_with_wholeCellMesh_of_certificate`: subordinate to pointwise path balls of half the requested radius, remove duplicate times using the S11 finite-sorted-sequence lemmas, and retain `Monotone`, strictness, and terminal tail. Apply task 13 only after the subdivision is fixed. Reuse S9's `RootedCartanPathSkeleton` without conversion to the old `RootedPathChainRealization`. The new part is the supplied policy/chain fields and the terminal anchor proof from S5.`state_anchor_eq_node`. The infinite tail is legitimate: all tail steps have zero distance and S2.`patch_successor_at_anchor` makes their states constant.

```lean
namespace CartanSuppliedWholeCellRealization
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
structure Subdivision {x y : M} (p : Path x y) (r : ℝ) where
  time : ℕ → unitInterval
  terminal : ℕ
  zero : time 0 = 0
  mono : Monotone time
  strict : ∀ n < terminal, time n < time (n + 1)
  tail : ∀ n ≥ terminal, time n = 1
  wholeCell : letI : MetricSpace M := g.toMetricSpace
    ∀ n (a b : unitInterval), a ∈ Icc (time n) (time (n + 1)) →
      b ∈ Icc (time n) (time (n + 1)) → dist (p a) (p b) < r

structure Realization (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) where
  subdivision : Subdivision (g := g) p S.mesh
  preferred : ℕ → S.cover.Label
  chain : ReachableChain (policy S.cover preferred)
    (fun n => p (subdivision.time n)) initial

def Realization.endpoint {S : System g} {initial : CartanChain.ChainState g}
    {y : M} {p : Path initial.anchor y} (R : Realization S initial p) :
    CartanChain.ChainState g := R.chain.state R.subdivision.terminal

structure RootedRealization (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g) where
  realization : ∀ x : M, Realization S skeleton.root (skeleton.path x)

theorem endpoint_anchor : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R : Realization S initial p),
  R.endpoint.anchor = y

theorem exists_subdivision : ∀ {x y : M} (p : Path x y) (r : ℝ),
  0 < r → Nonempty (Subdivision (g := g) p r)

theorem exists_realization : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y),
  ∃ R : Realization S initial p,
    Sticky S.cover R.preferred (fun n => p (R.subdivision.time n)) initial R.chain

theorem exists_rootedRealization_with_wholeCellMesh : ∀ (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g),
  Nonempty (RootedRealization S skeleton)
end CartanSuppliedWholeCellRealization
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedWholeCellRealization.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedWholeCellRealization.lean
git diff --check
```

Exact stop condition: All four targets compile. Require positive-mesh whole-cell control, strictness before the terminal index, constant terminal times, actual supplied `Data`, and the endpoint anchor equation. Existence along only the chosen skeleton without the arbitrary-path target, or a mesh selected after seeing chain data, is failure.

