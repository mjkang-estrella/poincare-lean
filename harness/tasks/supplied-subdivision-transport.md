# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-subdivision-transport`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-subdivision-transport_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-subdivision-transport
Landed prerequisites on main: tasks 11-14 (`CartanSuppliedFinitePatchCover.lean`, `CartanSuppliedUniformPatchSwitch.lean` + `CartanSuppliedBufferedPairAgreement.lean` (`exists_switchControl` unconditional), `CartanSuppliedPatchPolicy.lean` (`policy`, `Sticky`, `stepAvailable`, `exists_sticky_chain`, `chains_eq`), `CartanSuppliedWholeCellRealization.lean` (`Subdivision`, `Realization`, `RootedRealization`, `endpoint_anchor`, `exists_subdivision`, `exists_realization`, `exists_rootedRealization_with_wholeCellMesh`)). Import and use them; do not re-prove landed theorems.

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


## 15. `Poincare/Global/CartanSuppliedSubdivisionTransport.lean`

Namespace: `Poincare.CartanSuppliedSubdivisionTransport`.

Imports: task 14. S11's refinement declarations are available through that import.

Objective: show that inserting sample times inside whole cells, changing finite subdivisions, and changing patch schedules do not change endpoint states on a fixed path.

S11 provides common finite refinements and monotone factor maps. Reuse those parameter results directly. The new proof is the transport of supplied states across each refinement block: compare the original one-step map with the several inserted steps. All points of that block lie in the original whole cell. H1 can supply direct data from its initial state to each intermediate point. Task 12's transition equality and task 13's policy comparison give open agreement near the next inserted node; S2 then identifies the actual differentials/successors. The factor 4 allowance handles the two relevant point distances. This is the insertion/ladder argument behind S10.`reachableChains_ladder_invariant`, adapted to an arbitrary block length. It requires actual open agreement, not value-only endpoint matching.

`refinement_state_eq` explicitly permits repeated factor values and terminal tails; use S2's zero-step law there. `endpoint_eq_same_path` obtains a common refinement from S11 and compares both original realizations to its realized chain. This task uses no simple connectivity.

```lean
namespace CartanSuppliedSubdivisionTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

theorem refinement_state_eq : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R T : Realization S initial p)
    (f : ℕ → ℕ), f 0 = 0 → Monotone f →
  (∀ n, R.subdivision.time n = T.subdivision.time (f n)) →
  ∀ n, R.chain.state n = T.chain.state (f n)

theorem endpoint_eq_same_path : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R T : Realization S initial p),
  R.endpoint = T.endpoint
end CartanSuppliedSubdivisionTransport
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSubdivisionTransport.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedSubdivisionTransport.lean
git diff --check
```

Exact stop condition: Both targets compile for all displayed realizations and monotone factor maps. Equality for just one chosen subdivision, equality of targets without alignments, or a new global path-independence premise is failure. Stop at the exact block-induction/open-agreement type if it resists.

