# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-restricted-development`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-restricted-development_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-restricted-development
Landed prerequisites on main: tasks 11-17 (`CartanSuppliedFinitePatchCover.lean`, `CartanSuppliedUniformPatchSwitch.lean` + `CartanSuppliedBufferedPairAgreement.lean`, `CartanSuppliedPatchPolicy.lean` (`policy`, `fallback`, `Sticky`, `stepAvailable`, `exists_sticky_chain`, `chains_eq`), `CartanSuppliedWholeCellRealization.lean` (`Subdivision`, `Realization`, `RootedRealization`, `endpoint_anchor`, `exists_subdivision`, `exists_realization`, `exists_rootedRealization_with_wholeCellMesh`), `CartanSuppliedSubdivisionTransport.lean` (`block_state_eq`, `refinement_chain_state_eq`, `refinement_state_eq`, `state_eq_of_constant_nodes`, `endpoint_eq_same_path`), `CartanSuppliedHomotopyEndpoints.lean` (`GridSmall`, `exists_grid`, `ladder_state_eq`, `grid_endpoint_eq`, `endpoint_eq_of_homotopy`, `endpoint_eq` under `SimplyConnectedSpace M`), `CartanSuppliedTerminalTransport.lean` (`exists_short_paths`, `short_path_endpoint`, `exists_trans_subdivision`, `segment_state_eq`, `endpoint_trans`)). Import and use them; do not re-prove landed theorems.

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


## 18. `Poincare/Global/CartanSuppliedRestrictedDevelopment.lean`

Namespace: `Poincare.CartanSuppliedRestrictedDevelopment`.

Imports: tasks 16 and 17, `Poincare.Global.CartanRestrictedOverlapCompatibility`.

Objective: form the total map from rooted endpoints and prove it is locally the selected terminal supplied germ. This uses the direct supplied-germ option in the task, with a new restricted atlas containing arbitrary open partial homeomorphisms.

`development R x` is the target of the reached terminal state. `terminalGerm` uses the covering fallback at that state; task 14 places its anchor at `x`, and S1.`anchor_laws` identifies its value at `x` with that target. The terminal label need not be the last predecessor's label. Task 12 supplies the relevant switch agreement.

To prove `development_eqOn_terminal_neighborhood`, choose the short-path neighborhood from task 17 and intersect it with the terminal germ source. For `z` in this neighborhood, realize the short path from `x` to `z` starting at the terminal state at `x`. H1 supplies direct terminal data, and task 17 identifies its target with `terminalGerm R x z`. Concatenation identifies the endpoint of the rooted path to `x` followed by this short path. Task 16 compares that concatenated realization to the rooted realization chosen at `z`. This is the new supplied replacement for S8.`restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry`; no equality on maximal packaged sources is requested.

Choose each `domain x` from this neighborhood theorem. On `domain x ∩ domain y`, both germs equal `development`, giving `compatible`. Reuse S12's `diagonalDevelopment_eqOn_domain` and `isLocalHomeomorph_diagonalDevelopment` proof text with the supplied `germ` field: restrict `A.germ x` to `A.domain x`, show `x` belongs, and prove agreement with the diagonal. These existing theorems cannot be applied directly to the new structure, since S12's old `germ` definition is hardwired to `CartanMap.openPartialHomeomorph`. The target is an actual total local homeomorphism, not an atlas whose compatibility remains a hypothesis.

```lean
namespace CartanSuppliedRestrictedDevelopment
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

structure RestrictedAtlas (M : Type u) [TopologicalSpace M] where
  germ : M → OpenPartialHomeomorph M RoundSphere3
  domain : M → Set M
  isOpen_domain : ∀ x, IsOpen (domain x)
  anchor_mem_domain : ∀ x, x ∈ domain x
  domain_subset_source : ∀ x, domain x ⊆ (germ x).source
  compatible : ∀ x y, EqOn (germ x) (germ y) (domain x ∩ domain y)

def RestrictedAtlas.diagonal (A : RestrictedAtlas M) : M → RoundSphere3 :=
  fun x => A.germ x x

def terminalState {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) (x : M) : CartanChain.ChainState g :=
  (R.realization x).endpoint

def terminalGerm {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) (x : M) : OpenPartialHomeomorph M RoundSphere3 :=
  germ (S.cover.interp (fallback S.cover (terminalState R x))) (terminalState R x)

def development {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) : M → RoundSphere3 :=
  fun x => (terminalState R x).target

theorem development_eqOn_terminal_neighborhood [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk) (x : M),
  ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ (terminalGerm R x).source ∧
    EqOn (development R) (terminalGerm R x) W

theorem exists_restrictedAtlas [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk),
  ∃ A : RestrictedAtlas M, A.germ = terminalGerm R ∧ A.diagonal = development R

theorem isLocalHomeomorph_diagonal : ∀ A : RestrictedAtlas M,
  IsLocalHomeomorph A.diagonal

theorem isLocalHomeomorph_development [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk), IsLocalHomeomorph (development R)
end CartanSuppliedRestrictedDevelopment
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedRestrictedDevelopment.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedRestrictedDevelopment.lean
git diff --check
```

Exact stop condition: All four targets compile, including source inclusion and equality with the total rooted-endpoint map on open neighborhoods. A compatible atlas constructor taking compatibility as a new geometric premise, or only a generic-source adapter without verified domain shrinking, is failure.

