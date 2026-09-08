# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-homotopy-endpoints`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-homotopy-endpoints_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-homotopy-endpoints
Landed prerequisites on main: tasks 11-15 (`CartanSuppliedFinitePatchCover.lean`, `CartanSuppliedUniformPatchSwitch.lean` + `CartanSuppliedBufferedPairAgreement.lean` (`exists_switchControl` unconditional), `CartanSuppliedPatchPolicy.lean` (`policy`, `Sticky`, `stepAvailable`, `exists_sticky_chain`, `chains_eq`), `CartanSuppliedWholeCellRealization.lean` (`Subdivision`, `Realization`, `RootedRealization`, `endpoint_anchor`, `exists_subdivision`, `exists_realization`, `exists_rootedRealization_with_wholeCellMesh`), `CartanSuppliedSubdivisionTransport.lean` (`block_state_eq`, `refinement_chain_state_eq` for arbitrary monotone sampled chains, `refinement_state_eq`, `state_eq_of_constant_nodes`, `endpoint_eq_same_path`)). Import and use them; do not re-prove landed theorems.

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


## 16. `Poincare/Global/CartanSuppliedHomotopyEndpoints.lean`

Namespace: `Poincare.CartanSuppliedHomotopyEndpoints`.

Imports: task 15, `Poincare.Global.DifferentialSuccessorAdjacentContinuation`.

Objective: port the metric-ball homotopy ladder to supplied chains and then compare arbitrary path realizations. `GridSmall` gives pairwise diameter control on every closed rectangle, including boundary and eventual constant cells.

Use S10.`exists_homotopy_metricBall_grid` with balls of radius `S.mesh / 2`, covering the image by balls centered at its points; triangle inequality gives `GridSmall`. For the supplied ladder, construct each rung by task 13 H1 with a policy evaluated at the actual lower-row successor state. S4 H2 supplies the bottom and rung evaluation balls. At each re-anchoring, task 12 transfers from the old patch at the successor to the selected patch there. A diagonal pair of successive top cells may require two mesh bounds, which fit inside `4 * S.mesh`. Intersect the open balls around the opposite vertex to compare the actual upper edge and the rung using S2.

The finite ladder proof is S10.`reachableChains_endpoint_eq` and `differentialHomotopyGrid_chain_endpoint_eq_of_metricBall_patches`, replacing legacy data and zero-vector steps with supplied data and S2.`patch_successor_at_anchor`. It must track the interpretations separately. S5.`state_eq_of_open_agreement` compares a rebuilt row policy on the same row nodes after those neighborhoods have been proved; it cannot itself compare different rows or different paths.

To get `endpoint_eq_of_homotopy`, include the finitely many boundary sample times of both input realizations in a common grid refinement, or strictly sort the grid boundary and use task 15 on a common refinement. S11's product-cover refinement theorem is the template. Establish boundary transport and terminal-tail constancy, rather than asserting that the new grid has the old samples. Only `endpoint_eq` uses `SimplyConnectedSpace M`, through S17.`SimplyConnectedSpace.paths_homotopic`. Its `Path.Homotopic` witness is `Nonempty` of the relative-endpoint `Path.Homotopy` type.

```lean
namespace CartanSuppliedHomotopyEndpoints
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

def GridSmall (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q) (t : ℕ → unitInterval) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m n (a b c d : unitInterval),
    a ∈ Icc (t m) (t (m + 1)) → b ∈ Icc (t m) (t (m + 1)) →
    c ∈ Icc (t n) (t (n + 1)) → d ∈ Icc (t n) (t (n + 1)) →
    dist (H (a, c)) (H (b, d)) < S.mesh

theorem exists_grid : ∀ (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q),
  ∃ (t : ℕ → unitInterval) (k : ℕ), t 0 = 0 ∧ Monotone t ∧
    (∀ n ≥ k, t n = 1) ∧ GridSmall S H t

theorem grid_endpoint_eq : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} {p q : Path initial.anchor y} (H : p.Homotopy q)
    (t : ℕ → unitInterval) (k : ℕ),
  t 0 = 0 → Monotone t → (∀ n ≥ k, t n = 1) → GridSmall S H t →
  ∀ (a : ℕ → ℕ → S.cover.Label)
    (c : ∀ m, ReachableChain (policy S.cover (a m))
      (fun n => H (t m, t n)) initial),
    (c 0).state k = (c k).state k

theorem endpoint_eq_of_homotopy : ∀ (S : System g)
    (initial : CartanChain.ChainState g) {y : M}
    {p q : Path initial.anchor y}, p.Homotopy q →
  ∀ (R : Realization S initial p) (T : Realization S initial q),
    R.endpoint = T.endpoint

theorem endpoint_eq [SimplyConnectedSpace M] : ∀ (S : System g)
    (initial : CartanChain.ChainState g) {y : M}
    (p q : Path initial.anchor y)
    (R : Realization S initial p) (T : Realization S initial q),
    R.endpoint = T.endpoint
end CartanSuppliedHomotopyEndpoints
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedHomotopyEndpoints.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedHomotopyEndpoints.lean
git diff --check
```

Exact stop condition: All four targets compile, including full state equality for arbitrary boundary subdivisions/policies. A grid theorem still asking for unproduced equality balls or a same-node comparison alone is only partial. Do not introduce source simple connectivity before it is used to obtain the path homotopy; do not substitute sphere simple connectivity for it.

