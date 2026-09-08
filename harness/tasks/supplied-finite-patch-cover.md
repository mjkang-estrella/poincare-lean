# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-finite-patch-cover`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-finite-patch-cover_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-finite-patch-cover

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


## 11. `Poincare/Global/CartanSuppliedFinitePatchCover.lean`

Namespace: `Poincare.CartanSuppliedFinitePatchCover`.

Imports: `Poincare.Global.FixedChartMappedGeodesicAssembly`, `Poincare.Global.ControlledChartInstance`.

Objective: produce finite nested source and sphere covers and three uniform positive radii before any path, alignment or chain is chosen. `exists_patchCover` is intentionally stronger than a controlled-instance-only statement: its ingredients in S6 require no atlas finiteness assumption. The final adapter still uses the controlled reduction requested in S7.

For each point choose `zone := cutoffOneLocus center`, using S6, and a patch. Choose smaller metric balls whose nested closures lie in the open anchor set; compactness of the metric space makes the closed cores compact. Take a finite subcover of the innermost open sets. Then apply `lebesgue_number_lemma_of_metric` to those sets, exactly as S7.`exists_finite_uniform_chart_cover` does for chart sources. `covers` is the consequence at ball centers, retained to define `pick` without another proof-producing choice. Repeat for `roundSphereMetric3`; there is no new sphere chart instance.

Apply S4.`exists_radii` to every pair of buffers. Take finite minima of these already uniform pair radii. Apply S4.`exists_uniform_domain_radius_into_open` to each pair of operating cores, with the interiors of the buffers as the requested neighborhoods, and take a finite minimum for `retention`. The new work is the nested finite cover and these quantifier-preserving minima. The controlled-chart cover proof is the topological template; S3/S4 supply the geometric estimates. A minimum of per-state generic chosen radii is not part of this task.

```lean
namespace CartanSuppliedFinitePatchCover
structure PatchCover (g : ClosedSmoothRiemannianMetric 3 M) where
  count : ℕ
  center : Fin count → M
  zone : Fin count → Set E
  patch : ∀ i, FixedChartUniformSourceNormal.Patch g (center i) (zone i)
  cutoff : ∀ i, zone i ⊆ IsometryInstantiate.cutoffOneLocus (center i)
  core : Fin count → Set M
  buffer : Fin count → Set M
  openCore : Fin count → Set M
  core_compact : ∀ i, IsCompact (core i)
  buffer_compact : ∀ i, IsCompact (buffer i)
  openCore_open : ∀ i, IsOpen (openCore i)
  openCore_subset : ∀ i, openCore i ⊆ core i
  core_subset : ∀ i, core i ⊆ interior (buffer i)
  buffer_subset : ∀ i, buffer i ⊆ (patch i).anchors
  lebesgue : ℝ
  lebesgue_pos : 0 < lebesgue
  ball_cover : letI : MetricSpace M := g.toMetricSpace
    ∀ x : M, ∃ i, ball x lebesgue ⊆ openCore i
  covers : ∀ x : M, ∃ i, x ∈ core i

def PatchCover.pick (C : PatchCover g) (x : M) : Fin C.count :=
  Classical.choose (C.covers x)

def Controlled (charts : ChartedSpace E M) (d : MetricSpace M) : Prop :=
  charts.atlas.Finite ∧ letI : MetricSpace M := d
    ∃ δ > (0 : ℝ), ∀ x : M, ball x δ ⊆ (charts.chartAt x).source

structure QuantitativeCover (g : ClosedSmoothRiemannianMetric 3 M) where
  source : PatchCover g
  target : PatchCover roundSphereMetric3
  step : ℝ
  evaluation : ℝ
  retention : ℝ
  step_pos : 0 < step
  evaluation_pos : 0 < evaluation
  retention_pos : 0 < retention
  h1 : ∀ i j, FixedChartLocalSuccessorExistence.OnCompact
    (patch (source.patch i) (target.patch j)) (source.buffer i) (target.buffer j) step
  h2 : ∀ i j, FixedChartLocalSuccessorEquality.OnCompact
    (patch (source.patch i) (target.patch j)) (source.buffer i) (target.buffer j)
    step evaluation
  retained : letI : MetricSpace M := g.toMetricSpace
    ∀ i j (s : CartanChain.ChainState g),
      s.anchor ∈ source.core i → s.target ∈ target.core j →
      ∀ z : M, dist z s.anchor < retention →
        z ∈ interior (source.buffer i) ∧
        map (patch (source.patch i) (target.patch j)) s z ∈ interior (target.buffer j)

def QuantitativeCover.Label (B : QuantitativeCover g) :=
  Fin B.source.count × Fin B.target.count

def QuantitativeCover.interp (B : QuantitativeCover g) (a : B.Label) : Interpretation g :=
  patch (B.source.patch a.1) (B.target.patch a.2)

def QuantitativeCover.Valid (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g) : Prop :=
  s.anchor ∈ B.source.core a.1 ∧ s.target ∈ B.target.core a.2

def QuantitativeCover.Buffered (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g) : Prop :=
  s.anchor ∈ B.source.buffer a.1 ∧ s.target ∈ B.target.buffer a.2

theorem exists_patchCover : ∀ g : ClosedSmoothRiemannianMetric 3 M,
  Nonempty (PatchCover g)

theorem exists_quantitativeCover : HasConstantSectionalCurvature3 g 1 →
  Nonempty (QuantitativeCover g)
end CartanSuppliedFinitePatchCover
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedFinitePatchCover.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedFinitePatchCover.lean
git diff --check
```

Exact stop condition: Both existence targets must compile, including `ball_cover`, the finite sphere cover, H1/H2 over buffers, and retention of both successor anchors in buffer interiors. A collection whose cores do not cover, or whose radius depends on the current alignment/chain, is failure. If finite refinement is disallowed, report the exact unsupported one-patch coverage type.

