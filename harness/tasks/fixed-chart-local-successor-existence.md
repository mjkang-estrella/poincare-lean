# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/fixed-chart-local-successor-existence`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/fixed-chart-local-successor-existence_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-2.md` (the whole specification: its "Decisions and limits",
"Source and declaration index", and "Shared contract and verification convention" sections apply to you; your
task is reproduced below verbatim), the landed task 6 and 7 modules `Poincare/Global/CartanSuppliedDifferentialSuccessor.lean`
and `Poincare/Global/CartanSuppliedDifferentialTransfer.lean` with their reports
`harness/reports/supplied-differential-successor_done.md` and `harness/reports/supplied-differential-transfer_done.md`.

# Task fixed-chart-local-successor-existence

## Shared contract and verification convention

Task 6 starts at the recorded base. Each later implementation task freezes a new base containing its accepted predecessors. Tasks 6→7→8→9→10 are the requested dependency order; task 10's abstract recursion only needs tasks 6–7, while the later geometric dispatcher will need 8–9. Each task owns exactly the one new file named in its heading. All existing Lean files, `Poincare.lean`, audit wiring, and the other tasks' files are forbidden. This report-only attempt owns only this Markdown file; it does not update `HANDOFF.md`.

The following blocks give complete definitions and full theorem signatures. The signatures intentionally have no proof bodies. For declaration/type checking, each `theorem name : P` is transformed into `def name_spec : Prop := P`; no proof placeholder, axiom, or implementation of a target is introduced. Concatenating the blocks in order is the checked scratch contract. The broad existing import envelope below is for that scratch file. Each task's intended imports are specified separately.

```lean
import Poincare.Global.FixedChartUniformPreferredGermAgreement
import Poincare.Global.DifferentialSuccessorIntervalNaturality
import Poincare.Global.DifferentialSuccessorAdjacentContinuation
import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

```


## 8. `Poincare/Global/FixedChartLocalSuccessorExistence.lean`

Namespace: `Poincare.FixedChartLocalSuccessorExistence`.
Imports: task 7, `Poincare.Global.TangentAlignmentFiberCompactness`, `Poincare.Global.UniformTangentAlignmentRigidity`.

Objective: prove the patchwise replacement of **H1**. The exact replacement is `exists_radius` below, with `OnCompact` fully expanded by its definition. The radius is chosen before `x,p,L,z`; it produces supplied `Data`, proves actual source membership, and retains both new anchors for the next germ. `K,H` are arbitrary compact subsets of the open retained source/target anchor sets, not just single centers. Positive radius for the singleton centers is consequently a substantive special case.

S3 supplies the joint normal domain and evaluator on each patch, and retains the original compact `K,R,ρ` endpoint clause with separate image and injectivity radii. S4 supplies fixed-anchor germ identification. S7/S10 supply old fixed-anchor data-existence theorems; S12 supplies compact alignment fibers and fixed-anchor operator bounds. These are reusable ingredients, not a proof of this statement. In particular, uniform bounds for framed alignments as `x,p` move over `K,H`, and uniform strict differential/metric-pullback witnesses on the retained domains, must be established in this task. One cannot take a minimum of separately chosen per-anchor radii. S10's `LocalUniformNormalGenericSuccessorDataOn` still concludes old `Data` and is not this H1.

This is deliberately an open mathematical task. The C¹ and germ statements in S3/S4 alone do not prove all the `CoordinateData` fields uniformly. If that is the resisting interface, stop with the exact field and quantified type rather than turning it into an extra premise of `exists_radius`.

```lean
namespace FixedChartLocalSuccessorExistence
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3) (η : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
    z ∈ Q.sourceAnchors ∧ map Q ⟨x, p, L⟩ z ∈ Q.targetAnchors ∧
    z ∈ (germ Q ⟨x, p, L⟩).source ∧ Nonempty (Data Q ⟨x, p, L⟩ z)
-- TARGET 8.1
theorem exists_radius :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    ∃ η > (0 : ℝ), OnCompact (patch C D) K H η
end FixedChartLocalSuccessorExistence
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorExistence.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartLocalSuccessorExistence.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: Prove `exists_radius` exactly for every compact `K,H` satisfying the displayed inclusions, including actual source membership and `Data` production. Otherwise report the exact uniform field/estimate that resists proof and any compiler-verified weaker result. Per-anchor existence, a conditional radius, or old generic `Data` is not success.

