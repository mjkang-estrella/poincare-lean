# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/fixed-chart-local-successor-equality`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/fixed-chart-local-successor-equality_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-2.md` (the whole specification; your task is reproduced below
verbatim), the landed modules `CartanSuppliedDifferentialSuccessor.lean`, `CartanSuppliedDifferentialTransfer.lean`,
`FixedChartLocalSuccessorExistence.lean`, and `harness/reports/fixed-chart-local-successor-existence_blocked.md`.
IMPORTANT ORCHESTRATOR NOTE: task 8 stopped short; its frozen `exists_radius` is NOT on `main`. What exists is
`FixedChartLocalSuccessorExistence.exists_uniform_domain_radius` (the domain conjuncts with one uniform radius)
and `exists_onCompact_of_uniformDifferentialPullback` (the H1 `OnCompact` conditional on the exact remainder
`UniformDifferentialPullback`, which another worker is attacking). Therefore: prove YOUR equality `OnCompact`
unconditionally with radii chosen before all moving parameters (that is the substance of task 9), and state the
bundled frozen target `exists_radii` as `exists_radii_of_uniformDifferentialPullback`, taking
`UniformDifferentialPullback (patch C D) K H` as its only extra hypothesis and using the existing reduction for
the H1 conjunct. Do not assume any other unproved statement.

# Task fixed-chart-local-successor-equality

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


## 9. `Poincare/Global/FixedChartLocalSuccessorEquality.lean`

Namespace: `Poincare.FixedChartLocalSuccessorEquality`.
Imports: task 8, `Poincare.Global.DifferentialSuccessorAdjacentContinuation`.

Objective: prove the patchwise replacement of **H2**, namely `exists_radii` with the displayed `OnCompact`. It retains H1 at the same predecessor-step radius `η` and supplies an independent evaluation radius `ε`. Both are chosen before all moving anchors, alignments, and actual data. Equality is quantified over every witness, not a chosen datum.

The conclusion includes `ball z ε ⊆ old.source ∩ new.source`. Consequently it implies source-intersected equality and supports a later full-ball consumer using a radius at most `min η ε`. Source-intersected equality without this inclusion would not replace S11.`UniformSuccessorEqOnBall`. Taking a minimum here means two already uniform positive numbers, never radii extracted from an unrealized chain.

Use task 8 for existence and task 7 for witness independence and any available local comparison. S7's interval theorem supplies a generic fixed-anchor germ equality only. S8's continuation theorem `exists_metricBall_eqOn_coordinateControlled_of_pathIndependence` has an explicit cross-history/path-independence hypothesis and chooses a ball after the anchors/data; neither that hypothesis nor the quantifier order can be silently removed. A new uniform reanchoring/ODE equality argument on the retained patches is required. S3's joint openness can support the domain part once the framed target maps are controlled; it does not prove the equality part. Do not bootstrap this H2 from a future global chain-independence theorem that itself consumes H2.

```lean
namespace FixedChartLocalSuccessorEquality
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3)
    (η ε : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
    (d : Data Q ⟨x, p, L⟩ z), dist z x < η →
      Metric.ball z ε ⊆ (germ Q ⟨x, p, L⟩).source ∩ (germ Q d.successor).source ∧
      EqOn (map Q ⟨x, p, L⟩) (map Q d.successor) (Metric.ball z ε)
-- TARGET 9.1
theorem exists_radii :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    ∃ η > (0 : ℝ), ∃ ε > (0 : ℝ),
      FixedChartLocalSuccessorExistence.OnCompact (patch C D) K H η ∧
      OnCompact (patch C D) K H η ε
end FixedChartLocalSuccessorEquality
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorEquality.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartLocalSuccessorEquality.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: Prove `exists_radii` exactly, including H1 at `η`, the common-source full-ball inclusion, and equality for every datum on the same `ε` ball. Otherwise record the exact equality or domain goal and missing uniform estimate. An anchor-dependent evaluation neighborhood, component-only equality, or a new path-independence premise is not success.

