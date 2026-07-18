import Poincare.Global.HausdorffFrozenInverseChartAreaFormula
import Mathlib.Analysis.Matrix.Normed

/-!
# Regularity and frozen comparison for the inverse-chart Gram field

The exact frozen formula in
`HausdorffFrozenInverseChartAreaFormula` uses the single matrix
`inverseChartPullbackGramMatrix g x₀ z₀`.  This file proves that the actual
spatially varying Gram matrix is the restriction of a smooth matrix field on
the ambient Euclidean chart model.  Consequently both the restricted Gram
matrix and its `sqrt |det|` density are continuous.

Continuity gives two genuinely local comparisons with the frozen value:
all matrix entries are simultaneously close, and the positive volume density
lies between prescribed relative multiples of its value at the base point.
These statements compare the variable metric with its frozen tangent model;
they do not assert the still-missing variable path-metric Hausdorff area
formula.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Set Filter Metric Matrix
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  Matrix.Norms.Elementwise

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The ambient-coordinate matrix field whose restriction to the extended
chart target is the actual inverse-chart pullback Gram matrix. -/
noncomputable def inverseChartPullbackGramMatrixField
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (z : E) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    CovariantDerivative.chartMetric g.inner x₀ z
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- On the genuine extended-chart target, the ambient chart-metric matrix is
exactly the inverse-chart pullback Gram matrix defined from the transported
Euclidean tangent basis. -/
theorem inverseChartPullbackGramMatrix_eq_field
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) :
    inverseChartPullbackGramMatrix g x₀ z =
      inverseChartPullbackGramMatrixField g x₀ z := by
  ext i j
  change
    g.inner ((extChartAt I x₀).symm (z : E))
        ((ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
          (n := n) (M := M) x₀ z.2) i)
        ((ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
          (n := n) (M := M) x₀ z.2) j) =
      CovariantDerivative.chartMetric g.inner x₀ (z : E)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)
  rw [ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply,
    ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
  rfl

/-- Every scalar entry of the ambient inverse-chart Gram field is smooth on
the extended-chart target. -/
theorem contDiffOn_inverseChartPullbackGramMatrixField_entry
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (i j : Fin n) :
    ContDiffOn ℝ ∞
      (fun z ↦ inverseChartPullbackGramMatrixField g x₀ z i j)
      (extChartAt I x₀).target := by
  exact
    (CovariantDerivative.contMDiffOn_chartMetric_pairing
      g.inner x₀ (m := ∞) (by simp)
      g.contMDiff_inner
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)).contDiffOn

/-- The whole ambient inverse-chart Gram matrix is smooth on the
extended-chart target, not merely continuous entry by entry. -/
theorem contDiffOn_inverseChartPullbackGramMatrixField
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ContDiffOn ℝ ∞ (inverseChartPullbackGramMatrixField g x₀)
      (extChartAt I x₀).target := by
  change ContDiffOn ℝ ∞
    (fun z i ↦ inverseChartPullbackGramMatrixField g x₀ z i)
    (extChartAt I x₀).target
  rw [contDiffOn_pi]
  intro i
  rw [← (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin n ↦ ℝ)).symm.comp_contDiffOn_iff]
  apply (contDiffOn_piLp 2).2
  intro j
  exact contDiffOn_inverseChartPullbackGramMatrixField_entry g x₀ i j

/-- The actual inverse-chart pullback Gram matrix is continuous as a function
on the subtype of genuine chart coordinates. -/
theorem continuous_inverseChartPullbackGramMatrix
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    Continuous
      (fun z : (extChartAt I x₀).target ↦
        inverseChartPullbackGramMatrix g x₀ z) := by
  have hfield :
      Continuous
        (fun z : (extChartAt I x₀).target ↦
          inverseChartPullbackGramMatrixField g x₀ z) :=
    continuous_pi fun i ↦
      continuous_pi fun j ↦
        (contDiffOn_inverseChartPullbackGramMatrixField_entry g x₀ i j).continuousOn.restrict
  exact hfield.congr fun z ↦
    (inverseChartPullbackGramMatrix_eq_field g x₀ z).symm

/-- The actual inverse-chart `sqrt |det|` volume density is continuous on the
genuine extended-chart target. -/
theorem continuous_inverseChartPullbackVolumeDensity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    Continuous
      (fun z : (extChartAt I x₀).target ↦
        inverseChartPullbackVolumeDensity g x₀ z) := by
  simpa only [inverseChartPullbackVolumeDensity] using
    VolumeDensity.continuous_chartVolumeDensity
      (continuous_inverseChartPullbackGramMatrix g x₀)

/-- The inverse-chart volume density is strictly positive at every genuine
chart coordinate. -/
theorem inverseChartPullbackVolumeDensity_pos
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) :
    0 < inverseChartPullbackVolumeDensity g x₀ z := by
  exact VolumeDensity.chartVolumeDensity_pos_of_posDef
    (inverseChartPullbackGramMatrix_posDef g x₀ z)

/-- Near `z₀`, every entry of the variable Gram matrix is simultaneously
within `ε` of the corresponding entry of its frozen value.  Finiteness of
the coordinate frame is what turns the entrywise continuity statements into
one common neighborhood. -/
theorem inverseChartPullbackGramMatrix_eventually_entrywise_close
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) { ε : ℝ } (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀, ∀ i j : Fin n,
      |inverseChartPullbackGramMatrix g x₀ z i j -
        inverseChartPullbackGramMatrix g x₀ z₀ i j| < ε := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  have hij :
      Continuous
        (fun z : (extChartAt I x₀).target ↦
          inverseChartPullbackGramMatrix g x₀ z i j) :=
    (continuous_apply_apply i j).comp
      (continuous_inverseChartPullbackGramMatrix g x₀)
  have hcont : Tendsto
      (fun z : (extChartAt I x₀).target ↦
        inverseChartPullbackGramMatrix g x₀ z i j)
      (nhds z₀)
      (nhds (inverseChartPullbackGramMatrix g x₀ z₀ i j)) :=
    hij.continuousAt
  have hclose := (Metric.tendsto_nhds.mp hcont) ε hε
  simpa only [Real.dist_eq] using hclose

/-- The variable inverse-chart density is additively close to the frozen
density on a neighborhood of the freezing point. -/
theorem inverseChartPullbackVolumeDensity_eventually_close
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) { ε : ℝ } (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀,
      |inverseChartPullbackVolumeDensity g x₀ z -
        inverseChartPullbackVolumeDensity g x₀ z₀| < ε := by
  have hcont : Tendsto
      (fun z : (extChartAt I x₀).target ↦
        inverseChartPullbackVolumeDensity g x₀ z)
      (nhds z₀)
      (nhds (inverseChartPullbackVolumeDensity g x₀ z₀)) :=
    (continuous_inverseChartPullbackVolumeDensity g x₀).continuousAt
  have hclose := (Metric.tendsto_nhds.mp hcont) ε hε
  simpa only [Real.dist_eq] using hclose

/-- A quantitative frozen-density comparison: for every positive relative
tolerance, the variable density lies between the corresponding lower and
upper multiples of its frozen value on one neighborhood of `z₀`.

When `ε < 1`, the lower comparison factor is itself positive. -/
theorem inverseChartPullbackVolumeDensity_eventually_relative_bounds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) { ε : ℝ } (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀,
      (1 - ε) * inverseChartPullbackVolumeDensity g x₀ z₀ <
          inverseChartPullbackVolumeDensity g x₀ z ∧
        inverseChartPullbackVolumeDensity g x₀ z <
          (1 + ε) * inverseChartPullbackVolumeDensity g x₀ z₀ := by
  have hδ0 : 0 < inverseChartPullbackVolumeDensity g x₀ z₀ :=
    inverseChartPullbackVolumeDensity_pos g x₀ z₀
  have hclose :=
    inverseChartPullbackVolumeDensity_eventually_close g x₀ z₀
      (mul_pos hε hδ0)
  filter_upwards [hclose] with z hz
  rcases abs_lt.mp hz with ⟨hlower, hupper⟩
  constructor <;> nlinarith

end Poincare
