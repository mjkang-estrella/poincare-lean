import Poincare.Global.HausdorffPullbackAreaFormulaReduction
import Poincare.Global.HausdorffLinearPullbackAreaFormula

/-!
# Frozen inverse-chart Hausdorff area formula

The exact fixed-constant-Gram area formula applies to the Gram matrix of a
Riemannian inverse chart after freezing that matrix at one coordinate point.
This file proves the required pointwise positive definiteness and records the
resulting exact frozen-tangent formula.

The distinction from `InverseChartPullbackHausdorffAreaFormula` is essential.
That proposition concerns the actual inverse-chart parametrization and the
spatially varying matrix `z ↦ inverseChartPullbackGramMatrix g x₀ z`.  The
formula proved here fixes one `z₀`, represents the single matrix `G(z₀)` by a
linear equivalence, and installs the corresponding constant pullback metric
on the whole coordinate target.  Thus this is a proved constant-coefficient
local model, not the still-missing variable-metric area formula.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Set Metric Matrix
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n d : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

namespace ClosedSmoothRiemannianMetric

/-- The matrix of a Riemannian metric in any genuine finite tangent basis is
positive definite.

For a nonzero coordinate vector `a`, the basis equivalence reconstructs a
nonzero tangent vector.  The matrix quadratic form is the metric evaluated
on that vector, hence is strictly positive. -/
theorem metricMatrixInBasisAt_posDef
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) :
    (metricMatrixInBasisAt g x b).PosDef := by
  have hmatrix :
      metricMatrixInBasisAt g x b =
        LinearMap.toMatrix₂ b b (g.metricBilinAt x) := by
    ext i j
    simp [metricMatrixInBasisAt, LinearMap.toMatrix₂_apply,
      g.metricBilinAt_apply]
  rw [hmatrix]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [LinearMap.toMatrix₂_apply, star_trivial,
      g.metricBilinAt_apply]
    exact g.inner_symm x (b j) (b i)
  · intro a ha
    have hva : b.equivFun.symm a ≠ 0 :=
      b.equivFun.symm.map_ne_zero_iff.mpr ha
    have hquadratic :=
      dotProduct_toMatrix₂_mulVec
        b b (g.metricBilinAt x) a a
    have heq :
        star a ⬝ᵥ
            (LinearMap.toMatrix₂ b b (g.metricBilinAt x)).mulVec a =
          g.metricBilinAt x (b.equivFun.symm a)
            (b.equivFun.symm a) := by
      simpa using hquadratic
    rw [heq]
    rw [g.metricBilinAt_apply]
    exact g.inner_pos x hva

end ClosedSmoothRiemannianMetric

/-- Every actual inverse-chart pullback Gram matrix is positive definite.

The inverse-chart derivative applied to the Euclidean frame is a genuine
tangent basis because the inverse-chart derivative is invertible on the
extended-chart target.  The general basis theorem therefore applies. -/
theorem inverseChartPullbackGramMatrix_posDef
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) :
    (inverseChartPullbackGramMatrix g x₀ z).PosDef := by
  exact
    ClosedSmoothRiemannianMetric.metricMatrixInBasisAt_posDef g
      (inverseExtendedChartParametrization (n := n) (M := M) x₀ z)
      (ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
        (n := n) (M := M) x₀ z.2)

/-- The exact constant-coefficient area formula obtained by freezing the
inverse-chart Gram matrix at `z₀`.

The metric used by the source Hausdorff measure is pulled back along the
positive square-root representative of the single matrix `G(z₀)`.  Its
density is the constant value of the actual inverse-chart density at `z₀`.
-/
def FrozenInverseChartPullbackHausdorffAreaFormulaAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) : Prop :=
  let U := (extChartAt I x₀).target
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  let ψ := linearPullbackParametrization e U
  let hψ := linearPullbackParametrization_isEmbedding e U
  let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
  let pullbackEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U pullbackMetric
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
  (μH[(n : ℝ)] : Measure U) =
    rawHausdorffCoordinateDensityMeasure U
      (fun _ ↦ inverseChartPullbackVolumeDensity g x₀ z₀)

/-- The frozen inverse-chart area formula is unconditional: openness of the
genuine extended-chart target gives measurability, and pointwise Riemannian
positivity supplies the positive-definite constant Gram matrix. -/
theorem frozenInverseChartPullbackHausdorffAreaFormulaAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) :
    FrozenInverseChartPullbackHausdorffAreaFormulaAt g x₀ z₀ := by
  rw [FrozenInverseChartPullbackHausdorffAreaFormulaAt]
  have harea :=
    positiveDefiniteConstantGramHausdorffAreaFormula
      (n := n) (U := (extChartAt I x₀).target)
      (isOpen_extChartAt_target x₀).measurableSet
      (inverseChartPullbackGramMatrix g x₀ z₀)
      (inverseChartPullbackGramMatrix_posDef g x₀ z₀)
  simpa only [inverseChartPullbackVolumeDensity] using harea

end Poincare
