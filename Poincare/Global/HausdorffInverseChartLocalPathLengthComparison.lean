import Poincare.Global.HausdorffInverseChartGramQuadraticComparison
import Poincare.Global.GeodesicLength
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Local inverse-chart path-length comparison

The preceding inverse-chart Gram comparison is pointwise in the tangent
vector.  This file identifies its quadratic form with the genuine
Riemannian speed of an inverse-chart curve and integrates the resulting
uniform estimate.

At a fixed chart coordinate `z₀`, define the frozen speed integral by using
the single quadratic form `inverseChartPullbackQuadraticForm g x₀ z₀` along
the coordinate velocity of a curve.  For every relative tolerance
`0 < ε < 1`, there is one coordinate ball such that every differentiable
curve contained in that ball has genuine Riemannian path length between the
`sqrt (1 - ε)` and `sqrt (1 + ε)` multiples of its frozen speed integral.

This is the curve-length bridge needed before a local bi-Lipschitz argument.
It deliberately does not claim a comparison of the unrestricted global path
metric: a minimizing sequence between nearby points might leave the chart
ball unless one also proves a short-path confinement lemma.  Mathlib's
Hausdorff-measure inequalities for Lipschitz maps can be applied after that
metric-level bridge, but they do not by themselves supply the variable-metric
area formula.
-/

noncomputable section

open Bundle Filter Matrix MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  RealInnerProductSpace

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

/-- The Gram-matrix quadratic form is the transported chart metric evaluated
on the corresponding Euclidean tangent vector. -/
theorem inverseChartPullbackQuadraticForm_eq_chartMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) (v : E) :
    inverseChartPullbackQuadraticForm g x₀ z (fun i ↦ v i) =
      CovariantDerivative.chartMetric g.inner x₀ (z : E) v v := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let B := CovariantDerivative.chartMetric g.inner x₀ (z : E)
  have hmatrix :
      inverseChartPullbackGramMatrix g x₀ z =
        LinearMap.toMatrix₂ b b B.toBilinForm := by
    rw [inverseChartPullbackGramMatrix_eq_field]
    ext i j
    simp only [inverseChartPullbackGramMatrixField,
      LinearMap.toMatrix₂_apply, ContinuousLinearMap.toBilinForm_apply,
      OrthonormalBasis.coe_toBasis, b, B]
  have hrepr : b.repr v = (fun i ↦ v i) := by
    funext i
    rfl
  rw [inverseChartPullbackQuadraticForm, hmatrix, ← hrepr]
  exact
    (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
      b B.toBilinForm v v).symm

/-- The e-norm of the genuine manifold velocity of an inverse-chart curve is
the square root of the inverse-chart Gram quadratic form. -/
theorem inverseChartCurve_enorm_mfderiv_eq_pullbackQuadraticForm
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : ℝ → E} {v : E} {s : ℝ}
    (hz : z s ∈ (extChartAt I x₀).target)
    (hzder : HasDerivAt z v s) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ‖mfderiv 𝓘(ℝ) I
        (fun r : ℝ ↦ (extChartAt I x₀).symm (z r)) s 1‖ₑ =
      ENNReal.ofReal
        (Real.sqrt
          (inverseChartPullbackQuadraticForm g x₀ ⟨z s, hz⟩
            (fun i ↦ v i))) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rw [GeodesicTransport.inverseChartCurve_enorm_mfderiv_eq_chartMetric
    (g := g) (x₀ := x₀) hz hzder]
  rw [inverseChartPullbackQuadraticForm_eq_chartMetric]

/-- The path-length functional for the frozen inverse-chart metric tensor at
`z₀`, evaluated on a prescribed Euclidean velocity field. -/
noncomputable def frozenInverseChartSpeedIntegral
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) (v : ℝ → E)
    (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioo a b,
    ENNReal.ofReal
      (Real.sqrt
        (inverseChartPullbackQuadraticForm g x₀ z₀
          (fun i ↦ v s i)))

/-- An inverse-chart curve's genuine Riemannian path length is the integral
of the variable pullback Gram speed. -/
theorem inverseChartCurve_pathELength_eq_lintegral_pullbackQuadraticForm
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : ℝ → (extChartAt I x₀).target) (v : ℝ → E)
    (a b : ℝ)
    (hzder : ∀ s ∈ Ioo a b,
      HasDerivAt (fun r : ℝ ↦ (z r : E)) (v s) s) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    Manifold.pathELength I
        (fun r : ℝ ↦ (extChartAt I x₀).symm (z r : E)) a b =
      ∫⁻ s in Ioo a b,
        ENNReal.ofReal
          (Real.sqrt
            (inverseChartPullbackQuadraticForm g x₀ (z s)
              (fun i ↦ v s i))) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  exact inverseChartCurve_enorm_mfderiv_eq_pullbackQuadraticForm
    (g := g) (x₀ := x₀) (z s).2 (hzder s hs)

/-- On one coordinate ball, every inverse-chart curve has genuine
Riemannian length uniformly comparable to its frozen-metric speed integral.

The radius is independent of the curve, its velocity field, and its time
interval.  Only containment of the curve in the ball and pointwise
differentiability on the interior of the interval are required. -/
theorem exists_inverseChartCurve_pathELength_relative_bounds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r > 0, ∀ (z : ℝ → (extChartAt I x₀).target) (v : ℝ → E)
      (a b : ℝ),
      (∀ s ∈ Ioo a b, dist (z s) z₀ < r) →
      (∀ s ∈ Ioo a b,
        HasDerivAt (fun t : ℝ ↦ (z t : E)) (v s) s) →
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      ENNReal.ofReal (Real.sqrt (1 - ε)) *
          frozenInverseChartSpeedIntegral g x₀ z₀ v a b ≤
        Manifold.pathELength I
          (fun t : ℝ ↦ (extChartAt I x₀).symm (z t : E)) a b ∧
      Manifold.pathELength I
          (fun t : ℝ ↦ (extChartAt I x₀).symm (z t : E)) a b ≤
        ENNReal.ofReal (Real.sqrt (1 + ε)) *
          frozenInverseChartSpeedIntegral g x₀ z₀ v a b := by
  rcases Metric.eventually_nhds_iff.mp
      (inverseChartPullbackQuadraticForm_eventually_sqrt_relative_bounds
        g x₀ z₀ hε0 hε1) with ⟨r, hr, hspeed⟩
  refine ⟨r, hr, ?_⟩
  intro z v a b hstay hzder
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rw [inverseChartCurve_pathELength_eq_lintegral_pullbackQuadraticForm
    (g := g) (x₀ := x₀) z v a b hzder]
  rw [frozenInverseChartSpeedIntegral]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Ioo
    intro s hs
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      ((hspeed (hstay s hs) (fun i ↦ v s i)).1)
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Ioo
    intro s hs
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      ((hspeed (hstay s hs) (fun i ↦ v s i)).2)

end Poincare
