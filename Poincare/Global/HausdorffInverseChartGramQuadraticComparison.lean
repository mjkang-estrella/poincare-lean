import Poincare.Global.HausdorffInverseChartGramContinuity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Uniform quadratic comparison with a frozen inverse-chart Gram matrix

Continuity of the inverse-chart Gram matrix gives entrywise comparison near a
fixed coordinate `z₀`.  The result needed by metric-length arguments is
stronger: one neighborhood must work simultaneously for every tangent vector,
with error measured relative to the positive frozen quadratic form.

This file obtains that uniformity on the unit sphere.  At each unit vector the
frozen quadratic form is strictly positive, joint continuity gives a product
neighborhood, and compactness of the finite-dimensional unit sphere produces
one coordinate neighborhood valid for all directions.  Homogeneity then
extends the estimate to every vector, including zero with non-strict bounds.

The resulting positive-semidefinite difference statements are precisely the
local Loewner comparison.  They still concern pointwise metric tensors.  No
claim about lengths of curves leaving the comparison neighborhood, global
path metrics, or the variable-metric Hausdorff area formula is made here.
-/

noncomputable section

open Bundle FiberBundle Filter Matrix MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  Matrix.Norms.Elementwise MatrixOrder

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n

/-- The coordinate quadratic form of the actual inverse-chart Gram matrix. -/
noncomputable def inverseChartPullbackQuadraticForm
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) (v : Fin n → ℝ) : ℝ :=
  v ⬝ᵥ (inverseChartPullbackGramMatrix g x₀ z *ᵥ v)

@[simp]
theorem inverseChartPullbackQuadraticForm_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) :
    inverseChartPullbackQuadraticForm g x₀ z 0 = 0 := by
  simp [inverseChartPullbackQuadraticForm]

/-- Quadratic homogeneity in the coordinate vector. -/
theorem inverseChartPullbackQuadraticForm_smul
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) (c : ℝ) (v : Fin n → ℝ) :
    inverseChartPullbackQuadraticForm g x₀ z (c • v) =
      c ^ 2 * inverseChartPullbackQuadraticForm g x₀ z v := by
  unfold inverseChartPullbackQuadraticForm
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, pow_two, mul_assoc]

/-- Positive definiteness of the actual Gram matrix is strict positivity of
its coordinate quadratic form away from the zero vector. -/
theorem inverseChartPullbackQuadraticForm_pos
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < inverseChartPullbackQuadraticForm g x₀ z v := by
  unfold inverseChartPullbackQuadraticForm
  simpa only [star_trivial] using
    (inverseChartPullbackGramMatrix_posDef g x₀ z).dotProduct_mulVec_pos hv

/-- The quadratic form is jointly continuous in the genuine chart coordinate
and the coordinate tangent vector. -/
theorem continuous_inverseChartPullbackQuadraticForm
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    Continuous
      (fun p : (extChartAt I x₀).target × (Fin n → ℝ) ↦
        inverseChartPullbackQuadraticForm g x₀ p.1 p.2) := by
  unfold inverseChartPullbackQuadraticForm
  exact continuous_snd.dotProduct
    (((continuous_inverseChartPullbackGramMatrix g x₀).comp continuous_fst).matrix_mulVec
      continuous_snd)

/-- On one neighborhood of `z₀`, the relative quadratic error is strict in
every unit direction.  Compactness of the unit sphere is the source of the
single common neighborhood. -/
theorem inverseChartPullbackQuadraticForm_eventually_unit_relative_error_lt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀, ∀ v ∈ Metric.sphere (0 : Fin n → ℝ) 1,
      |inverseChartPullbackQuadraticForm g x₀ z v -
          inverseChartPullbackQuadraticForm g x₀ z₀ v| <
        ε * inverseChartPullbackQuadraticForm g x₀ z₀ v := by
  let q := fun p : (extChartAt I x₀).target × (Fin n → ℝ) ↦
    inverseChartPullbackQuadraticForm g x₀ p.1 p.2
  have hq : Continuous q := by
    simpa only [q] using continuous_inverseChartPullbackQuadraticForm g x₀
  have hqFrozen : Continuous
      (fun p : (extChartAt I x₀).target × (Fin n → ℝ) ↦
        inverseChartPullbackQuadraticForm g x₀ z₀ p.2) := by
    exact hq.comp (continuous_const.prodMk continuous_snd)
  apply (isCompact_sphere (0 : Fin n → ℝ) 1).eventually_forall_of_forall_eventually
  intro v hv
  have hv0 : v ≠ 0 := Metric.ne_of_mem_sphere hv one_ne_zero
  have hq0 : 0 < inverseChartPullbackQuadraticForm g x₀ z₀ v :=
    inverseChartPullbackQuadraticForm_pos g x₀ z₀ hv0
  have hLeft : ContinuousAt
      (fun p : (extChartAt I x₀).target × (Fin n → ℝ) ↦
        |q p - inverseChartPullbackQuadraticForm g x₀ z₀ p.2|)
      (z₀, v) :=
    (hq.sub hqFrozen).abs.continuousAt
  have hRight : ContinuousAt
      (fun p : (extChartAt I x₀).target × (Fin n → ℝ) ↦
        ε * inverseChartPullbackQuadraticForm g x₀ z₀ p.2)
      (z₀, v) :=
    (continuous_const.mul hqFrozen).continuousAt
  apply hLeft.eventually_lt hRight
  simpa only [q, sub_self, abs_zero] using mul_pos hε hq0

/-- The strict unit-sphere estimate extends by quadratic homogeneity to a
non-strict relative-error estimate for every coordinate vector. -/
theorem inverseChartPullbackQuadraticForm_eventually_relative_error_le
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀, ∀ v : Fin n → ℝ,
      |inverseChartPullbackQuadraticForm g x₀ z v -
          inverseChartPullbackQuadraticForm g x₀ z₀ v| ≤
        ε * inverseChartPullbackQuadraticForm g x₀ z₀ v := by
  have hUnit :=
    inverseChartPullbackQuadraticForm_eventually_unit_relative_error_lt
      g x₀ z₀ hε
  filter_upwards [hUnit] with z hz
  intro v
  by_cases hv0 : v = 0
  · subst v
    simp
  · let u : Fin n → ℝ := (‖v‖⁻¹ : ℝ) • v
    have hu : u ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      apply mem_sphere_zero_iff_norm.mpr
      exact norm_smul_inv_norm hv0
    have hUnitError := hz u hu
    have hnorm0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    have hnormSq : 0 < ‖v‖ ^ 2 := sq_pos_of_ne_zero hnorm0
    have hvScale : v = ‖v‖ • u := by
      dsimp only [u]
      exact (smul_inv_smul₀ hnorm0 v).symm
    have hQuadraticScale
        (w : (extChartAt I x₀).target) :
        inverseChartPullbackQuadraticForm g x₀ w v =
          ‖v‖ ^ 2 * inverseChartPullbackQuadraticForm g x₀ w u := by
      calc
        inverseChartPullbackQuadraticForm g x₀ w v =
            inverseChartPullbackQuadraticForm g x₀ w (‖v‖ • u) :=
          congrArg (inverseChartPullbackQuadraticForm g x₀ w) hvScale
        _ = _ := inverseChartPullbackQuadraticForm_smul g x₀ w ‖v‖ u
    have hScaled := mul_lt_mul_of_pos_left hUnitError hnormSq
    apply le_of_lt
    calc
      |inverseChartPullbackQuadraticForm g x₀ z v -
          inverseChartPullbackQuadraticForm g x₀ z₀ v| =
          ‖v‖ ^ 2 *
            |inverseChartPullbackQuadraticForm g x₀ z u -
              inverseChartPullbackQuadraticForm g x₀ z₀ u| := by
        rw [hQuadraticScale z, hQuadraticScale z₀, ← mul_sub, abs_mul,
          abs_of_nonneg (sq_nonneg ‖v‖)]
      _ < ‖v‖ ^ 2 *
          (ε * inverseChartPullbackQuadraticForm g x₀ z₀ u) := hScaled
      _ = ε * inverseChartPullbackQuadraticForm g x₀ z₀ v := by
        rw [hQuadraticScale z₀]
        ring

/-- Uniform local comparison of the variable and frozen quadratic forms.
The inequalities are non-strict so that the statement also includes `v = 0`.
-/
theorem inverseChartPullbackQuadraticForm_eventually_relative_bounds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀, ∀ v : Fin n → ℝ,
      (1 - ε) * inverseChartPullbackQuadraticForm g x₀ z₀ v ≤
          inverseChartPullbackQuadraticForm g x₀ z v ∧
        inverseChartPullbackQuadraticForm g x₀ z v ≤
          (1 + ε) * inverseChartPullbackQuadraticForm g x₀ z₀ v := by
  have hError :=
    inverseChartPullbackQuadraticForm_eventually_relative_error_le
      g x₀ z₀ hε
  filter_upwards [hError] with z hz
  intro v
  rcases abs_le.mp (hz v) with ⟨hlower, hupper⟩
  constructor <;> nlinarith

/-- Metric-ball form of the same uniform comparison, convenient for curves
whose coordinate image is known to remain in a sufficiently small ball. -/
theorem exists_inverseChartPullbackQuadraticForm_ball_relative_bounds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ {z : (extChartAt I x₀).target},
      dist z z₀ < r → ∀ v : Fin n → ℝ,
        (1 - ε) * inverseChartPullbackQuadraticForm g x₀ z₀ v ≤
            inverseChartPullbackQuadraticForm g x₀ z v ∧
          inverseChartPullbackQuadraticForm g x₀ z v ≤
            (1 + ε) * inverseChartPullbackQuadraticForm g x₀ z₀ v := by
  exact Metric.eventually_nhds_iff.mp
    (inverseChartPullbackQuadraticForm_eventually_relative_bounds
      g x₀ z₀ hε)

/-- Equivalent positive-semidefinite form of the local quadratic comparison.
These are the two matrix differences defining the Loewner bounds. -/
theorem inverseChartPullbackGramMatrix_eventually_relative_posSemidef
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀,
      (inverseChartPullbackGramMatrix g x₀ z -
          (1 - ε) • inverseChartPullbackGramMatrix g x₀ z₀).PosSemidef ∧
        ((1 + ε) • inverseChartPullbackGramMatrix g x₀ z₀ -
          inverseChartPullbackGramMatrix g x₀ z).PosSemidef := by
  have hBounds :=
    inverseChartPullbackQuadraticForm_eventually_relative_bounds
      g x₀ z₀ hε
  filter_upwards [hBounds] with z hz
  have hGz := inverseChartPullbackGramMatrix_posDef g x₀ z
  have hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hGz.isHermitian.sub
        (hG₀.isHermitian.smul (isSelfAdjoint_iff.mpr rfl))) ?_
    intro v
    have hv := sub_nonneg.mpr (hz v).1
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, star_trivial, smul_eq_mul,
      inverseChartPullbackQuadraticForm] using hv
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hG₀.isHermitian.smul (isSelfAdjoint_iff.mpr rfl)).sub
        hGz.isHermitian) ?_
    intro v
    have hv := sub_nonneg.mpr (hz v).2
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, star_trivial, smul_eq_mul,
      inverseChartPullbackQuadraticForm] using hv

/-- Local Loewner comparison of the variable inverse-chart Gram matrix with
its frozen value.  If additionally `ε < 1`, both comparison factors are
positive and this is the usual two-sided uniform metric equivalence. -/
theorem inverseChartPullbackGramMatrix_eventually_loewner_bounds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in nhds z₀,
      (1 - ε) • inverseChartPullbackGramMatrix g x₀ z₀ ≤
          inverseChartPullbackGramMatrix g x₀ z ∧
        inverseChartPullbackGramMatrix g x₀ z ≤
          (1 + ε) • inverseChartPullbackGramMatrix g x₀ z₀ := by
  simpa only [Matrix.le_iff] using
    inverseChartPullbackGramMatrix_eventually_relative_posSemidef
      g x₀ z₀ hε

/-- The corresponding local comparison of Riemannian speed integrands.  This
is the pointwise estimate that can be integrated along any curve known to stay
inside the comparison neighborhood. -/
theorem inverseChartPullbackQuadraticForm_eventually_sqrt_relative_bounds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ z in nhds z₀, ∀ v : Fin n → ℝ,
      Real.sqrt (1 - ε) *
          Real.sqrt (inverseChartPullbackQuadraticForm g x₀ z₀ v) ≤
        Real.sqrt (inverseChartPullbackQuadraticForm g x₀ z v) ∧
      Real.sqrt (inverseChartPullbackQuadraticForm g x₀ z v) ≤
        Real.sqrt (1 + ε) *
          Real.sqrt (inverseChartPullbackQuadraticForm g x₀ z₀ v) := by
  have hBounds :=
    inverseChartPullbackQuadraticForm_eventually_relative_bounds
      g x₀ z₀ hε0
  have hLowerFactor : 0 ≤ 1 - ε := by linarith
  have hUpperFactor : 0 ≤ 1 + ε := by linarith
  filter_upwards [hBounds] with z hz
  intro v
  constructor
  · have h := Real.sqrt_le_sqrt (hz v).1
    rwa [Real.sqrt_mul hLowerFactor] at h
  · have h := Real.sqrt_le_sqrt (hz v).2
    rwa [Real.sqrt_mul hUpperFactor] at h

end Poincare
