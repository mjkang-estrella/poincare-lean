import Poincare.Global.HeatCauchyNext2
import Poincare.Global.HeatSemigroupBUCPositiveGenerator
import Poincare.Global.RiemannianContext
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Poincare.HeatKernelHessianMoments

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

/-- Dilation of the full spatial Hessian in dimension three. -/
theorem hessian_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    Hess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • Hess 1 x := by
  ext v w
  have hformula (t : ℝ) (ht : t ≠ 0) (u : E) :=
    iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
  simp [iteratedFDeriv_two_apply] at hformula
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hformula _ (pow_ne_zero _ ha.ne'), hformula _ one_ne_zero,
    heatKernel_sq_smul a ha x]
  simp only [inner_smul_left, conj_trivial, finrank_euclideanSpace_fin]
  field_simp

/-- A fractional radial weight is absorbed by a fixed Gaussian. -/
theorem rpow_mul_gaussian_le_eight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
    {r : ℝ} (hr : 0 ≤ r) : r ^ α * Real.exp (-(r ^ 2 / 8)) ≤ 8 := by
  have hpoly : r ^ α ≤ 1 + r ^ 2 := by
    by_cases hr1 : r ≤ 1
    · exact (Real.rpow_le_one hr hr1 hα).trans (by nlinarith [sq_nonneg r])
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hα2
      rw [Real.rpow_two] at h
      linarith
  have hbound : 1 + r ^ 2 ≤ 8 * Real.exp (r ^ 2 / 8) := by
    have h := Real.add_one_le_exp (r ^ 2 / 8)
    linarith
  calc
    r ^ α * Real.exp (-(r ^ 2 / 8)) ≤
        (8 * Real.exp (r ^ 2 / 8)) * Real.exp (-(r ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_right (hpoly.trans hbound) (Real.exp_pos _).le
    _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp

/-- The weighted Hessian norm is integrable at unit time. -/
theorem integrable_weighted_hessian_one {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) :
    Integrable (fun x : E => ‖Hess 1 x‖ * ‖x‖ ^ α) := by
  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hweight : Continuous (fun x : E => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))) :=
    ((Real.continuous_rpow_const hα).comp continuous_norm).mul
      (((continuous_norm.pow 2).div_const 8).neg.rexp)
  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
      hweight.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => show
        ‖‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
          rw [Real.norm_of_nonneg (by positivity)]
          exact rpow_mul_gaussian_le_eight hα hα2 (norm_nonneg x))
  have hcont : ContDiff ℝ 0 (Hess 1) :=
    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
  refine (hbound.const_mul c).mono'
    (hcont.continuous.norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  have hH := norm_fderiv_fderiv_heatKernel_le_order_two («E» := E) zero_lt_one x
  have hK : heatKernel (1 : ℝ) x =
      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
    rw [← Real.exp_add]
    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
      Nat.cast_ofNat, mul_one]
    congr 1
    congr 1
    ring
  calc
    ‖Hess 1 x‖ * ‖x‖ ^ α ≤
        (heatKernel 1 x * (‖x‖ ^ 2 / (4 * 1 ^ 2) + 1 / (2 * 1))) * ‖x‖ ^ α :=
      mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg x) α)
    _ ≤ (heatKernel 1 x * (1 + ‖x‖ ^ 2)) * ‖x‖ ^ α := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
      nlinarith [sq_nonneg ‖x‖]
    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
        (‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK]; ring

end Poincare.HeatKernelHessianMoments
