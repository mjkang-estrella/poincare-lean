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

/-- Pointwise parabolic dilation including the radial weight. -/
theorem weighted_hessian_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
    ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
      ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (‖Hess 1 x‖ * ‖x‖ ^ α) := by
  rw [hessian_sq_smul a ha x, norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 2)⁻¹ by positivity) (Hess 1 x),
    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
  ring

/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
theorem weighted_hessian_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
    (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
      ((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => ‖Hess (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
  calc
    (a ^ 3)⁻¹ * (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
        ∫ x : E, ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
    _ = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
      simp_rw [weighted_hessian_sq_smul a ha]
      rw [integral_const_mul]
    _ = (a ^ 3)⁻¹ * (((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α)) := by ring

/-- Weighted Bochner integrability at every positive time. -/
theorem integrable_weighted_hessian {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) := by
  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [← Real.sq_sqrt ht.le]
  apply (integrable_comp_smul_iff volume _ ha.ne').1
  simp_rw [weighted_hessian_sq_smul (Real.sqrt t) ha]
  exact (integrable_weighted_hessian_one hα hα2).const_mul _

/-- Exact positive-time scaling of the weighted Hessian integral. -/
theorem weighted_hessian_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) =
      t ^ (α / 2 - 1) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
  have h := weighted_hessian_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
  rw [Real.sq_sqrt ht.le] at h
  rw [h]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_one]
  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
  ring

/-- The full operator-valued Hessian is Bochner integrable. -/
theorem integrable_hessian {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => Hess t x) := by
  have hcont : ContDiff ℝ 0 (Hess t) :=
    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
  apply (integrable_norm_iff hcont.continuous.aestronglyMeasurable).1
  simpa using integrable_weighted_hessian (α := 0) (by norm_num) (by norm_num) ht

/-- Tensor cancellation follows by twice differentiating the heat evolution of one. -/
theorem integral_hessian_eq_zero {t : ℝ} (ht : 0 < t) :
    (∫ x : E, Hess t x) = 0 := by
  have hmass : heatSolution t (fun _ : E => (1 : ℝ)) = fun _ => 1 := by
    funext x
    simpa only [heatSolution_apply, mul_one] using
      (integral_heatKernel_eq_one («E» := E) ht)
  ext v w
  have hiv : Integrable (fun x : E => Hess t x v) := by
    exact (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp (integrable_hessian ht)
  rw [ContinuousLinearMap.integral_apply (integrable_hessian ht),
    ContinuousLinearMap.integral_apply hiv]
  have hder := heatSolution_fderiv_apply_hasFDerivAt ht
    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
    (C := 1) (by intro y; simp) (0 : E) w
  simp only [hmass, fderiv_const_apply, ContinuousLinearMap.zero_apply] at hder
  have hc := hder.unique (hasFDerivAt_const (0 : ℝ) (0 : E))
  have hi := integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht
    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
    (C := 1) (by intro y; simp) (0 : E) w
  have hev := congrArg (fun L : E →L[ℝ] ℝ => L v) hc
  dsimp only at hev
  rw [ContinuousLinearMap.integral_apply hi] at hev
  simp only [one_smul, ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hev ⊢
  rw [integral_sub_left_eq_self (fun y : E => Hess t y v w) volume (0 : E)] at hev
  exact hev

/-- Sharp weighted Hessian moments and tensor cancellation for the heat kernel. -/
theorem hessian_moments :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
      (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
      Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0 := by
  intro α hα hα1
  refine ⟨max 1 (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht _
  refine ⟨integrable_weighted_hessian hα.le (by linarith) ht, ?_,
    integrable_hessian ht, integral_hessian_eq_zero ht⟩
  rw [weighted_hessian_integral ht, mul_comm (t ^ (α / 2 - 1))]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

end Poincare.HeatKernelHessianMoments
