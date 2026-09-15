import Poincare.Global.HeatCauchyNext2
import Poincare.Global.HeatSemigroupBUCPositiveGenerator
import Poincare.Global.RiemannianContext
import Mathlib.Analysis.SpecificLimits.Normed
import Poincare.Global.HeatMildBUCPositiveHolder
import Mathlib.Analysis.MeanInequalitiesPow
import Poincare.Global.ParabolicHolderSpace
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Poincare.Global.ParabolicSolutionGraph

section

set_option autoImplicit false

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
  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
      («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
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
  rw [hessian_sq_smul a ha x,
    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 2)⁻¹ by positivity) (Hess 1 x),
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

end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Poincare.HeatDuhamelSpatialHolderHessian

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments

/-- The full translated Hessian integrand is integrable for bounded measurable data. -/
theorem integrable_data_smul_hessian_sub {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    Integrable (fun y : E => f y • Hess t (x - y)) := by
  have hi := (integrable_hessian ht).norm.comp_sub_left x
  refine (hi.const_mul M).mono'
    (smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable t hf x) ?_
  exact Filter.Eventually.of_forall fun y => by
    calc
      ‖f y • Hess t (x - y)‖ ≤ ‖f y‖ * ‖Hess t (x - y)‖ :=
        norm_real_smul_continuousLinearMap_two_le _ _
      _ ≤ M * ‖Hess t (x - y)‖ :=
        mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

/-- The spatial Hessian of the heat convolution is the convolution with the full kernel Hessian. -/
theorem hessian_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
      ∫ y : E, f y • Hess t (x - y) := by
  have htwo := contDiff_two_heatSolution_of_bounded_measurable ht hf hM
  have hD := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) x).hasFDerivAt
  have hi := integrable_data_smul_hessian_sub ht hf hM x
  ext v w
  have hc := hD.clm_apply (hasFDerivAt_const w x)
  have hg := heatSolution_fderiv_apply_hasFDerivAt ht hf hM x w
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hc.unique hg)
  have hiv : Integrable (fun y : E => (f y • Hess t (x - y)) v) :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp hi
  rw [ContinuousLinearMap.integral_apply hi,
    ContinuousLinearMap.integral_apply hiv]
  dsimp only at he
  rw [ContinuousLinearMap.integral_apply
    (integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht hf hM x w)] at he
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, add_zero,
    ContinuousLinearMap.smul_apply, smul_eq_mul, map_zero, zero_add] using he

/-- Changing variables puts the kernel Hessian at the integration variable. -/
theorem hessian_heatSolution_eq_integral_sub {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
      ∫ y : E, f (x - y) • Hess t y := by
  rw [hessian_heatSolution_eq_integral ht hf hM]
  have hc := integral_sub_left_eq_self
    (fun y : E => f y • Hess t (x - y)) volume x
  simpa only [sub_sub_cancel] using hc.symm

/-- Integrability also holds with bounded data translated against the fixed kernel. -/
theorem integrable_data_sub_smul_hessian {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    Integrable (fun y : E => f (x - y) • Hess t y) := by
  simpa only [sub_sub_cancel] using
    (integrable_data_smul_hessian_sub ht hf hM x).comp_sub_left x

/-- Tensor cancellation removes the value of the forcing at the observation point. -/
theorem hessian_heatSolution_eq_cancelled_integral {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
      ∫ y : E, (f (x - y) - f x) • Hess t y := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  have hc : Integrable (fun y : E => f x • Hess t y) :=
    (integrable_hessian ht).smul (f x)
  rw [hessian_heatSolution_eq_integral_sub ht hf hM]
  simp_rw [sub_smul]
  rw [integral_sub (integrable_data_sub_smul_hessian ht hf hM x)
    hc, integral_smul,
    integral_hessian_eq_zero ht, smul_zero, sub_zero]

/-- The cancelled Hessian integral remains a genuine Bochner integral. -/
theorem integrable_cancelled_hessian {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    Integrable (fun y : E => (f (x - y) - f x) • Hess t y) := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  have hc : Integrable (fun y : E => f x • Hess t y) :=
    (integrable_hessian ht).smul (f x)
  simpa only [sub_smul] using (integrable_data_sub_smul_hessian ht hf hM x).sub hc

/-- Spatial Hölder increments supply the weighted Hessian majorant. -/
theorem norm_cancelled_hessian_integrand_le {α K : ℝ} {f : E → ℝ}
    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α)
    (t : ℝ) (x y : E) :
    ‖(f (x - y) - f x) • Hess t y‖ ≤ K * (‖Hess t y‖ * ‖y‖ ^ α) := by
  have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
    have h := hK (x - y) x
    have he : x - y - x = -y := by abel
    simpa only [he, norm_neg, Real.norm_eq_abs] using h
  calc
    ‖(f (x - y) - f x) • Hess t y‖ ≤ ‖f (x - y) - f x‖ * ‖Hess t y‖ :=
      norm_real_smul_continuousLinearMap_two_le _ _
    _ ≤ (K * ‖y‖ ^ α) * ‖Hess t y‖ :=
      mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    _ = K * (‖Hess t y‖ * ‖y‖ ^ α) := by ring

/-- Integrating the spatial Hölder majorant gives the sharp time power. -/
theorem norm_cancelled_hessian_integral_le {α K t : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ht : 0 < t) {f : E → ℝ}
    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
      K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) := by
  calc
    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
        ∫ y : E, K * (‖Hess t y‖ * ‖y‖ ^ α) :=
      norm_integral_le_of_norm_le ((integrable_weighted_hessian hα hα2 ht).const_mul K)
        (Filter.Eventually.of_forall fun y => norm_cancelled_hessian_integrand_le hK t x y)
    _ = K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) := by
      rw [integral_const_mul, weighted_hessian_integral ht]
      ring

/-- A positive constant depending only on the exponent bounds the actual heat Hessian. -/
theorem exists_heat_hessian_holder_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t M K : ℝ}, 0 < t → 0 ≤ K →
      ∀ {f : E → ℝ}, AEStronglyMeasurable f volume → (∀ y, ‖f y‖ ≤ M) →
      (∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) → ∀ x : E,
      ‖fderiv ℝ (fderiv ℝ (heatSolution t f)) x‖ ≤ C * K * t ^ (α / 2 - 1) := by
  refine ⟨max 1 (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t M K ht hK0 f hf hM hK x
  rw [hessian_heatSolution_eq_cancelled_integral ht hf hM]
  calc
    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
        K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) :=
      norm_cancelled_hessian_integral_le hα.le (by linarith) ht hK x
    _ ≤ max 1 (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * K * t ^ (α / 2 - 1) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      rw [mul_comm K]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hK0

/-- The sharp Hessian time majorant is integrable, including its singular endpoint. -/
theorem intervalIntegrable_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
    IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) volume 0 t := by
  have hi := (intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := t) (r := α / 2 - 1) (by linarith)).comp_sub_left t
  have hj : IntervalIntegrable (fun s : ℝ => (t - s) ^ (α / 2 - 1)) volume 0 t := by
    simpa only [sub_zero, sub_self] using hi.symm
  exact hj.const_mul A

/-- Exact integration of the time majorant supplies the factor two over the exponent. -/
theorem integral_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
    (∫ s in (0 : ℝ)..t, A * (t - s) ^ (α / 2 - 1)) =
      A * (2 / α) * t ^ (α / 2) := by
  rw [intervalIntegral.integral_const_mul]
  have he : α / 2 - 1 = -(1 - α / 2) := by ring
  simp_rw [he]
  rw [integral_sub_rpow_neg (by linarith : 1 - α / 2 < 1)]
  rw [show 1 - (1 - α / 2) = α / 2 by ring]
  field_simp

/-- Dilation gives joint continuity of the full Hessian at positive times. -/
theorem continuous_hessian_pos :
    Continuous (fun p : Ioi (0 : ℝ) × E => Hess p.1 p.2) := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  have hunit : ContDiff ℝ 0 (Hess 1) :=
    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
    Real.sqrt_pos.2 p.1.property
  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * ((Real.sqrt (p.1 : ℝ)) ^ 2)⁻¹) •
        Hess 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
      ((ha.pow 2).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')) |>.smul
      (hunit.continuous.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
  apply hc.congr
  intro p
  have h := hessian_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm

/-- The cancelled spatial integral is integrable over the Duhamel time interval. -/
theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) {f : ℝ × E → ℝ}
    (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntegrableOn (fun s : ℝ => ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) (Ioo 0 t) := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hf1 : Continuous (fun p : Ioo (0 : ℝ) t × E => f ((p.1 : ℝ), x - p.2)) :=
    hf.comp_continuous (hs.prodMk (continuous_const.sub continuous_snd))
      (fun p => ⟨hmem p.1, mem_univ _⟩)
  have hf2 : Continuous (fun p : Ioo (0 : ℝ) t × E => f ((p.1 : ℝ), x)) :=
    hf.comp_continuous (hs.prodMk continuous_const)
      (fun p => ⟨hmem p.1, mem_univ _⟩)
  have hH : Continuous (fun p : Ioo (0 : ℝ) t × E => Hess (t - (p.1 : ℝ)) p.2) :=
    continuous_hessian_pos.comp
      (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
        continuous_snd)
  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right' (ν := volume)
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
  have hi : IntegrableOn (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
      (intervalIntegrable_hessian_majorant hα t A)
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi ⊢
  refine hi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  exact norm_cancelled_hessian_integral_le hα.le (by linarith)
    (sub_pos.mpr s.property.2) (hK s (hmem s)) x

/-- The cancelled Duhamel integral has the required spatial Hessian size. -/
theorem norm_integral_cancelled_hessian_time_le {α K t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 ≤ t) {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo 0 t, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    ‖∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * t ^ (α / 2) := by
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
  have hi : IntegrableOn (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mp
      (intervalIntegrable_hessian_majorant hα t A)
  have hb : ‖∫ s in Ioo (0 : ℝ) t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      ∫ s in Ioo (0 : ℝ) t, A * (t - s) ^ (α / 2 - 1) := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
      (sub_pos.mpr hs.2) (hK s hs) x
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht,
    ← intervalIntegral.integral_of_le ht] at hb
  simpa only [integral_hessian_majorant hα, A] using hb

end Poincare.HeatDuhamelSpatialHolderHessian

end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval

namespace Poincare.HeatDuhamelHessianDifferentiation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Grad" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fun z : E => Poincare.heatKernel t z) x
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian

/-- The spatial gradient as an inner-product functional. -/
theorem gradient_eq {t : ℝ} (ht : t ≠ 0) (x : E) :
    Grad t x = (heatKernel t x * (-(1 / (2 * t)))) • innerSL ℝ x := by
  dsimp only
  rw [(hasFDerivAt_heatKernel_spatial («E» := E) ht x).fderiv]
  simp only [smul_smul, heatKernel]
  congr 1
  ring

/-- Parabolic dilation of the spatial gradient. -/
theorem gradient_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    Grad (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * a⁻¹) • Grad 1 x := by
  rw [gradient_eq (pow_ne_zero _ ha.ne'), gradient_eq one_ne_zero,
    heatKernel_sq_smul a ha x]
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
    inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
  field_simp

/-- The gradient kernel is Bochner integrable at positive time. -/
theorem integrable_gradient {t : ℝ} (ht : 0 < t) :
    Integrable (Grad t) := by
  have h := (integrable_smul_fderiv_heatKernel_sub («E» := E) ht
    (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (C := 1) (by intro y; simp) (0 : E)).comp_sub_left (0 : E)
  simpa only [one_smul, sub_sub_cancel] using h

/-- The spatial Jacobian leaves exactly one inverse length in the gradient moment. -/
theorem gradient_integral_sq (a : ℝ) (ha : 0 < a) :
    (∫ y : E, ‖Grad (a ^ 2) y‖) = a⁻¹ * (∫ y : E, ‖Grad 1 y‖) := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => ‖Grad (a ^ 2) y‖) a (hR := ha.le)
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
  calc
    (a ^ 3)⁻¹ * (∫ y : E, ‖Grad (a ^ 2) y‖) =
        ∫ y : E, ‖Grad (a ^ 2) (a • y)‖ := by
      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul]
        using hchange.symm
    _ = ((a ^ 3)⁻¹ * a⁻¹) * (∫ y : E, ‖Grad 1 y‖) := by
      simp_rw [gradient_sq_smul a ha]
      simp_rw [norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * a⁻¹ by positivity)
        (fderiv ℝ (fun z : E => heatKernel 1 z) _)]
      rw [integral_const_mul]
    _ = (a ^ 3)⁻¹ * (a⁻¹ * (∫ y : E, ‖Grad 1 y‖)) := by ring

/-- The exact first gradient moment has the inverse square-root time power. -/
theorem gradient_integral {t : ℝ} (ht : 0 < t) :
    (∫ y : E, ‖Grad t y‖) = (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
  have h := gradient_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht)
  rw [Real.sq_sqrt ht.le] at h
  rw [h, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
  ring

/-- The full gradient of bounded measurable heat data in translated coordinates. -/
theorem gradient_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    fderiv ℝ (heatSolution t f) x = ∫ y : E, f (x - y) • Grad t y := by
  rw [(heatSolution_hasFDerivAt ht hf hM x).fderiv]
  have hc := integral_sub_left_eq_self
    (fun y : E => f y • Grad t (x - y)) volume x
  simpa only [sub_sub_cancel] using hc.symm

/-- The sharp gradient majorant is uniform over observation points. -/
theorem norm_gradient_heatSolution_le {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
    ‖fderiv ℝ (heatSolution t f) x‖ ≤
      M * (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
  rw [gradient_heatSolution_eq_integral ht hf hM]
  calc
    ‖∫ y : E, f (x - y) • Grad t y‖ ≤ ∫ y : E, M * ‖Grad t y‖ := by
      apply norm_integral_le_of_norm_le ((integrable_gradient ht).norm.const_mul M)
      exact Filter.Eventually.of_forall fun y =>
        (norm_real_smul_continuousLinearMap_one_le _ _).trans
          (mul_le_mul_of_nonneg_right (hM (x - y)) (norm_nonneg _))
    _ = M * (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
      rw [integral_const_mul, gradient_integral ht, mul_assoc]

/-- Dilation gives joint continuity of the positive-time gradient kernel. -/
theorem continuous_gradient_pos :
    Continuous (fun p : Ioi (0 : ℝ) × E => Grad p.1 p.2) := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
  have hunit : ContDiff ℝ 0 (Grad 1) :=
    (contDiff_heatKernel_spatial («E» := E) 1).fderiv_right (m := 0) (by norm_num)
  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
    Real.sqrt_pos.2 p.1.property
  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * (Real.sqrt (p.1 : ℝ))⁻¹) •
        Grad 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
      (ha.inv₀ (fun p => (hapos p).ne')) |>.smul
      (hunit.continuous.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
  apply hc.congr
  intro p
  have h := gradient_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm

/-- Dilation puts the convolution gradient against a fixed unit-time kernel. -/
theorem gradient_convolution_sq (a : ℝ) (ha : 0 < a) (f : E → ℝ) (x : E) :
    (∫ y : E, f (x - y) • Grad (a ^ 2) y) =
      a⁻¹ • (∫ y : E, f (x - a • y) • Grad 1 y) := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => f (x - y) • Grad (a ^ 2) y) a (hR := ha.le)
  apply (smul_right_injective (M := E →L[ℝ] ℝ) (inv_ne_zero (pow_ne_zero 3 ha.ne')))
  calc
    (a ^ 3)⁻¹ • (∫ y : E, f (x - y) • Grad (a ^ 2) y) =
        ∫ y : E, f (x - a • y) • Grad (a ^ 2) (a • y) := by
      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin] using hchange.symm
    _ = ((a ^ 3)⁻¹ * a⁻¹) • (∫ y : E, f (x - a • y) • Grad 1 y) := by
      simp_rw [gradient_sq_smul a ha, smul_comm (f (x - a • _))]
      rw [integral_smul]
    _ = (a ^ 3)⁻¹ • (a⁻¹ • (∫ y : E, f (x - a • y) • Grad 1 y)) := by
      rw [smul_smul]

/-- The positive elapsed-time convolution gradient is jointly continuous. -/
theorem continuous_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) :
    Continuous (fun p : Ioo (0 : ℝ) t × E =>
      fderiv ℝ (heatSolution (t - p.1) (fun y => f (p.1, y))) p.2) := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have ha : Continuous (fun p : Ioo (0 : ℝ) t × E => Real.sqrt (t - p.1)) :=
    Real.continuous_sqrt.comp (continuous_const.sub hs)
  have hapos (p : Ioo (0 : ℝ) t × E) : 0 < Real.sqrt (t - p.1) :=
    Real.sqrt_pos.2 (sub_pos.mpr p.1.property.2)
  have hunit : Continuous (Grad 1) :=
    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
      (m := 0) (by norm_num)).continuous
  have hn : Continuous (fun p : Ioo (0 : ℝ) t × E =>
      ∫ y : E, f (p.1, p.2 - Real.sqrt (t - p.1) • y) • Grad 1 y) := by
    apply continuous_of_dominated (bound := fun y : E => M * ‖Grad 1 y‖)
    · intro p
      exact ((hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hmem p.1, mem_univ _⟩)).smul hunit).aestronglyMeasurable
    · intro p
      exact Filter.Eventually.of_forall fun y =>
        (norm_real_smul_continuousLinearMap_one_le _ _).trans
          (mul_le_mul_of_nonneg_right (hM p.1 (hmem p.1) _ ) (norm_nonneg _))
    · exact (integrable_gradient zero_lt_one).norm.const_mul M
    · exact Filter.Eventually.of_forall fun y =>
        (hf.comp_continuous (hs.prodMk (continuous_snd.sub (ha.smul continuous_const)))
          (fun p => ⟨hmem p.1, mem_univ _⟩)).smul continuous_const
  apply ((ha.inv₀ (fun p => (hapos p).ne')).smul hn).congr
  intro p
  have hfc : Continuous (fun y : E => f (p.1, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hmem p.1, mem_univ y⟩)
  rw [gradient_heatSolution_eq_integral (sub_pos.mpr p.1.property.2)
    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM p.1 (hmem p.1))]
  have h := gradient_convolution_sq (Real.sqrt (t - p.1)) (hapos p)
    (fun y => f (p.1, y)) p.2
  rw [Real.sq_sqrt (sub_pos.mpr p.1.property.2).le] at h
  exact h.symm

/-- The gradient time majorant is integrable through the endpoint. -/
theorem intervalIntegrable_gradient_majorant (t A : ℝ) :
    IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
  convert intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A using 1
  norm_num

/-- The actual first spatial derivative is integrable in Duhamel time. -/
theorem intervalIntegrable_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    IntervalIntegrable
      (fun s : ℝ => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) volume 0 t := by
  have hc := (continuous_gradient_heatSolution_time ht hf hM).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Ioo (0 : ℝ) t => x)))
  let A := M * (∫ y : E, ‖Grad 1 y‖)
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
    (intervalIntegrable_gradient_majorant t A)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
  refine hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have hmem : (s : ℝ) ∈ Icc 0 T := ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
  have hfc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hmem, mem_univ y⟩)
  exact norm_gradient_heatSolution_le (sub_pos.mpr s.property.2)
    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hmem) x


/-- The heat kernel is jointly continuous away from zero time. -/
theorem continuous_kernel_pos :
    Continuous (fun p : Ioi (0 : ℝ) × E => heatKernel (p.1 : ℝ) p.2) := by
  have ht (p : Ioi (0 : ℝ) × E) : 0 < (p.1 : ℝ) := p.1.property
  unfold heatKernel
  apply Continuous.mul
  · apply Continuous.rpow_const (by fun_prop)
    intro p
    left
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ht p).ne'
  · apply Continuous.rexp
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro p
    exact mul_ne_zero (by norm_num) (ht p).ne'

/-- Bounded cylinder data give a genuine time integral for the heat evolution. -/
theorem intervalIntegrable_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    IntervalIntegrable
      (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x) volume 0 t := by
  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hfc : Continuous (fun p : Ioo (0 : ℝ) t × E => f (p.1, x - p.2)) :=
    hf.comp_continuous (hs.prodMk (continuous_const.sub continuous_snd))
      (fun p => ⟨hmem p.1, mem_univ _⟩)
  have hk : Continuous (fun p : Ioo (0 : ℝ) t × E => heatKernel (t - p.1) p.2) :=
    continuous_kernel_pos.comp
      (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
        continuous_snd)
  have hm := (hk.mul hfc).stronglyMeasurable.integral_prod_right' (ν := volume)
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 t)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
  refine hi.mono' (by simpa only [heatSolution_apply] using hm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s => ?_)
  have hpos := sub_pos.mpr s.property.2
  dsimp only [Function.comp_apply]
  rw [heatSolution_apply]
  calc
    ‖∫ y : E, heatKernel (t - s) y * f (s, x - y)‖ ≤
        ∫ y : E, M * heatKernel (t - s) y := by
      apply norm_integral_le_of_norm_le ((heatKernel_integrable («E» := E) hpos).const_mul M)
      refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hpos y), mul_comm]
      exact mul_le_mul_of_nonneg_right (hM s (hmem s) _) (heatKernel_nonneg hpos y)
    _ = M := by rw [integral_const_mul, integral_heatKernel_eq_one hpos, mul_one]

/-- First spatial differentiation under the Duhamel time integral. -/
theorem hasFDerivAt_duhamel {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    HasFDerivAt (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)
      (∫ s in (0 : ℝ)..t, fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) x := by
  let A := M * (∫ y : E, ‖Grad 1 y‖)
  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
    ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hfc (s : ℝ) (hs : s ∈ Ioo 0 t) : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hmem s hs, mem_univ y⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F' := fun z s => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) z)
    (s := univ) (bound := fun s => A * (t - s) ^ (-(1 / 2 : ℝ))) (by simp)
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [uIoc_of_le ht.1] using
        (intervalIntegrable_heatSolution_time ht hf hM z).aestronglyMeasurable
  · exact intervalIntegrable_heatSolution_time ht hf hM x
  · simpa only [uIoc_of_le ht.1] using
      (intervalIntegrable_gradient_heatSolution_time ht hf hM x).aestronglyMeasurable
  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z
  · exact intervalIntegrable_gradient_majorant t A
  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact (heatSolution_hasFDerivAt (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z).differentiableAt.hasFDerivAt

/-- Second spatial differentiation uses the integrable cancelled Hessian. -/
theorem hasFDerivAt_duhamel_gradient {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    HasFDerivAt (fun z : E => ∫ s in (0 : ℝ)..t,
      fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) z)
      (∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) x := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
    ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hfc (s : ℝ) (hs : s ∈ Ioo 0 t) : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hmem s hs, mem_univ y⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F' := fun z s => ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)
    (s := univ) (bound := fun s => A * (t - s) ^ (α / 2 - 1)) (by simp)
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [uIoc_of_le ht.1] using
        (intervalIntegrable_gradient_heatSolution_time ht hf hM z).aestronglyMeasurable
  · exact intervalIntegrable_gradient_heatSolution_time ht hf hM x
  · have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x)
    simpa only [uIoc_of_le ht.1] using hi.aestronglyMeasurable
  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
      (sub_pos.mpr hs.2) (hK s (hmem s hs)) z
  · exact intervalIntegrable_hessian_majorant hα t A
  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by
      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
    have htwo := contDiff_two_heatSolution_of_bounded_measurable
      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs
    have hd := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) z).hasFDerivAt
    rw [hessian_heatSolution_eq_cancelled_integral
      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs z] at hd
    exact hd

/-- The cancelled time-integrated Hessian is continuous in the observation point. -/
theorem continuous_duhamel_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
    Continuous (fun x : E => ∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
    ⟨hs.1.le, hs.2.le.trans ht.2⟩
  simp_rw [intervalIntegral.integral_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
  apply continuous_of_dominated (bound := fun s : ℝ => A * (t - s) ^ (α / 2 - 1))
  · intro x
    exact (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
      (sub_pos.mpr hs.2) (hK s (hmem s hs)) x
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
      (intervalIntegrable_hessian_majorant hα t A)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hfc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hmem s hs, mem_univ y⟩)
    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by
      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
    have htwo := contDiff_two_heatSolution_of_bounded_measurable
      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs
    have hc := ((htwo.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous
    exact hc.congr (fun x => hessian_heatSolution_eq_cancelled_integral
      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs x)

/-- The actual second derivative equals the cancelled double integral. -/
theorem hessian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y := by
  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
  rw [hD]
  exact (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK x).fderiv

/-- Spatial C² regularity of the Duhamel formula under the frozen forcing hypotheses. -/
theorem contDiff_two_duhamel {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z) := by
  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
  have hDD := funext (fun z => (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z).fderiv)
  change ContDiff ℝ (1 + 1) _
  refine contDiff_succ_iff_fderiv.mpr
    ⟨fun z => (hasFDerivAt_duhamel ht hf hM z).differentiableAt, by norm_num, ?_⟩
  rw [hD]
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun z => (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z).differentiableAt, ?_⟩
  rw [hDD]
  exact continuous_duhamel_hessian hα hα1 ht hf hM hK

/-- The frozen spatial Hölder Duhamel Hessian estimate. -/
theorem duhamel_hessian_bound :
  (∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  (∀ x, u 0 x = 0) ∧
  ∀ t ∈ Icc 0 T, ∀ x : E,
    ContDiff ℝ 2 (u t) ∧
    IntegrableOn (fun s : ℝ => ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y) (Ioo 0 t) ∧
    fderiv ℝ (fderiv ℝ (u t)) x =
      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y ∧
    ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2)) := by
  intro α hα hα1
  let J := ∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α
  refine ⟨max 1 (J * (2 / α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro T _ _ f M K _ hK0 hf hM hK
  dsimp only
  refine ⟨?_, ?_⟩
  · intro x
    exact intervalIntegral.integral_same
  · intro t ht x
    refine ⟨contDiff_two_duhamel hα hα1 ht hf hM hK,
      integrableOn_cancelled_hessian_time hα hα1 ht hf hK x,
      hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, ?_⟩
    rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x]
    calc
      ‖∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
          (K * J) * (2 / α) * t ^ (α / 2) :=
        norm_integral_cancelled_hessian_time_le hα hα1 ht.1
          (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x
      _ = (J * (2 / α)) * K * t ^ (α / 2) := by ring
      _ ≤ max 1 (J * (2 / α)) * K * t ^ (α / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hK0)
          (Real.rpow_nonneg ht.1 _)

end Poincare.HeatDuhamelHessianDifferentiation

end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology InnerProductSpace Interval

namespace Poincare.HeatDuhamelHessianSpatialHolder

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
local notation "Third" => fun (t : ℝ) (x : E) => fderiv ℝ (Hess t) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The third derivative of the Gaussian, evaluated in three directions. -/
theorem third_apply {t : ℝ} (ht : t ≠ 0) (x u v w : E) :
    Third t x u v w = heatKernel t x *
      (-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / (8 * t ^ 3) +
        (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ +
          ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / (4 * t ^ 2)) := by
  have hH : ContDiff ℝ 1 (Hess t) :=
    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hd := (((hH.differentiable (by norm_num) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x))
  have he : (fun z : E => Hess t z v w) = fun z : E => heatKernel t z *
      (⟪v, z⟫_ℝ * ⟪w, z⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
    funext z
    simpa only [iteratedFDeriv_two_apply, real_inner_comm] using
      iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht z v w
  have hv := (innerSL ℝ v).hasFDerivAt (x := x)
  have hw := (innerSL ℝ w).hasFDerivAt (x := x)
  have hp := (hasFDerivAt_heatKernel_spatial («E» := E) ht x).mul
    (((hv.mul hw).mul_const ((4 * t ^ 2)⁻¹)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
  rw [he] at hd
  simp only [Pi.mul_apply, innerSL_apply_apply, div_eq_mul_inv] at hp hd
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, smul_eq_mul,
    innerSL_apply_apply] at h
  rw [h]
  simp only [heatKernel, real_inner_comm]
  ring_nf

/-- The unit-time third derivative has a cubic Gaussian envelope. -/
theorem norm_third_one_le (x : E) :
    ‖Third 1 x‖ ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by
  have hk : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
  have hB : 0 ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg u))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [third_apply one_ne_zero]
  norm_num only [one_pow, mul_one]
  rw [norm_mul, Real.norm_of_nonneg hk]
  calc
    _ ≤ heatKernel 1 x *
        (‖⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ‖ / 8 +
          ((‖⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ‖ + ‖⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ‖) +
            ‖⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ‖) / 4) := by
      gcongr
      calc
        _ ≤ ‖-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / 8‖ +
            ‖(⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ +
              ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / 4‖ := norm_add_le _ _
        _ ≤ _ := by
          simp only [norm_div, norm_neg, Real.norm_ofNat]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ heatKernel 1 x *
        (((‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) / 8 +
          (((‖u‖ * ‖v‖) * (‖x‖ * ‖w‖) + (‖x‖ * ‖v‖) * (‖u‖ * ‖w‖)) +
            (‖x‖ * ‖u‖) * (‖v‖ * ‖w‖)) / 4) := by
      simp only [norm_mul]
      gcongr <;> apply norm_inner_le_norm
    _ = _ := by ring

/-- The weighted third derivative is integrable at unit time. -/
theorem integrable_weighted_third_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    Integrable (fun x : E => ‖Third 1 x‖ * ‖x‖ ^ α) := by
  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hweight : Continuous (fun x : E => ‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))) :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ α + 1)).comp continuous_norm).mul
      (((continuous_norm.pow 2).div_const 8).neg.rexp)
  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
      («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
      hweight.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => show
        ‖‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
          rw [Real.norm_of_nonneg (by positivity)]
          exact rpow_mul_gaussian_le_eight (by linarith) (by linarith) (norm_nonneg x))
  have hcont : ContDiff ℝ 0 (Third 1) :=
    (((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)
  refine (hbound.const_mul c).mono'
    (hcont.continuous.norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  have hK : heatKernel (1 : ℝ) x =
      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
    rw [← Real.exp_add]
    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
      Nat.cast_ofNat, mul_one]
    congr 1
    congr 1
    ring
  have hw : ‖x‖ ^ (α + 1) = ‖x‖ ^ α * ‖x‖ :=
    Real.rpow_add_one' (norm_nonneg x) (by linarith)
  calc
    ‖Third 1 x‖ * ‖x‖ ^ α ≤
        (heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)) * ‖x‖ ^ α :=
      mul_le_mul_of_nonneg_right (norm_third_one_le x) (Real.rpow_nonneg (norm_nonneg x) α)
    _ ≤ (heatKernel 1 x * (‖x‖ * (1 + ‖x‖ ^ 2))) * ‖x‖ ^ α := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg x) 3]
    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
        (‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK, hw]; ring

/-- Parabolic dilation of the full third spatial derivative. -/
theorem third_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    Third (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹) • Third 1 x := by
  ext u v w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [third_apply (pow_ne_zero _ ha.ne'), third_apply one_ne_zero,
    heatKernel_sq_smul a ha x]
  simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
  field_simp

/-- Pointwise parabolic dilation including the radial weight. -/
theorem weighted_third_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
    ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
      ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (‖Third 1 x‖ * ‖x‖ ^ α) := by
  rw [third_sq_smul a ha x,
    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 3)⁻¹ by positivity) (Third 1 x),
    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
  ring

/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
theorem weighted_third_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
    (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
      ((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => ‖Third (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
  calc
    (a ^ 3)⁻¹ * (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
        ∫ x : E, ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
    _ = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
      simp_rw [weighted_third_sq_smul a ha]
      rw [integral_const_mul]
    _ = (a ^ 3)⁻¹ * (((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α)) := by ring

/-- Weighted Bochner integrability at every positive time. -/
theorem integrable_weighted_third {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) := by
  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [← Real.sq_sqrt ht.le]
  apply (integrable_comp_smul_iff volume _ ha.ne').1
  simp_rw [weighted_third_sq_smul (Real.sqrt t) ha]
  exact (integrable_weighted_third_one hα hα1).const_mul _

/-- Exact scaling of the third spatial derivative moment. -/
theorem weighted_third_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
    (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) =
      t ^ (α / 2 - 3 / 2) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
  have h := weighted_third_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
  rw [Real.sq_sqrt ht.le] at h
  rw [h]
  congr 1
  have hp : (Real.sqrt t) ^ 3 = t ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
    congr 1
    norm_num
  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht]
  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
  ring

/-- The third Gaussian moment has a positive constant independent of time. -/
theorem third_moment_bound :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) ∧
      (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 3 / 2) := by
  intro α hα hα1
  refine ⟨max 1 (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  refine ⟨integrable_weighted_third hα.le hα1.le ht, ?_⟩
  rw [weighted_third_integral ht, mul_comm (t ^ (α / 2 - 3 / 2))]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

/-- The near-time cancelled integral is bounded by the length of its time interval. -/
theorem norm_integral_cancelled_hessian_near_le {α K a t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hat : a ≤ t) {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * (t - a) ^ (α / 2) := by
  have hb := norm_integral_cancelled_hessian_time_le hα hα1 (sub_nonneg.mpr hat)
    (f := fun p => f (p.1 + a, p.2))
    (fun s hs => hK (s + a) ⟨by linarith [hs.1], by linarith [hs.2]⟩) x
  have he := intervalIntegral.integral_comp_add_right
    (a := (0 : ℝ)) (b := t - a)
    (fun s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) a
  simp only [zero_add, sub_add_cancel] at he
  have htau (s : ℝ) : t - a - s = t - (s + a) := by ring
  simp only [htau] at hb
  rw [he] at hb
  exact hb

/-- The near part of the spatial increment has the required Hölder power. -/
theorem near_hessian_difference_le {α K a t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hat : a ≤ t)
    {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hscale : t - a ≤ ‖x - z‖ ^ 2) :
    ‖(∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
      (∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
  let J := ∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α
  have hJ : 0 ≤ J := integral_nonneg (fun y => by positivity)
  have hp : (t - a) ^ (α / 2) ≤ ‖x - z‖ ^ α := by
    calc
      (t - a) ^ (α / 2) ≤ (‖x - z‖ ^ 2) ^ (α / 2) :=
        Real.rpow_le_rpow (sub_nonneg.mpr hat) hscale (by linarith)
      _ = ‖x - z‖ ^ α := by
        rw [← Real.rpow_natCast_mul (norm_nonneg (x - z))]
        congr 1
        norm_num
        ring
  calc
    _ ≤ ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ +
        ‖∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y‖ :=
      norm_sub_le _ _
    _ ≤ (K * J) * (2 / α) * (t - a) ^ (α / 2) +
        (K * J) * (2 / α) * (t - a) ^ (α / 2) :=
      add_le_add (norm_integral_cancelled_hessian_near_le hα hα1 hat hK x)
        (norm_integral_cancelled_hessian_near_le hα hα1 hat hK z)
    _ = (2 * J * (2 / α)) * K * (t - a) ^ (α / 2) := by ring
    _ ≤ (2 * J * (2 / α)) * K * ‖x - z‖ ^ α :=
      mul_le_mul_of_nonneg_left hp
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hJ)
          (div_nonneg (by norm_num) hα.le)) hK0)

/-- The spatial Hölder estimate for the actual Duhamel Hessian when the near interval is all of time. -/
theorem duhamel_hessian_spatial_holder_of_time_le_dist_sq {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hscale : t ≤ ‖x - z‖ ^ 2) :
    let u : E → ℝ := fun x => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) x
    ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
  dsimp only
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
  exact near_hessian_difference_le hα hα1 hK0 ht.1
    (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x z (by simpa using hscale)

/-- The far-time power integral supplies the factor two over one minus the exponent. -/
theorem far_time_power_integral_le {α ρ t : ℝ}
    (hα1 : α < 1) (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ t) :
    ρ * (∫ s in (0 : ℝ)..(t - ρ ^ 2), (t - s) ^ (α / 2 - 3 / 2)) ≤
      (2 / (1 - α)) * ρ ^ α := by
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hq : α / 2 - 3 / 2 + 1 < 0 := by linarith
  rw [intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => r ^ (α / 2 - 3 / 2)) t, sub_sub_cancel, sub_zero]
  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
  · calc
      ρ * ((t ^ (α / 2 - 3 / 2 + 1) - (ρ ^ 2) ^ (α / 2 - 3 / 2 + 1)) /
          (α / 2 - 3 / 2 + 1)) ≤
          ρ * (-(ρ ^ 2) ^ (α / 2 - 3 / 2 + 1) / (α / 2 - 3 / 2 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hρ.le
        simp only [div_eq_mul_inv]
        apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
        have hnn := Real.rpow_nonneg (hρ2.le.trans ht) (α / 2 - 3 / 2 + 1)
        simp only [div_eq_mul_inv] at hnn
        linarith only [hnn]
      _ = (2 / (1 - α)) * ρ ^ α := by
        rw [← Real.rpow_natCast_mul hρ.le]
        simp only [Nat.cast_ofNat]
        rw [show (2 : ℝ) * (α / 2 - 3 / 2 + 1) = α - 1 by ring]
        rw [Real.rpow_sub hρ, Real.rpow_one]
        have hden : 1 - α ≠ 0 := by linarith
        have hden' : α / 2 - 3 / 2 + 1 ≠ 0 := hq.ne
        field_simp [hρ.ne', hden, hden', show -1 + α ≠ 0 by linarith]
        ring_nf
        all_goals
          have hi := mul_inv_cancel₀ (show -1 + α ≠ 0 by linarith)
          nlinarith only [hi]
  · rw [uIcc_of_le ht]
    intro hz
    exact (not_le.mpr hρ2) hz.1

/-- Both observation points can use the same cancellation constant. -/
theorem hessian_heatSolution_eq_common_cancelled_integral {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
    fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
      ∫ y : E, (f (x - y) - f x) • Hess t (y + (z - x)) := by
  have hi : Integrable (fun y : E => f y • Hess t (z - y)) :=
    integrable_data_smul_hessian_sub ht hf hM z
  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
    ((integrable_hessian ht).comp_sub_left z).smul (f x)
  have hz : (∫ y : E, Hess t (z - y)) = 0 := by
    rw [integral_sub_left_eq_self, integral_hessian_eq_zero ht]
  have he : (∫ y : E, (f y - f x) • Hess t (z - y)) =
      fderiv ℝ (fderiv ℝ (heatSolution t f)) z := by
    simp_rw [sub_smul]
    rw [integral_sub hi hc, integral_smul, hz, smul_zero, sub_zero,
      hessian_heatSolution_eq_integral ht hf hM]
  rw [← he]
  have hchange := integral_sub_left_eq_self
    (fun y : E => (f y - f x) • Hess t (z - y)) volume x
  have halg (y : E) : z - (x - y) = y + (z - x) := by abel
  simpa only [halg] using hchange.symm

/-- The Hessian increment is the cancelled integral of a kernel translation difference. -/
theorem hessian_heatSolution_difference_eq_integral {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
    fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
      fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
      ∫ y : E, (f (x - y) - f x) • (Hess t y - Hess t (y + (z - x))) := by
  have hi := integrable_data_smul_hessian_sub ht hf hM z
  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
    ((integrable_hessian ht).comp_sub_left z).smul (f x)
  have hij : Integrable (fun y : E => (f (x - y) - f x) • Hess t (y + (z - x))) := by
    have h := (hi.sub hc).comp_sub_left x
    have halg (y : E) : z - (x - y) = y + (z - x) := by abel
    simpa only [Pi.sub_apply, halg, ← sub_smul] using h
  rw [hessian_heatSolution_eq_cancelled_integral ht hf hM x,
    hessian_heatSolution_eq_common_cancelled_integral ht hf hM x z]
  simp_rw [smul_sub]
  rw [integral_sub (integrable_cancelled_hessian ht hf hM x) hij]

/-- A translated Hessian difference is bounded by the third derivative along its segment. -/
theorem norm_hessian_translation_le (t : ℝ) (y w : E) :
    ‖Hess t (y + w) - Hess t y‖ ≤
      ∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖ := by
  have hH : ContDiff ℝ 1 (Hess t) :=
    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hD : Continuous (Third t) := (hH.fderiv_right (m := 0) (by norm_num)).continuous
  have hline (r : ℝ) : HasDerivAt (fun q : ℝ => y + q • w) w r := by
    simpa only [one_smul] using ((hasDerivAt_id r).smul_const w).const_add y
  have hd (r : ℝ) : HasDerivAt (fun q : ℝ => Hess t (y + q • w))
      (Third t (y + r • w) w) r :=
    ((hH.differentiable (by norm_num) (y + r • w)).hasFDerivAt).comp_hasDerivAt r (hline r)
  have hbound : Continuous (fun r : ℝ => ‖Third t (y + r • w)‖ * ‖w‖) :=
    (hD.comp (continuous_const.add (continuous_id.smul continuous_const))).norm.mul continuous_const
  have hi : IntervalIntegrable (fun r : ℝ => Third t (y + r • w) w) volume 0 1 :=
    ((hD.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun r _ => hd r) hi
  simp only [one_smul, zero_smul, add_zero] at he
  rw [← he]
  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall fun r _ => ContinuousLinearMap.le_opNorm _ _)
    (hbound.intervalIntegrable 0 1)

/-- Translating the third derivative costs one unweighted moment in addition to its weighted moment. -/
theorem weighted_third_translation {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (ht : 0 < t) (w : E) :
    Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) ∧
    (∫ y : E, ‖Third t (y + w)‖ * ‖y‖ ^ α) ≤
      (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖) := by
  have hiα := (integrable_weighted_third hα hα1 ht).comp_add_right w
  have hi0 : Integrable (fun y : E => ‖Third t y‖) := by
    simpa using integrable_weighted_third (α := 0) (by norm_num) (by norm_num) ht
  have hiw := (hi0.comp_add_right w).const_mul (‖w‖ ^ α)
  have hmajor := hiα.add hiw
  have hb (y : E) : ‖Third t (y + w)‖ * ‖y‖ ^ α ≤
      ‖Third t (y + w)‖ * ‖y + w‖ ^ α + ‖w‖ ^ α * ‖Third t (y + w)‖ := by
    have hnorm : ‖y‖ ≤ ‖y + w‖ + ‖w‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (y + w) w
    have hp : ‖y‖ ^ α ≤ ‖y + w‖ ^ α + ‖w‖ ^ α :=
      (Real.rpow_le_rpow (norm_nonneg y) hnorm hα).trans
        (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hα hα1)
    calc
      _ ≤ ‖Third t (y + w)‖ * (‖y + w‖ ^ α + ‖w‖ ^ α) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = _ := by ring
  have hD : Continuous (Third t) :=
    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuous
  have hi : Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) :=
    hmajor.mono' ((hD.comp (continuous_id.add continuous_const)).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
        exact hb y)
  refine ⟨hi, (integral_mono hi hmajor hb).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add hiα hiw, integral_const_mul,
    integral_add_right_eq_self (fun y : E => ‖Third t y‖ * ‖y‖ ^ α) w,
    integral_add_right_eq_self (fun y : E => ‖Third t y‖) w]

/-- The segment parameter and the weighted spatial third derivative form an integrable product. -/
theorem integrable_segment_weighted_third {α t : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
    Integrable (fun p : ℝ × E => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
  have hD : Continuous (Third t) :=
    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuous
  have hg : Continuous G :=
    (hD.comp (continuous_snd.add (continuous_fst.smul continuous_const))).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_snd.norm)
  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall fun r => (weighted_third_translation hα hα1 ht (r • w)).1, ?_⟩
  have hm := hg.norm.stronglyMeasurable.integral_prod_right' (ν := volume)
  refine (integrable_const C).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have he : (∫ y : E, ‖G (r, y)‖) = ∫ y : E, G (r, y) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
  have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
    rw [norm_smul_of_nonneg hr.1]
    nlinarith [norm_nonneg w, hr.2]
  exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
      (integral_nonneg (fun y => norm_nonneg _))))

/-- Integrating the segment estimate gives a weighted translation estimate for the Hessian. -/
theorem weighted_hessian_translation {α t : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
    Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ∧
    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
      ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := by
  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
  have hg : Integrable G ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
    integrable_segment_weighted_third hα hα1 ht w
  have hiMajor := hg.integral_prod_right.const_mul ‖w‖
  have hb (y : E) : ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α ≤
      ‖w‖ * (∫ r in Icc (0 : ℝ) 1, G (r, y)) := by
    calc
      _ ≤ (∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖) * ‖y‖ ^ α :=
        mul_le_mul_of_nonneg_right (norm_hessian_translation_le t y w)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by
        change _ = ‖w‖ * (∫ r in Icc (0 : ℝ) 1, ‖Third t (y + r • w)‖ * ‖y‖ ^ α)
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
        ring
  have hH : Continuous (Hess t) :=
    (((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hi : Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) :=
    hiMajor.mono' (((hH.comp (continuous_id.add continuous_const)).sub hH).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
        exact hb y)
  refine ⟨hi, (integral_mono hi hiMajor hb).trans ?_⟩
  rw [integral_const_mul]
  have hswap : (∫ y : E, ∫ r in Icc (0 : ℝ) 1, G (r, y)) =
      ∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y) :=
    (integral_integral_swap hg).symm
  rw [hswap]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
  calc
    (∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y)) ≤ ∫ _r in Icc (0 : ℝ) 1, C := by
      apply integral_mono_ae hg.integral_prod_left (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
        apply Real.rpow_le_rpow (norm_nonneg _) _ hα
        rw [norm_smul_of_nonneg hr.1]
        nlinarith [norm_nonneg w, hr.2]
      exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
          (integral_nonneg (fun y => norm_nonneg _))))
    _ = C := by simp

/-- Beyond the spatial time scale, both translation terms have the same time power. -/
theorem weighted_hessian_translation_far {α t : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) (hw : ‖w‖ ^ 2 ≤ t) :
    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
      ‖w‖ * t ^ (α / 2 - 3 / 2) *
        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) := by
  have hp : ‖w‖ ^ α ≤ t ^ (α / 2) := by
    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (show 0 ≤ α / 2 by linarith)
    rw [← Real.rpow_natCast_mul (norm_nonneg w)] at h
    have he : (2 : ℝ) * (α / 2) = α := by ring
    simpa only [Nat.cast_ofNat, he] using h
  have hzero : (∫ y : E, ‖Third t y‖) =
      t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖) := by
    simpa using weighted_third_integral ht 0
  have hJ : 0 ≤ ∫ y : E, ‖Third 1 y‖ := integral_nonneg (fun y => norm_nonneg _)
  calc
    _ ≤ ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) +
        ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := (weighted_hessian_translation hα hα1 ht w).2
    _ = ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
        ‖w‖ ^ α * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
      rw [weighted_third_integral ht, hzero]
    _ ≤ ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
        t ^ (α / 2) * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hp
        (mul_nonneg (Real.rpow_nonneg ht.le _) hJ))
    _ = _ := by
      rw [← mul_assoc (t ^ (α / 2)), ← Real.rpow_add ht]
      rw [show α / 2 + -(3 / 2 : ℝ) = α / 2 - 3 / 2 by ring]
      ring

/-- The far-time spatial heat Hessian increment is linear in the observation distance. -/
theorem norm_heat_hessian_difference_far_le {α t M K : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (hK0 : 0 ≤ K)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (hM : ∀ y, ‖f y‖ ≤ M)
    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hscale : ‖x - z‖ ^ 2 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
      fderiv ℝ (fderiv ℝ (heatSolution t f)) z‖ ≤
      ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
        K * ‖x - z‖ * t ^ (α / 2 - 3 / 2) := by
  rw [hessian_heatSolution_difference_eq_integral ht hf hM x z]
  have hi := (weighted_hessian_translation hα hα1 ht (z - x)).1.const_mul K
  have hb (y : E) : ‖(f (x - y) - f x) • (Hess t y - Hess t (y + (z - x)))‖ ≤
      K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := by
    have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
      have he : x - y - x = -y := by abel
      simpa only [he, norm_neg, Real.norm_eq_abs] using hK (x - y) x
    calc
      _ ≤ ‖f (x - y) - f x‖ * ‖Hess t y - Hess t (y + (z - x))‖ :=
        norm_real_smul_continuousLinearMap_two_le _ _
      _ ≤ (K * ‖y‖ ^ α) * ‖Hess t y - Hess t (y + (z - x))‖ :=
        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev (Hess t y)]; ring
  calc
    _ ≤ ∫ y : E, K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
    _ = K * (∫ y : E, ‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := integral_const_mul _ _
    _ ≤ K * (‖z - x‖ * t ^ (α / 2 - 3 / 2) *
        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖))) :=
      mul_le_mul_of_nonneg_left (weighted_hessian_translation_far hα hα1 ht (z - x)
        (by simpa only [norm_sub_rev z x] using hscale)) hK0
    _ = _ := by rw [norm_sub_rev z x]; ring

/-- The far part of the cancelled Duhamel Hessian has the spatial Hölder bound. -/
theorem far_hessian_difference_le {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hρ : 0 < ‖x - z‖) (hscale : ‖x - z‖ ^ 2 < t) :
    ‖(∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
        (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
      (∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
        (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
      (((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
        (2 / (1 - α))) * K * ‖x - z‖ ^ α := by
  let a := t - ‖x - z‖ ^ 2
  let J := (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)
  let F := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
  have ha : 0 < a := sub_pos.mpr hscale
  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
  have hρ2 : 0 < ‖x - z‖ ^ 2 := sq_pos_of_pos hρ
  have hJ : 0 ≤ J := add_nonneg
    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (integral_nonneg (fun y => norm_nonneg _))
  have hFi (p : E) : IntervalIntegrable (fun s => F s p) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
        (Ioo_subset_Ioo le_rfl hat))
  have hip : IntervalIntegrable (fun r : ℝ => r ^ (α / 2 - 3 / 2)) volume (‖x - z‖ ^ 2) t := by
    apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
    rw [uIcc_of_le hscale.le]
    intro hz
    exact (not_le.mpr hρ2) hz.1
  have hiB : IntervalIntegrable
      (fun s : ℝ => J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2)) volume 0 a := by
    have h := (hip.comp_sub_left t).symm
    simp only [sub_self] at h
    exact h.const_mul (J * K * ‖x - z‖)
  have hbound : ‖∫ s in (0 : ℝ)..a, F s x - F s z‖ ≤
      ∫ s in (0 : ℝ)..a, J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ha.le _ hiB
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, (hs.2.trans hat).trans ht.2⟩
    have hsτ : ‖x - z‖ ^ 2 ≤ t - s := by dsimp [a] at hs; linarith [hs.2]
    have hτ : 0 < t - s := hρ2.trans_le hsτ
    have hfc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM s hsT
    dsimp only [F]
    rw [← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs x,
      ← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs z]
    exact norm_heat_hessian_difference_far_le hα.le hα1.le hτ hK0
      hfc.aestronglyMeasurable hMs (hK s hsT) x z hsτ
  change ‖(∫ s in (0 : ℝ)..a, F s x) - (∫ s in (0 : ℝ)..a, F s z)‖ ≤ _
  rw [← intervalIntegral.integral_sub (hFi x) (hFi z)]
  refine hbound.trans ?_
  rw [intervalIntegral.integral_const_mul]
  calc
    (J * K * ‖x - z‖) * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2)) =
        (J * K) * (‖x - z‖ * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2))) := by ring
    _ ≤ (J * K) * ((2 / (1 - α)) * ‖x - z‖ ^ α) :=
      mul_le_mul_of_nonneg_left (far_time_power_integral_le hα1 hρ hscale.le) (mul_nonneg hJ hK0)
    _ = _ := by ring

/-- The spatial Hölder estimate for the actual Duhamel Hessian. -/
theorem duhamel_hessian_spatial_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t ∈ Icc 0 T, ∀ x z : E,
    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α := by
  intro α hα hα1
  let N := 2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
  let F := ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) * (2 / (1 - α))
  have hN : 0 ≤ N := mul_nonneg
    (mul_nonneg (by norm_num) (integral_nonneg (fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))))
    (div_nonneg (by norm_num) hα.le)
  have hF : 0 ≤ F := mul_nonneg
    (add_nonneg (integral_nonneg (fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
      (integral_nonneg (fun y => norm_nonneg _)))
    (div_nonneg (by norm_num) (by linarith))
  refine ⟨max 1 (N + F), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro T _ _ f M K _ hK0 hf hM hK
  dsimp only
  intro t ht x z
  have hC : N + F ≤ max 1 (N + F) := le_max_right _ _
  have hpow : 0 ≤ ‖x - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  suffices hraw : ‖fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) x)) x -
      fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) x)) z‖ ≤ (N + F) * K * ‖x - z‖ ^ α by
    exact hraw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hK0) hpow)
  by_cases he : x = z
  · subst z
    simp [Real.zero_rpow hα.ne']
  have hρ : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  by_cases htime : t ≤ ‖x - z‖ ^ 2
  · exact (duhamel_hessian_spatial_holder_of_time_le_dist_sq hα hα1 ht hK0 hf hM hK x z htime).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show N ≤ N + F by linarith) hK0) hpow)
  have hscale : ‖x - z‖ ^ 2 < t := lt_of_not_ge htime
  let a := t - ‖x - z‖ ^ 2
  let H := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
  have ha : 0 < a := sub_pos.mpr hscale
  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
  have h0t (p : E) : IntervalIntegrable (fun s => H s p) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK p)
  have h0a (p : E) : IntervalIntegrable (fun s => H s p) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
        (Ioo_subset_Ioo le_rfl hat))
  have hsplit (p : E) : (∫ s in (0 : ℝ)..t, H s p) =
      (∫ s in (0 : ℝ)..a, H s p) + (∫ s in a..t, H s p) :=
    (intervalIntegral.integral_add_adjacent_intervals (h0a p) ((h0a p).symm.trans (h0t p))).symm
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
  change ‖(∫ s in (0 : ℝ)..t, H s x) - (∫ s in (0 : ℝ)..t, H s z)‖ ≤ _
  rw [hsplit x, hsplit z]
  have hnear : ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ ≤ N * K * ‖x - z‖ ^ α := by
    apply near_hessian_difference_le hα hα1 hK0 hat
    · intro s hs
      exact hK s ⟨ha.le.trans hs.1.le, hs.2.le.trans ht.2⟩
    · dsimp only [a]
      linarith
  have hfar : ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ ≤ F * K * ‖x - z‖ ^ α :=
    far_hessian_difference_le hα hα1 ht hK0 hf hM hK x z hρ hscale
  calc
    _ = ‖((∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)) +
        ((∫ s in a..t, H s x) - (∫ s in a..t, H s z))‖ := by congr 1; abel
    _ ≤ ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ +
        ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ := norm_add_le _ _
    _ ≤ F * K * ‖x - z‖ ^ α + N * K * ‖x - z‖ ^ α := add_le_add hfar hnear
    _ = (N + F) * K * ‖x - z‖ ^ α := by ring

end Poincare.HeatDuhamelHessianSpatialHolder

end
end

section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory
open scoped Topology InnerProductSpace Interval
namespace Poincare.HeatDuhamelHessianTimeHolder
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation HeatDuhamelHessianSpatialHolder

/-- The Euclidean inner product as a real bilinear operator. -/
def euclideanForm : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

/-- The Gaussian Hessian as a linear combination of two fixed bilinear forms. -/
theorem hessian_eq_tensor {t : ℝ} (ht : t ≠ 0) (x : E) :
    Hess t x = (heatKernel t x / (4 * t ^ 2)) •
        (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)) -
      (heatKernel t x / (2 * t)) • euclideanForm := by
  ext v w
  have h := iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht x v w
  simp [iteratedFDeriv_two_apply] at h
  rw [h]
  change heatKernel t x * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) =
    (heatKernel t x / (4 * t ^ 2)) * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) -
      (heatKernel t x / (2 * t)) * ⟪v, w⟫_ℝ
  ring


/-- The time derivative of the full Gaussian Hessian. -/
theorem hasDerivAt_hessian_time {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun r : ℝ => Hess r x)
      ((heatKernel t x * (‖x‖ ^ 2 / (16 * t ^ 4) - 7 / (8 * t ^ 3))) •
          (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)) -
        (heatKernel t x * (‖x‖ ^ 2 / (8 * t ^ 3) - 5 / (4 * t ^ 2))) • euclideanForm) t := by
  have hk : HasDerivAt (fun r : ℝ => heatKernel r x)
      (heatKernel t x * (‖x‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t))) t := by
    have h := (hasDerivAt_heatKernel_time ht x)
    rw [← h.deriv, deriv_heatKernel_time_eq_heatKernel_mul ht x] at h
    simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, Nat.cast_ofNat] using h
  have ha := hk.div (((hasDerivAt_id t).pow 2).const_mul 4)
    (show 4 * t ^ 2 ≠ 0 by positivity)
  have hb := hk.div ((hasDerivAt_id t).const_mul 2)
    (show 2 * t ≠ 0 by positivity)
  have ha' : HasDerivAt (fun r : ℝ => heatKernel r x / (4 * r ^ 2))
      (heatKernel t x * (‖x‖ ^ 2 / (16 * t ^ 4) - 7 / (8 * t ^ 3))) t := by
    convert ha using 1
    dsimp
    field_simp
    ring
  have hb' : HasDerivAt (fun r : ℝ => heatKernel r x / (2 * r))
      (heatKernel t x * (‖x‖ ^ 2 / (8 * t ^ 3) - 5 / (4 * t ^ 2))) t := by
    convert hb using 1
    dsimp
    field_simp
    ring
  apply ((ha'.smul_const (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x))).sub
    (hb'.smul_const euclideanForm)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  exact hessian_eq_tensor hr.ne' x


local notation "DtHess" => fun (t : ℝ) (x : E) => deriv (fun r : ℝ => Hess r x) t

/-- A quartic Gaussian envelope for the time derivative at unit time. -/
theorem norm_hessian_time_deriv_one_le (x : E) :
    ‖DtHess 1 x‖ ≤ heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2) := by
  change ‖deriv (fun r : ℝ => Hess r x) 1‖ ≤ _
  rw [(hasDerivAt_hessian_time zero_lt_one x).deriv]
  have hI : ‖euclideanForm‖ ≤ 1 := norm_innerSL_le ℝ
  have hQ : ‖ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)‖ = ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    ring
  have hk : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
  calc
    _ ≤ ‖(heatKernel 1 x * (‖x‖ ^ 2 / (16 * 1 ^ 4) - 7 / (8 * 1 ^ 3))) •
        (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x))‖ +
      ‖(heatKernel 1 x * (‖x‖ ^ 2 / (8 * 1 ^ 3) - 5 / (4 * 1 ^ 2))) • euclideanForm‖ :=
      norm_sub_le _ _
    _ ≤ (heatKernel 1 x * (‖x‖ ^ 2 / 16 + 7 / 8)) * ‖x‖ ^ 2 +
        (heatKernel 1 x * (‖x‖ ^ 2 / 8 + 5 / 4)) * 1 := by
      simp only [norm_smul, norm_mul, Real.norm_of_nonneg hk, hQ, one_pow, mul_one]
      apply add_le_add
      · gcongr
        exact (norm_sub_le _ _).trans_eq (by simp [Real.norm_of_nonneg (sq_nonneg ‖x‖)])
      · calc
          _ ≤ (heatKernel 1 x * ‖‖x‖ ^ 2 / 8 - 5 / 4‖) * 1 :=
            mul_le_mul_of_nonneg_left hI (by positivity)
          _ ≤ _ := by
            rw [mul_one]
            apply mul_le_mul_of_nonneg_left _ hk
            exact (norm_sub_le _ _).trans_eq (by simp [Real.norm_of_nonneg (sq_nonneg ‖x‖)])
    _ ≤ _ := by nlinarith [mul_nonneg hk (sq_nonneg (‖x‖ ^ 2))]


/-- Spatial continuity of the actual Hessian time derivative at positive time. -/
theorem continuous_hessian_time_deriv {t : ℝ} (ht : 0 < t) :
    Continuous (DtHess t) := by
  have hQ : Continuous (fun x : E =>
      ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
      euclideanForm.continuous).clm_apply euclideanForm.continuous
  change Continuous (fun x : E => deriv (fun r : ℝ => Hess r x) t)
  simp_rw [(hasDerivAt_hessian_time ht _).deriv]
  exact ((((contDiff_heatKernel_spatial («E» := E) t).continuous).mul
    (((continuous_norm.pow 2).div_const _).sub continuous_const)).smul hQ).sub
    ((((contDiff_heatKernel_spatial («E» := E) t).continuous).mul
      (((continuous_norm.pow 2).div_const _).sub continuous_const)).smul continuous_const)


/-- The quartic envelope remains integrable after a fractional radial weight. -/
theorem integrable_weighted_hessian_time_deriv_one {α : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) :
    Integrable (fun x : E => ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmajor := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
    («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).const_mul (512 * c)
  apply hmajor.mono'
    ((continuous_hessian_time_deriv zero_lt_one).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun x => ?_
  change ‖‖DtHess 1 x‖ * ‖x‖ ^ α‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
  have hk0 : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
  have hw : ‖x‖ ^ α ≤ 1 + ‖x‖ ^ 2 := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx hα).trans (by nlinarith [sq_nonneg ‖x‖])
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hα2
      rw [Real.rpow_two] at h
      linarith
  have hbase : 1 + ‖x‖ ^ 2 ≤ 16 * Real.exp (‖x‖ ^ 2 / 16) := by
    have h := Real.add_one_le_exp (‖x‖ ^ 2 / 16)
    linarith
  have hsquare : (1 + ‖x‖ ^ 2) ^ 2 ≤ 256 * Real.exp (‖x‖ ^ 2 / 8) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖ ^ 2) hbase 2
    have he : Real.exp (‖x‖ ^ 2 / 16) ^ 2 = Real.exp (‖x‖ ^ 2 / 8) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow, he, show (16 : ℝ) ^ 2 = 256 by norm_num] using h
  have hpoly : ‖x‖ ^ 4 + ‖x‖ ^ 2 + 2 ≤ 2 * (1 + ‖x‖ ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ ^ 2), sq_nonneg ‖x‖]
  have hk : heatKernel (1 : ℝ) x = c * Real.exp (-(‖x‖ ^ 2 / 4)) := by
    simp [heatKernel, c, ClosedSmoothModel, neg_div]
  calc
    _ ≤ (heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2)) * ‖x‖ ^ α :=
      mul_le_mul_of_nonneg_right (norm_hessian_time_deriv_one_le x) (by positivity)
    _ ≤ (heatKernel 1 x * (2 * (1 + ‖x‖ ^ 2) ^ 2)) * (1 + ‖x‖ ^ 2) := by
      gcongr
    _ ≤ (heatKernel 1 x * (2 * (256 * Real.exp (‖x‖ ^ 2 / 8)))) * (1 + ‖x‖ ^ 2) := by
      gcongr
    _ = (512 * c) * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) := by
      rw [hk]
      have he : Real.exp (-(‖x‖ ^ 2 / 4)) * Real.exp (‖x‖ ^ 2 / 8) =
          Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (512 * c) * ((1 + ‖x‖ ^ 2) *
          (Real.exp (-(‖x‖ ^ 2 / 4)) * Real.exp (‖x‖ ^ 2 / 8))) := by ring
        _ = _ := by rw [he]


/-- Parabolic dilation of the time derivative of the Gaussian Hessian. -/
theorem hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    DtHess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) • DtHess 1 x := by
  change deriv (fun r : ℝ => Hess r (a • x)) (a ^ 2) =
    ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) • deriv (fun r : ℝ => Hess r x) 1
  rw [(hasDerivAt_hessian_time (sq_pos_of_pos ha) (a • x)).deriv,
    (hasDerivAt_hessian_time zero_lt_one x).deriv]
  ext v w
  change (heatKernel (a ^ 2) (a • x) *
      (‖a • x‖ ^ 2 / (16 * (a ^ 2) ^ 4) - 7 / (8 * (a ^ 2) ^ 3))) *
        (⟪a • x, v⟫_ℝ * ⟪a • x, w⟫_ℝ) -
      (heatKernel (a ^ 2) (a • x) *
        (‖a • x‖ ^ 2 / (8 * (a ^ 2) ^ 3) - 5 / (4 * (a ^ 2) ^ 2))) * ⟪v, w⟫_ℝ =
    ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) *
      ((heatKernel 1 x * (‖x‖ ^ 2 / (16 * 1 ^ 4) - 7 / (8 * 1 ^ 3))) *
        (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) -
      (heatKernel 1 x * (‖x‖ ^ 2 / (8 * 1 ^ 3) - 5 / (4 * 1 ^ 2))) * ⟪v, w⟫_ℝ)
  rw [heatKernel_sq_smul a ha x, norm_smul_of_nonneg ha.le]
  simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
  field_simp

/-- Pointwise parabolic dilation including the radial weight. -/
theorem weighted_hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
    ‖DtHess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
      ((a ^ 3)⁻¹ * (a ^ 4)⁻¹ * a ^ α) * (‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  rw [hessian_time_deriv_sq_smul a ha x,
    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 4)⁻¹ by positivity) (DtHess 1 x),
    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
  ring


/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
theorem weighted_hessian_time_deriv_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
    (∫ x : E, ‖DtHess (a ^ 2) x‖ * ‖x‖ ^ α) =
      ((a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => ‖DtHess (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
  calc
    (a ^ 3)⁻¹ * (∫ x : E, ‖DtHess (a ^ 2) x‖ * ‖x‖ ^ α) =
        ∫ x : E, ‖DtHess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
    _ = ((a ^ 3)⁻¹ * (a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
      simp_rw [weighted_hessian_time_deriv_sq_smul a ha]
      rw [integral_const_mul]
    _ = (a ^ 3)⁻¹ * (((a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α)) := by ring


/-- Weighted Bochner integrability at every positive time. -/
theorem integrable_weighted_hessian_time_deriv {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => ‖DtHess t x‖ * ‖x‖ ^ α) := by
  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [← Real.sq_sqrt ht.le]
  apply (integrable_comp_smul_iff volume _ ha.ne').1
  simp_rw [weighted_hessian_time_deriv_sq_smul (Real.sqrt t) ha]
  exact (integrable_weighted_hessian_time_deriv_one hα hα2).const_mul _


/-- Exact scaling of the weighted Hessian time-derivative moment. -/
theorem weighted_hessian_time_deriv_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
    (∫ x : E, ‖DtHess t x‖ * ‖x‖ ^ α) =
      t ^ (α / 2 - 2) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  have h := weighted_hessian_time_deriv_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
  rw [Real.sq_sqrt ht.le] at h
  rw [h]
  congr 1
  have hp : (Real.sqrt t) ^ 4 = t ^ 2 := by nlinarith [Real.sq_sqrt ht.le]
  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_two]
  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
  ring

/-- The weighted time derivative has a positive constant uniform for all positive times. -/
theorem hessian_time_deriv_moment_bound :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : E => ‖DtHess t x‖ * ‖x‖ ^ α) ∧
      (∫ x : E, ‖DtHess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 2) := by
  intro α hα hα1
  refine ⟨max 1 (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  refine ⟨integrable_weighted_hessian_time_deriv hα.le (by linarith) ht, ?_⟩
  rw [weighted_hessian_time_deriv_integral ht, mul_comm (t ^ (α / 2 - 2))]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

/-- The new time interval contributes only the half-exponent Hölder tail. -/
theorem hessian_tail_bound {α K T t₁ t₂ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht₁ : t₁ ∈ Icc 0 T)
    (ht₂ : t₂ ∈ Icc 0 T) (h12 : t₁ ≤ t₂) {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖∫ s in t₁..t₂, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y‖ ≤
      ((∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * |t₂ - t₁| ^ (α / 2) := by
  have h := norm_integral_cancelled_hessian_near_le hα hα1 h12
    (fun s hs => hK s ⟨ht₁.1.trans hs.1.le, hs.2.le.trans ht₂.2⟩) x
  rw [abs_of_nonneg (sub_nonneg.mpr h12)]
  convert h using 1
  ring

/-- An interval ending before the observation time obeys the same short-interval bound. -/
theorem norm_integral_cancelled_hessian_before_le {α K a b t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hab : a ≤ b) (hbt : b ≤ t)
    {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a b, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖∫ s in a..b, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * (b - a) ^ (α / 2) := by
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
  have hA : 0 ≤ A := mul_nonneg hK0 (integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
  have hi : IntervalIntegrable (fun s : ℝ => A * (b - s) ^ (α / 2 - 1)) volume a b := by
    have h := ((intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := b - a) (r := α / 2 - 1) (by linarith)).comp_sub_left b).symm
    simp only [sub_zero, sub_sub_cancel] at h
    exact h.const_mul A
  have hb : ‖∫ s in Ioo a b, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      ∫ s in Ioo a b, A * (b - s) ^ (α / 2 - 1) := by
    apply norm_integral_le_of_norm_le
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (norm_cancelled_hessian_integral_le hα.le (by linarith)
      (by linarith [hs.2] : 0 < t - s) (hK s hs) x).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hs.2) (by linarith) (by linarith)) hA)
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hab] at hb
  refine hb.trans_eq ?_
  have he := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := b - a)
    (fun s : ℝ => A * (b - s) ^ (α / 2 - 1)) a
  simp only [zero_add, sub_add_cancel] at he
  have hs (s : ℝ) : b - (s + a) = b - a - s := by ring
  simp only [hs] at he
  rw [← he, integral_hessian_majorant hα]

/-- The recent part of a time increment costs twice the Hessian majorant. -/
theorem near_hessian_time_difference_le {α K a t₁ t₂ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (ha : a ≤ t₁) (h12 : t₁ ≤ t₂)
    (hscale : t₁ - a ≤ t₂ - t₁) {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a t₁, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖(∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y) -
      (∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y)‖ ≤
      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * (t₂ - t₁) ^ (α / 2) := by
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hK0 (integral_nonneg (fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))))
    (div_nonneg (by norm_num) hα.le)
  have hp : (t₁ - a) ^ (α / 2) ≤ (t₂ - t₁) ^ (α / 2) :=
    Real.rpow_le_rpow (sub_nonneg.mpr ha) hscale (by linarith)
  calc
    _ ≤ ‖∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y‖ +
      ‖∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y‖ :=
      norm_sub_le _ _
    _ ≤ A * (t₁ - a) ^ (α / 2) + A * (t₁ - a) ^ (α / 2) :=
      add_le_add (norm_integral_cancelled_hessian_before_le hα hα1 hK0 ha h12 hK x)
        (norm_integral_cancelled_hessian_before_le hα hα1 hK0 ha le_rfl hK x)
    _ ≤ A * (t₂ - t₁) ^ (α / 2) + A * (t₂ - t₁) ^ (α / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hp hA) (mul_le_mul_of_nonneg_left hp hA)
    _ = _ := by dsimp [A]; ring

/-- Dilation gives joint continuity of the full DtHessian at positive times. -/
theorem continuous_hessian_time_deriv_pos :
    Continuous (fun p : Ioi (0 : ℝ) × E => DtHess p.1 p.2) := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  have hunit : Continuous (DtHess 1) := continuous_hessian_time_deriv zero_lt_one
  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
    Real.sqrt_pos.2 p.1.property
  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * ((Real.sqrt (p.1 : ℝ)) ^ 4)⁻¹) •
        DtHess 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
      ((ha.pow 4).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')) |>.smul
      (hunit.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
  apply hc.congr
  intro p
  have h := hessian_time_deriv_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm


/-- The weighted time derivative is integrable jointly on every positive time slab. -/
theorem integrable_time_weighted_hessian_deriv {α a : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (b : ℝ) :
    Integrable (fun p : ℝ × E => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α)
      ((volume.restrict (Icc a b)).prod volume) := by
  let G : ℝ × E → ℝ := fun p => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α
  have hpos (p : ℝ × E) : 0 < max a p.1 := ha.trans_le (le_max_left _ _)
  have hD : Continuous (fun p : ℝ × E => DtHess (max a p.1) p.2) :=
    continuous_hessian_time_deriv_pos.comp
      (((continuous_const.max continuous_fst).subtype_mk hpos).prodMk continuous_snd)
  have hg : Continuous G := hD.norm.mul
    ((Real.continuous_rpow_const hα).comp continuous_snd.norm)
  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro r
    change Integrable (fun y : E => ‖DtHess (max a r) y‖ * ‖y‖ ^ α) volume
    exact integrable_weighted_hessian_time_deriv hα hα2 (ha.trans_le (le_max_left a r))
  · have hm := hg.norm.stronglyMeasurable.integral_prod_right' (ν := volume)
    refine (integrable_const (a ^ (α / 2 - 2) * J)).mono' hm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun r => ?_
    have he : (∫ y : E, ‖G (r, y)‖) = ∫ y : E, G (r, y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
    change (∫ y : E, ‖DtHess (max a r) y‖ * ‖y‖ ^ α) ≤ _
    rw [weighted_hessian_time_deriv_integral (ha.trans_le (le_max_left _ _))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos ha (le_max_left _ _) (by linarith)) hJ

/-- Integrating the actual time derivative bounds a kernel Hessian increment. -/
theorem norm_hessian_time_difference_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : E) :
    ‖Hess b y - Hess a y‖ ≤ ∫ r in a..b, ‖DtHess (max a r) y‖ := by
  have hD : Continuous (fun r : ℝ => DtHess (max a r) y) :=
    continuous_hessian_time_deriv_pos.comp
      (((continuous_const.max continuous_id).subtype_mk
        (fun r => ha.trans_le (le_max_left _ _))).prodMk continuous_const)
  have hd (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => Hess t y) (DtHess (max a r) y) r := by
    rw [uIcc_of_le hab] at hr
    rw [max_eq_right hr.1]
    exact (hasDerivAt_hessian_time (ha.trans_le hr.1) y).differentiableAt.hasDerivAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hD.intervalIntegrable a b)
  rw [← he]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- A weighted kernel Hessian time increment is linear away from time zero. -/
theorem weighted_hessian_time_difference {α a b : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (hab : a ≤ b) :
    Integrable (fun y : E => ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) ∧
    (∫ y : E, ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) ≤
      (b - a) * a ^ (α / 2 - 2) * (∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) := by
  let G : ℝ × E → ℝ := fun p => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α
  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  have hg : Integrable G ((volume.restrict (Icc a b)).prod volume) :=
    integrable_time_weighted_hessian_deriv hα hα2 ha b
  have hiMajor := hg.integral_prod_right
  have hb (y : E) : ‖Hess b y - Hess a y‖ * ‖y‖ ^ α ≤ ∫ r in Icc a b, G (r, y) := by
    calc
      _ ≤ (∫ r in a..b, ‖DtHess (max a r) y‖) * ‖y‖ ^ α :=
        mul_le_mul_of_nonneg_right (norm_hessian_time_difference_le ha hab y)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
        exact (intervalIntegral.integral_mul_const _ _).symm
  have hH (t : ℝ) : Continuous (Hess t) :=
    (((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hi : Integrable (fun y : E => ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) :=
    hiMajor.mono' (((hH b).sub (hH a)).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        change ‖‖Hess b y - Hess a y‖ * ‖y‖ ^ α‖ ≤ _
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
        exact hb y)
  refine ⟨hi, (integral_mono hi hiMajor hb).trans ?_⟩
  rw [← integral_integral_swap hg]
  calc
    (∫ r in Icc a b, ∫ y : E, G (r, y)) ≤ ∫ _r in Icc a b, a ^ (α / 2 - 2) * J := by
      apply integral_mono_ae hg.integral_prod_left (integrable_const _)
      refine Filter.Eventually.of_forall fun r => ?_
      change (∫ y : E, ‖DtHess (max a r) y‖ * ‖y‖ ^ α) ≤ _
      rw [weighted_hessian_time_deriv_integral (ha.trans_le (le_max_left _ _))]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos ha (le_max_left _ _) (by linarith)) hJ
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- The far-time fourth-order power integrates to the half Hölder exponent. -/
theorem far_time_deriv_power_integral_le {α τ t : ℝ}
    (hα1 : α < 1) (hτ : 0 < τ) (ht : τ ≤ t) :
    τ * (∫ s in (0 : ℝ)..(t - τ), (t - s) ^ (α / 2 - 2)) ≤
      (2 / (2 - α)) * τ ^ (α / 2) := by
  have hq : α / 2 - 2 + 1 < 0 := by linarith
  rw [intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => r ^ (α / 2 - 2)) t, sub_sub_cancel, sub_zero]
  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
  · calc
      τ * ((t ^ (α / 2 - 2 + 1) - τ ^ (α / 2 - 2 + 1)) / (α / 2 - 2 + 1)) ≤
          τ * (-τ ^ (α / 2 - 2 + 1) / (α / 2 - 2 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hτ.le
        simp only [div_eq_mul_inv]
        apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
        have hnn := Real.rpow_nonneg (hτ.le.trans ht) (α / 2 - 2 + 1)
        simp only [div_eq_mul_inv] at hnn
        linarith only [hnn]
      _ = (2 / (2 - α)) * τ ^ (α / 2) := by
        rw [show α / 2 - 2 + 1 = α / 2 - 1 by ring, Real.rpow_sub hτ, Real.rpow_one]
        field_simp [hτ.ne', show 2 - α ≠ 0 by linarith, show α / 2 - 1 ≠ 0 by linarith]
        ring_nf
        all_goals
          have hi := mul_inv_cancel₀ (show -2 + α ≠ 0 by linarith)
          nlinarith only [hi]
  · rw [uIcc_of_le ht]
    intro hz
    exact (not_le.mpr hτ) hz.1

/-- Cancellation transfers the weighted kernel time increment to Hölder forcing. -/
theorem norm_cancelled_hessian_time_difference_le {α a b M K : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (hab : a ≤ b) (hK0 : 0 ≤ K)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (hM : ∀ y, ‖f y‖ ≤ M)
    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖(∫ y : E, (f (x - y) - f x) • Hess b y) -
      (∫ y : E, (f (x - y) - f x) • Hess a y)‖ ≤
      ((∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) * K * (b - a)) * a ^ (α / 2 - 2) := by
  rw [← integral_sub (integrable_cancelled_hessian (ha.trans_le hab) hf hM x)
    (integrable_cancelled_hessian ha hf hM x)]
  simp_rw [← smul_sub]
  have hi := (weighted_hessian_time_difference hα hα2 ha hab).1.const_mul K
  have hb (y : E) : ‖(f (x - y) - f x) • (Hess b y - Hess a y)‖ ≤
      K * (‖Hess b y - Hess a y‖ * ‖y‖ ^ α) := by
    have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
      have he : x - y - x = -y := by abel
      simpa only [he, norm_neg, Real.norm_eq_abs] using hK (x - y) x
    calc
      _ ≤ ‖f (x - y) - f x‖ * ‖Hess b y - Hess a y‖ :=
        norm_real_smul_continuousLinearMap_two_le _ _
      _ ≤ (K * ‖y‖ ^ α) * ‖Hess b y - Hess a y‖ :=
        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∫ y : E, K * (‖Hess b y - Hess a y‖ * ‖y‖ ^ α) :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
    _ = K * (∫ y : E, ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) := integral_const_mul _ _
    _ ≤ K * ((b - a) * a ^ (α / 2 - 2) * (∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α)) :=
      mul_le_mul_of_nonneg_left (weighted_hessian_time_difference hα hα2 ha hab).2 hK0
    _ = _ := by ring

/-- The far part of the Duhamel time increment has the required half Hölder power. -/
theorem far_hessian_time_difference_le {α T t₁ t₂ M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht₁ : t₁ ∈ Icc 0 T) (ht₂ : t₂ ∈ Icc 0 T)
    (h12 : t₁ < t₂) (hscale : t₂ - t₁ < t₁) (hK0 : 0 ≤ K)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖(∫ s in (0 : ℝ)..(t₁ - (t₂ - t₁)), ∫ y : E,
        (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y) -
      (∫ s in (0 : ℝ)..(t₁ - (t₂ - t₁)), ∫ y : E,
        (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y)‖ ≤
      ((∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) * (2 / (2 - α))) *
        K * (t₂ - t₁) ^ (α / 2) := by
  let a := t₁ - (t₂ - t₁)
  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
  let F := fun r s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (r - s) y
  have ha : 0 < a := sub_pos.mpr hscale
  have hτ : 0 < t₂ - t₁ := sub_pos.mpr h12
  have hat : a ≤ t₁ := sub_le_self t₁ hτ.le
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  have hFi (r : ℝ) (hr : r ∈ Icc 0 T) (har : a ≤ r) :
      IntervalIntegrable (F r) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      ((integrableOn_cancelled_hessian_time hα hα1 hr hf hK x).mono_set
        (Ioo_subset_Ioo le_rfl har))
  have hip : IntervalIntegrable (fun r : ℝ => r ^ (α / 2 - 2)) volume (t₂ - t₁) t₁ := by
    apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
    rw [uIcc_of_le hscale.le]
    intro hz
    exact (not_le.mpr hτ) hz.1
  have hiB : IntervalIntegrable
      (fun s : ℝ => J * K * (t₂ - t₁) * (t₁ - s) ^ (α / 2 - 2)) volume 0 a := by
    have h := (hip.comp_sub_left t₁).symm
    simp only [sub_self] at h
    exact h.const_mul (J * K * (t₂ - t₁))
  have hbound : ‖∫ s in (0 : ℝ)..a, F t₂ s - F t₁ s‖ ≤
      ∫ s in (0 : ℝ)..a, J * K * (t₂ - t₁) * (t₁ - s) ^ (α / 2 - 2) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ha.le _ hiB
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, (hs.2.trans hat).trans ht₁.2⟩
    have hsτ : t₂ - t₁ ≤ t₁ - s := by dsimp [a] at hs; linarith [hs.2]
    have hlag : 0 < t₁ - s := hτ.trans_le hsτ
    have hfc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM s hsT
    have hd := norm_cancelled_hessian_time_difference_le hα.le (by linarith) hlag
      (show t₁ - s ≤ t₂ - s by linarith) hK0 hfc.aestronglyMeasurable hMs (hK s hsT) x
    have he : t₂ - s - (t₁ - s) = t₂ - t₁ := by ring
    simpa only [he] using hd
  change ‖(∫ s in (0 : ℝ)..a, F t₂ s) - (∫ s in (0 : ℝ)..a, F t₁ s)‖ ≤ _
  rw [← intervalIntegral.integral_sub (hFi t₂ ht₂ (hat.trans h12.le)) (hFi t₁ ht₁ hat)]
  refine hbound.trans ?_
  rw [intervalIntegral.integral_const_mul]
  calc
    (J * K * (t₂ - t₁)) * (∫ s in (0 : ℝ)..a, (t₁ - s) ^ (α / 2 - 2)) =
      (J * K) * ((t₂ - t₁) * (∫ s in (0 : ℝ)..a, (t₁ - s) ^ (α / 2 - 2))) := by ring
    _ ≤ (J * K) * ((2 / (2 - α)) * (t₂ - t₁) ^ (α / 2)) :=
      mul_le_mul_of_nonneg_left (far_time_deriv_power_integral_le hα1 hτ hscale.le)
        (mul_nonneg hJ hK0)
    _ = _ := by ring

/-- The time Hölder estimate for the actual Duhamel Hessian, including both endpoints. -/
theorem duhamel_hessian_time_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ x : E,
    ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖
      ≤ C * K * |t₁ - t₂| ^ (α / 2) := by
  intro α hα hα1
  let B := (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
  let F := (∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) * (2 / (2 - α))
  have hB : 0 ≤ B := mul_nonneg (integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (div_nonneg (by norm_num) hα.le)
  have hF : 0 ≤ F := mul_nonneg (integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (div_nonneg (by norm_num) (by linarith))
  refine ⟨max 1 (3 * B + F), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro T _ _ f M K _ hK0 hf hM hK
  let u : ℝ → E → ℝ := fun t x => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  change ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ x : E,
    ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖ ≤
      max 1 (3 * B + F) * K * |t₁ - t₂| ^ (α / 2)
  have ordered (t₁ : ℝ) (ht₁ : t₁ ∈ Icc 0 T) (t₂ : ℝ) (ht₂ : t₂ ∈ Icc 0 T)
      (h12 : t₁ ≤ t₂) (x : E) :
      ‖fderiv ℝ (fderiv ℝ (u t₂)) x - fderiv ℝ (fderiv ℝ (u t₁)) x‖ ≤
        (3 * B + F) * K * (t₂ - t₁) ^ (α / 2) := by
    by_cases he : t₁ = t₂
    · subst t₂
      simp [Real.zero_rpow (show α / 2 ≠ 0 by linarith)]
    have hlt : t₁ < t₂ := lt_of_le_of_ne h12 he
    let H := fun r s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (r - s) y
    have hi (r : ℝ) (hr : r ∈ Icc 0 T) (b : ℝ) (hb : 0 ≤ b) (hbr : b ≤ r) :
        IntervalIntegrable (H r) volume 0 b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hb).mpr
        ((integrableOn_cancelled_hessian_time hα hα1 hr hf hK x).mono_set
          (Ioo_subset_Ioo le_rfl hbr))
    have hsplit : (∫ s in (0 : ℝ)..t₂, H t₂ s) =
        (∫ s in (0 : ℝ)..t₁, H t₂ s) + (∫ s in t₁..t₂, H t₂ s) :=
      (intervalIntegral.integral_add_adjacent_intervals (hi t₂ ht₂ t₁ ht₁.1 h12)
        ((hi t₂ ht₂ t₁ ht₁.1 h12).symm.trans (hi t₂ ht₂ t₂ ht₂.1 le_rfl))).symm
    have htail : ‖∫ s in t₁..t₂, H t₂ s‖ ≤ B * K * (t₂ - t₁) ^ (α / 2) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr h12)] using hessian_tail_bound hα hα1 ht₁ ht₂ h12 hK x
    have hoverlap : ‖(∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ ≤
        (2 * B + F) * K * (t₂ - t₁) ^ (α / 2) := by
      by_cases hsmall : t₁ ≤ t₂ - t₁
      · have hn := near_hessian_time_difference_le hα hα1 hK0 ht₁.1 h12
          (by simpa using hsmall)
          (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht₁.2⟩) x
        have hn' : ‖(∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ ≤
            (2 * B) * K * (t₂ - t₁) ^ (α / 2) := by
          convert hn using 1
          dsimp [B]
          ring
        exact hn'.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : 2 * B ≤ 2 * B + F) hK0)
          (Real.rpow_nonneg (sub_nonneg.mpr h12) _))
      have hscale : t₂ - t₁ < t₁ := lt_of_not_ge hsmall
      let a := t₁ - (t₂ - t₁)
      have ha : 0 < a := sub_pos.mpr hscale
      have hat : a ≤ t₁ := sub_le_self t₁ (sub_nonneg.mpr h12)
      have hs (r : ℝ) (hr : r ∈ Icc 0 T) (htr : t₁ ≤ r) :
          (∫ s in (0 : ℝ)..t₁, H r s) =
            (∫ s in (0 : ℝ)..a, H r s) + (∫ s in a..t₁, H r s) :=
        (intervalIntegral.integral_add_adjacent_intervals (hi r hr a ha.le (hat.trans htr))
          ((hi r hr a ha.le (hat.trans htr)).symm.trans (hi r hr t₁ ht₁.1 htr))).symm
      have hn : ‖(∫ s in a..t₁, H t₂ s) - (∫ s in a..t₁, H t₁ s)‖ ≤
          (2 * B) * K * (t₂ - t₁) ^ (α / 2) := by
        have h := near_hessian_time_difference_le hα hα1 hK0 hat h12
          (by dsimp [a]; linarith)
          (fun s hs => hK s ⟨ha.le.trans hs.1.le, hs.2.le.trans ht₁.2⟩) x
        convert h using 1
        dsimp [B]
        ring
      have hfar : ‖(∫ s in (0 : ℝ)..a, H t₂ s) - (∫ s in (0 : ℝ)..a, H t₁ s)‖ ≤
          F * K * (t₂ - t₁) ^ (α / 2) :=
        far_hessian_time_difference_le hα hα1 ht₁ ht₂ hlt hscale hK0 hf hM hK x
      rw [hs t₂ ht₂ h12, hs t₁ ht₁ le_rfl]
      calc
        _ = ‖((∫ s in (0 : ℝ)..a, H t₂ s) - (∫ s in (0 : ℝ)..a, H t₁ s)) +
            ((∫ s in a..t₁, H t₂ s) - (∫ s in a..t₁, H t₁ s))‖ := by congr 1; abel
        _ ≤ ‖(∫ s in (0 : ℝ)..a, H t₂ s) - (∫ s in (0 : ℝ)..a, H t₁ s)‖ +
            ‖(∫ s in a..t₁, H t₂ s) - (∫ s in a..t₁, H t₁ s)‖ := norm_add_le _ _
        _ ≤ F * K * (t₂ - t₁) ^ (α / 2) + (2 * B) * K * (t₂ - t₁) ^ (α / 2) :=
          add_le_add hfar hn
        _ = _ := by ring
    rw [hessian_duhamel_eq_integral hα hα1 ht₂ hf hM hK x,
      hessian_duhamel_eq_integral hα hα1 ht₁ hf hM hK x]
    change ‖(∫ s in (0 : ℝ)..t₂, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ ≤ _
    rw [hsplit]
    calc
      _ = ‖((∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)) +
          (∫ s in t₁..t₂, H t₂ s)‖ := by congr 1; abel
      _ ≤ ‖(∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ +
          ‖∫ s in t₁..t₂, H t₂ s‖ := norm_add_le _ _
      _ ≤ (2 * B + F) * K * (t₂ - t₁) ^ (α / 2) + B * K * (t₂ - t₁) ^ (α / 2) :=
        add_le_add hoverlap htail
      _ = _ := by ring
  intro t₁ ht₁ t₂ ht₂ x
  have hraw : ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖ ≤
      (3 * B + F) * K * |t₁ - t₂| ^ (α / 2) := by
    rcases le_total t₁ t₂ with h12 | h21
    · rw [abs_sub_comm t₁ t₂, abs_of_nonneg (sub_nonneg.mpr h12), norm_sub_rev]
      exact ordered t₁ ht₁ t₂ ht₂ h12 x
    · rw [abs_of_nonneg (sub_nonneg.mpr h21)]
      exact ordered t₂ ht₂ t₁ ht₁ h21 x
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right 1 (3 * B + F)) hK0)
    (Real.rpow_nonneg (abs_nonneg _) _))

end Poincare.HeatDuhamelHessianTimeHolder

end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Poincare.DuhamelParabolicHolderSeminorm

local notation "E" => Poincare.ClosedSmoothModel 3

/-- Spatial and temporal Hessian estimates give the parabolic Hölder bound. -/
theorem duhamel_hessian_parabolic_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ p ∈ ParabolicHolder.cylinder («E» := E) T, ∀ q ∈ ParabolicHolder.cylinder («E» := E) T,
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
      ≤ C * K * ParabolicHolder.parabolicDist p q ^ α := by
  intro α hα hα1
  obtain ⟨C₁, hC₁, hspace⟩ :=
    HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder α hα hα1
  obtain ⟨C₂, hC₂, htime⟩ :=
    HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder α hα hα1
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro p hp q hq
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  have hs := hspace T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 p.2 q.2
  have ht := htime T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 q.1 hq.1 q.2
  have hspow : ‖p.2 - q.2‖ ^ α ≤ ParabolicHolder.parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _)
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have htpow : |p.1 - q.1| ^ (α / 2) ≤ ParabolicHolder.parabolicDist p q ^ α := by
    calc
      |p.1 - q.1| ^ (α / 2) = (Real.sqrt |p.1 - q.1|) ^ α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ ParabolicHolder.parabolicDist p q ^ α :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _)
          (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  calc
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ ≤
        ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2‖ +
        ‖fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2)
        (fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
    _ ≤ C₁ * K * ‖p.2 - q.2‖ ^ α + C₂ * K * |p.1 - q.1| ^ (α / 2) :=
      add_le_add hs ht
    _ ≤ C₁ * K * ParabolicHolder.parabolicDist p q ^ α +
        C₂ * K * ParabolicHolder.parabolicDist p q ^ α :=
      add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg hC₁.le hK))
        (mul_le_mul_of_nonneg_left htpow (mul_nonneg hC₂.le hK))
    _ = (C₁ + C₂) * K * ParabolicHolder.parabolicDist p q ^ α := by ring

/-- The Duhamel Hessian satisfies the landed parabolic Hölder predicate. -/
theorem hasHolderBound_duhamel_hessian :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ParabolicHolder.HasHolderBound α (ParabolicHolder.cylinder («E» := E) T)
    (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K) := by
  intro α hα hα1
  obtain ⟨C, hC, hbound⟩ := duhamel_hessian_parabolic_holder α hα hα1
  exact ⟨C, hC, hbound⟩

end Poincare.DuhamelParabolicHolderSeminorm

end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
theorem continuousOn_heat_integrand_extension {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
  apply hc.congr
  intro p hp
  dsimp only
  by_cases hz : p.1 = 0
  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  · rw [if_neg hz]
    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
      (fun y => f (p.2, y)) x
    rwa [Real.sq_sqrt hpos.le] at he

/-- The Duhamel boundary term converges to the forcing at the observation point. -/
theorem tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    Filter.Tendsto (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x)
      (𝓝[Ico 0 t] t) (𝓝 (f (t, x))) := by
  have hc : ContinuousOn (fun s : ℝ => ∫ y : E,
      heatKernel 1 y * f (s, x - Real.sqrt (t - s) • y)) (Icc 0 T) :=
    (continuousOn_rescaled_heat_integral hf hM x).comp
      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩)
  have hl := (hc t ht).tendsto.mono_left
    (nhdsWithin_mono t (show Ico 0 t ⊆ Icc 0 T from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩))
  have hmass : (∫ y : E, heatKernel 1 y * f (t, x - Real.sqrt (t - t) • y)) =
      f (t, x) := by
    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  rw [hmass] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < t - s := sub_pos.mpr hs.2
  have he := heatSolution_sq (Real.sqrt (t - s)) (Real.sqrt_pos.mpr hpos)
    (fun y => f (s, y)) x
  rw [Real.sq_sqrt hpos.le] at he
  exact he.symm

/-- The interior time derivative is integrable and its integral is the Duhamel Laplacian. -/
theorem duhamel_time_derivative_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t ∧
    (∫ s in (0 : ℝ)..t,
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =
      (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
        heatSolution (t - s) (fun y => f (s, y)) z)) x := by
  have he : (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =ᵐ[volume.restrict (Ι 0 t)]
      (fun s : ℝ => (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x).deriv
  refine ⟨(intervalIntegrable_heat_laplacian hα hα1 ht hf hM hK x).congr_ae he.symm, ?_⟩
  rw [laplacian_duhamel_eq_integral hα hα1 ht hf hM hK x]
  exact intervalIntegral.integral_congr_ae_restrict he

/-- The specified Duhamel formula has zero initial value. -/
theorem duhamel_zero (f : ℝ × E → ℝ) (x : E) :
    (∫ s in (0 : ℝ)..0, heatSolution (0 - s) (fun y => f (s, y)) x) = 0 := by
  exact intervalIntegral.integral_same

end Poincare.HeatDuhamelHeatEquation

end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace Poincare.MovingLimitLeibniz

/-- Integrable bounds on secants permit differentiation within an arbitrary real set. -/
theorem hasDerivWithinAt_integral_of_dominated_secants
    {G : ℝ → ℝ → ℝ} {D B : ℝ → ℝ} {μ : Measure ℝ} {S : Set ℝ} {t : ℝ}
    (hG : ∀ᶠ r in 𝓝[S] t, Integrable (G r) μ)
    (hGt : Integrable (G t) μ) (hB : Integrable B μ)
    (hbound : ∀ᶠ r in 𝓝[S] t, ∀ᵐ s ∂μ,
      ‖G r s - G t s‖ ≤ B s * ‖r - t‖)
    (hD : ∀ᵐ s ∂μ, HasDerivWithinAt (fun r => G r s) (D s) S t) :
    HasDerivWithinAt (fun r => ∫ s, G r s ∂μ) (∫ s, D s ∂μ) S t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hle : 𝓝[S \ {t}] t ≤ 𝓝[S] t := nhdsWithin_mono _ diff_subset
  have hi := tendsto_integral_filter_of_dominated_convergence B
    (by
      filter_upwards [hG.filter_mono hle] with r hr
      exact (hr.aestronglyMeasurable.sub hGt.aestronglyMeasurable).const_mul (r-t)⁻¹)
    (by
      filter_upwards [hbound.filter_mono hle, self_mem_nhdsWithin] with r hr hrt
      have hn : r - t ≠ 0 := sub_ne_zero.mpr (by simpa using hrt.2)
      filter_upwards [hr] with s hs
      rw [norm_mul, norm_inv]
      calc
        ‖r - t‖⁻¹ * ‖G r s - G t s‖ ≤ ‖r - t‖⁻¹ * (B s * ‖r - t‖) :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (norm_nonneg _))
        _ = B s := by rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn), mul_one])
    hB (by
      filter_upwards [hD] with s hs
      simpa only [slope, smul_eq_mul] using
        (hasDerivWithinAt_iff_tendsto_slope.mp hs))
  apply hi.congr'
  filter_upwards [hG.filter_mono hle] with r hr
  simp only [slope, smul_eq_mul, Pi.sub_apply, vsub_eq_sub,
    integral_const_mul, integral_sub hr hGt]

/-- The primitive of a continuous function has the expected derivative at both endpoints. -/
theorem hasDerivWithinAt_integral_Icc {g : ℝ → ℝ} {T t : ℝ}
    (ht : t ∈ Icc 0 T) (hg : ContinuousOn g (Icc 0 T)) :
    HasDerivWithinAt (fun r => ∫ s in (0 : ℝ)..r, g s) (g t) (Icc 0 T) t := by
  let c : ℝ → ℝ := fun r => max 0 (min T r)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (r : ℝ) : c r ∈ Icc 0 T :=
    ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (min_le_left _ _)⟩
  have hce (r : ℝ) (hr : r ∈ Icc 0 T) : c r = r := by
    simp only [c, min_eq_right hr.2, max_eq_right hr.1]
  have hg' : Continuous (fun r => g (c r)) := hg.comp_continuous hc hcm
  have hd := intervalIntegral.integral_hasDerivAt_right (hg'.intervalIntegrable 0 t)
    hg'.aestronglyMeasurable.stronglyMeasurableAtFilter hg'.continuousAt
  rw [hce t ht] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro r hr
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hr.1] at hs
  change g s = g (c s)
  rw [hce s ⟨hs.1, hs.2.trans hr.2⟩]

/-- Clipping below the diagonal reduces the moving limit to dominated secants on a fixed interval. -/
theorem hasDerivWithinAt_integral_moving_limit_of_secants
    {F D : ℝ → ℝ → ℝ} {b T t : ℝ} (ht : t ∈ Icc 0 T)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1})
    (hdiag : F t t = b)
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t)
    (hbound : ∃ B : ℝ → ℝ, IntegrableOn B (Ioc 0 T) ∧
      ∀ᶠ r in 𝓝[Icc 0 T] t, ∀ᵐ s ∂volume.restrict (Ioc 0 T),
        ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r-t‖) :
    HasDerivWithinAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, F r s)
      (b + ∫ s in (0 : ℝ)..t, D t s) (Icc 0 T) t := by
  let G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
  let d : ℝ → ℝ := (Iic t).indicator (D t)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T) :=
    hcont.comp (continuous_id.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hs, hs, le_rfl⟩)
  have hcG (r : ℝ) (hr : r ∈ Icc 0 T) : ContinuousOn (G r) (Icc 0 T) :=
    (hcont.comp ((continuous_const.max continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨hs, ⟨hr.1.trans (le_max_left _ _), max_le hr.2 hs.2⟩,
        le_max_right _ _⟩)).sub hcdiag
  have hiG (r : ℝ) (hr : r ∈ Icc 0 T) : IntegrableOn (G r) (Ioc 0 T) :=
    (hcG r hr).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  obtain ⟨B, hB, hb⟩ := hbound
  have hdG : HasDerivWithinAt (fun r => ∫ s in Ioc 0 T, G r s)
      (∫ s in Ioc 0 T, d s) (Icc 0 T) t := by
    apply hasDerivWithinAt_integral_of_dominated_secants
      (B := B) (Eventually.mono self_mem_nhdsWithin hiG) (hiG t ht) hB
    · filter_upwards [hb] with r hr
      filter_upwards [hr] with s hs
      simpa only [G, sub_sub_sub_cancel_right] using hs
    · filter_upwards [ae_restrict_mem measurableSet_Ioc,
        (volume.restrict (Ioc 0 T)).ae_ne t] with s hs hst
      by_cases hlt : s < t
      · have hd := (hderiv s ⟨hs.1, hlt⟩).sub_const (F s s)
        have he : (G · s) =ᶠ[𝓝 t] (fun r => F r s - F s s) := by
          filter_upwards [Ioi_mem_nhds hlt] with r hr
          simp only [G, max_eq_left (le_of_lt (show s < r from hr))]
        have hd' := hd.congr_of_eventuallyEq he
        simpa only [d, indicator_of_mem (show s ∈ Iic t from hlt.le)] using
          hd'.hasDerivWithinAt (s := Icc 0 T)
      · have hgt : t < s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
        have he : (G · s) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          filter_upwards [Iio_mem_nhds hgt] with r hr
          simp only [G, max_eq_right (le_of_lt (show r < s from hr)), sub_self]
        have hd' := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
        simpa only [d, indicator_of_notMem (show s ∉ Iic t from not_le.mpr hgt)] using
          hd'.hasDerivWithinAt (s := Icc 0 T)
  have hdint : (∫ s in Ioc 0 T, d s) = ∫ s in (0 : ℝ)..t, D t s := by
    rw [← intervalIntegral.integral_of_le hT]
    exact intervalIntegral.integral_indicator (f := D t) ht
  rw [hdint] at hdG
  have hde := hdG.add (hasDerivWithinAt_integral_Icc ht hcdiag)
  rw [hdiag, add_comm (∫ s in (0 : ℝ)..t, D t s) b] at hde
  apply hde.congr_of_mem _ ht
  intro r hr
  have he : G r = (Iic r).indicator (fun s => F r s - F s s) := by
    funext s
    by_cases hs : s ≤ r
    · simp only [G, indicator_of_mem (show s ∈ Iic r from hs), max_eq_left hs]
    · simp only [G, indicator_of_notMem (show s ∉ Iic r from hs), max_eq_right (le_of_not_ge hs), sub_self]
  change (∫ s in (0 : ℝ)..r, F r s) =
    (∫ s in Ioc 0 T, G r s) + ∫ s in (0 : ℝ)..r, F s s
  rw [← intervalIntegral.integral_of_le hT, he]
  have hcut : (∫ s in (0 : ℝ)..T, (Iic r).indicator (fun s => F r s - F s s) s) =
      ∫ s in (0 : ℝ)..r, F r s - F s s :=
    intervalIntegral.integral_indicator hr
  rw [hcut]
  have hcF : ContinuousOn (F r) (Icc 0 r) :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨⟨hs.1, hs.2.trans hr.2⟩, hr, hs.2⟩)
  rw [intervalIntegral.integral_sub (hcF.intervalIntegrable_of_Icc hr.1)
    ((hcdiag.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1)]
  ring

/-- An interior derivative comparison controls increments even at singular endpoints. -/
theorem abs_sub_le_of_deriv_comparison
    {g g' v v' : ℝ → ℝ} {a z : ℝ} (haz : a ≤ z)
    (hg : ContinuousOn g (Icc a z)) (hv : ContinuousOn v (Icc a z))
    (hdg : ∀ r ∈ Ioo a z, HasDerivAt g (g' r) r)
    (hdv : ∀ r ∈ Ioo a z, HasDerivAt v (v' r) r)
    (hb : ∀ r ∈ Ioo a z, |g' r| ≤ v' r) :
    |g z - g a| ≤ v z - v a := by
  have hm : MonotoneOn (fun r => v r - g r) (Icc a z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hv.sub hg)
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hdv r hr).sub (hdg r hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      change 0 ≤ deriv (v - g) r
      rw [((hdv r hr).sub (hdg r hr)).deriv]
      exact sub_nonneg.mpr ((le_abs_self _).trans (hb r hr))
  have hp : MonotoneOn (fun r => v r + g r) (Icc a z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hv.add hg)
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hdv r hr).add (hdg r hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      change 0 ≤ deriv (v + g) r
      rw [((hdv r hr).add (hdg r hr)).deriv]
      have := (abs_le.mp (hb r hr)).1
      linarith
  have h1 := hm (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz) haz
  have h2 := hp (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz) haz
  exact abs_le.mpr ⟨by dsimp at h2; linarith, by dsimp at h1; linarith⟩

/-- Integrating a singular power bound requires no derivative at the initial endpoint. -/
theorem abs_sub_le_rpow_of_deriv_bound
    {g g' : ℝ → ℝ} {s T u v C β : ℝ} (hβ : 0 < β)
    (hc : ContinuousOn g (Icc s T))
    (hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r)
    (hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r-s) ^ (β-1))
    (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    |g v - g u| ≤ (C / β) * ((v-s)^β - (u-s)^β) := by
  have hdv (r : ℝ) (hr : r ∈ Ioo u v) :
      HasDerivAt (fun r : ℝ => (C / β) * (r-s)^β) (C * (r-s)^(β-1)) r := by
    have hp := (((hasDerivAt_id r).sub_const s).rpow_const (p := β)
      (Or.inl (ne_of_gt (sub_pos.mpr (hsu.trans_lt hr.1))))).const_mul (C / β)
    simp only [id_eq] at hp
    convert hp using 1
    field_simp [hβ.ne']
  have hi := abs_sub_le_of_deriv_comparison huv
    (hc.mono (Icc_subset_Icc hsu hvT))
    (continuousOn_const.mul ((continuous_id.sub continuous_const).continuousOn.rpow_const
      (fun _ _ => Or.inr hβ.le)))
    (fun r hr => hd r ⟨hsu.trans_lt hr.1, hr.2.le.trans hvT⟩)
    hdv (fun r hr => hb r ⟨hsu.trans_lt hr.1, hr.2.le.trans hvT⟩)
  change |g v - g u| ≤ (C / β) * (v-s)^β - (C / β) * (u-s)^β at hi
  nlinarith [hi]

/-- A fractional power has an integrable secant bound measured from a positive base point. -/
theorem abs_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hx : 0 ≤ x) (hy : 0 < y) :
    |x^β - y^β| ≤ y^(β-1) * |x-y| := by
  have hyid : y^β = y * y^(β-1) := by
    rw [Real.rpow_sub_one hy.ne']
    field_simp
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst x
    rw [Real.zero_rpow hβ.ne', zero_sub, abs_neg,
      abs_of_nonneg (Real.rpow_nonneg hy.le _), zero_sub, abs_neg, abs_of_pos hy, hyid]
    exact le_of_eq (mul_comm _ _)
  have hxid : x^β = x * x^(β-1) := by
    rw [Real.rpow_sub_one hx0.ne']
    field_simp
  rcases le_total x y with hxy | hyx
  · have hp := Real.rpow_le_rpow hx hxy hβ.le
    have hq := Real.rpow_le_rpow_of_nonpos hx0 hxy (sub_nonpos.mpr hβ1)
    rw [abs_of_nonpos (sub_nonpos.mpr hp), abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hm := mul_le_mul_of_nonneg_left hq hx
    rw [hxid, hyid]
    nlinarith [hm]
  · have hp := Real.rpow_le_rpow hy.le hyx hβ.le
    have hq := Real.rpow_le_rpow_of_nonpos hy hyx (sub_nonpos.mpr hβ1)
    rw [abs_of_nonneg (sub_nonneg.mpr hp), abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hm := mul_le_mul_of_nonneg_left hq hx
    rw [hxid, hyid]
    nlinarith [hm]

/-- The same bound survives clipping at zero, from either side of the base point. -/
theorem abs_clipped_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hy : y ≠ 0) :
    |(max x 0)^β - (max y 0)^β| ≤ |y|^(β-1) * |x-y| := by
  have hb : 0 ≤ |y|^(β-1) := Real.rpow_nonneg (abs_nonneg _) _
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · rw [max_eq_right hyneg.le, Real.zero_rpow hβ.ne', sub_zero,
      abs_of_nonneg (Real.rpow_nonneg (le_max_right x 0) _), abs_of_neg hyneg]
    by_cases hx : x ≤ 0
    · simp only [max_eq_right hx, Real.zero_rpow hβ.ne']
      exact mul_nonneg (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) _) (abs_nonneg _)
    have hxpos : 0 < x := lt_of_not_ge hx
    rw [max_eq_left hxpos.le, abs_of_pos (sub_pos.mpr (hyneg.trans hxpos))]
    rcases le_total x (-y) with hxy | hyx
    · have hp := Real.rpow_le_rpow hxpos.le hxy hβ.le
      have he : (-y)^β = (-y) * (-y)^(β-1) := by
        rw [Real.rpow_sub_one (neg_ne_zero.mpr hy)]
        field_simp
      rw [he] at hp
      have hq := mul_nonneg hxpos.le (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) (β-1))
      nlinarith
    · have hp := Real.rpow_le_rpow_of_nonpos (neg_pos.mpr hyneg) hyx (sub_nonpos.mpr hβ1)
      have he : x^β = x * x^(β-1) := by
        rw [Real.rpow_sub_one hxpos.ne']
        field_simp
      rw [he]
      have hq := mul_le_mul_of_nonneg_left hp hxpos.le
      have hz := mul_nonneg (neg_nonneg.mpr hyneg.le)
        (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) (β-1))
      nlinarith
  · rw [max_eq_left hypos.le, abs_of_pos hypos]
    have hh := abs_rpow_sub_le hβ hβ1 (le_max_right x 0) hypos
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hypos.le _)
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx]
    · have hx' : x < 0 := lt_of_not_ge hx
      rw [max_eq_right hx'.le, zero_sub, abs_neg, abs_of_pos hypos,
        abs_of_neg (sub_neg.mpr (hx'.trans hypos))]
      linarith

/-- The singularity of the secant majorant is integrable on either side of its base point. -/
theorem intervalIntegrable_abs_sub_rpow {β T t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume 0 T := by
  have hl : IntervalIntegrable (fun s : ℝ => (t-s)^(β-1)) volume 0 t := by
    simpa only [sub_zero, sub_self] using
      ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t)
        (r := β-1) (by linarith)).comp_sub_left t).symm
  have hr : IntervalIntegrable (fun s : ℝ => (s-t)^(β-1)) volume t T := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := T-t)
        (r := β-1) (by linarith)).comp_sub_right t
  have hl' : IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume 0 t := by
    apply hl.congr
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    simp only [abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hr' : IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume t T := by
    apply hr.congr
    intro s hs
    rw [uIoc_of_le ht.2] at hs
    simp only [abs_of_nonpos (sub_nonpos.mpr hs.1.le), neg_sub]
  exact hl'.trans hr'

/-- A power bound for the derivative supplies a common majorant for clipped secants. -/
theorem clipped_secant_le_of_deriv_rpow_bound
    {g g' : ℝ → ℝ} {s T r t C β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hC : 0 ≤ C) (hs : s ≤ T) (hr : r ≤ T) (ht : t ≤ T) (hst : t ≠ s)
    (hc : ContinuousOn g (Icc s T))
    (hd : ∀ z ∈ Ioc s T, HasDerivAt g (g' z) z)
    (hb : ∀ z ∈ Ioc s T, |g' z| ≤ C * (z-s)^(β-1)) :
    |g (max r s) - g (max t s)| ≤ (C / β) * |t-s|^(β-1) * |r-t| := by
  have hCβ : 0 ≤ C / β := div_nonneg hC hβ.le
  have hinc (a b : ℝ) (ha : a ∈ Icc s T) (hb' : b ∈ Icc s T) :
      |g a - g b| ≤ (C / β) * |(a-s)^β - (b-s)^β| := by
    rcases le_total a b with hab | hba
    · have hp := Real.rpow_le_rpow (sub_nonneg.mpr ha.1) (sub_le_sub_right hab s) hβ.le
      rw [abs_sub_comm (g a) (g b), abs_sub_comm ((a-s)^β) ((b-s)^β),
        abs_of_nonneg (sub_nonneg.mpr hp)]
      exact abs_sub_le_rpow_of_deriv_bound hβ hc hd hb ha.1 hab hb'.2
    · have hp := Real.rpow_le_rpow (sub_nonneg.mpr hb'.1) (sub_le_sub_right hba s) hβ.le
      rw [abs_of_nonneg (sub_nonneg.mpr hp)]
      exact abs_sub_le_rpow_of_deriv_bound hβ hc hd hb hb'.1 hba ha.2
  have hi := hinc (max r s) (max t s)
    ⟨le_max_right _ _, max_le hr hs⟩ ⟨le_max_right _ _, max_le ht hs⟩
  have hp := abs_clipped_rpow_sub_le (x := r-s) (y := t-s) hβ hβ1
    (sub_ne_zero.mpr hst)
  have he (z : ℝ) : max z s - s = max (z-s) 0 := by
    rw [← max_sub_sub_right, sub_self]
  rw [he r, he t] at hi
  have he' : r-s-(t-s) = r-t := by ring
  rw [he'] at hp
  exact hi.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hCβ)

/-- The Leibniz rule on a closed time interval under an integrable diagonal power singularity. -/
theorem hasDerivWithinAt_integral_moving_limit
    {F D : ℝ → ℝ → ℝ} {b T t C β : ℝ} (ht : t ∈ Icc 0 T)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1})
    (hdiag : F t t = b)
    (hderiv : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T,
      HasDerivAt (fun ρ => F ρ s) (D r s) r)
    (hbound : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T, |D r s| ≤ C * (r-s)^(β-1)) :
    HasDerivWithinAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, F r s)
      (b + ∫ s in (0 : ℝ)..t, D t s) (Icc 0 T) t := by
  apply hasDerivWithinAt_integral_moving_limit_of_secants ht hcont hdiag
    (fun s hs => hderiv s ⟨hs.1.le, hs.2.le.trans ht.2⟩ t ⟨hs.2, ht.2⟩)
  refine ⟨fun s => (C / β) * |t-s|^(β-1), ?_, ?_⟩
  · exact ((intervalIntegrable_abs_sub_rpow hβ ht).const_mul (C / β)).1
  · filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc 0 T)).ae_ne t] with s hs hst
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    have hc : ContinuousOn (fun r => F r s) (Icc s T) :=
      hcont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun z hz => ⟨hsT, ⟨hs.1.le.trans hz.1, hz.2⟩, hz.1⟩)
    simpa only [Real.norm_eq_abs] using
      clipped_secant_le_of_deriv_rpow_bound hβ hβ1 hC hs.2 hr.2 ht.2 hst.symm
        hc (hderiv s hsT) (hbound s hsT)

local notation "E" => Poincare.ClosedSmoothModel 3
open HeatDuhamelHeatEquation

/-- The existing Hessian estimate supplies the scalar time-derivative majorant. -/
theorem exists_heat_integrand_deriv_bound {α T M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x-y‖^α)
    (x : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T,
      |deriv (fun ρ => heatSolution (ρ-s) (fun y => f (s,y)) x) r| ≤
        C * (r-s)^(α/2-1) := by
  obtain ⟨A, hA, hAb⟩ :=
    HeatDuhamelSpatialHolderHessian.exists_heat_hessian_holder_bound hα hα1
  refine ⟨3 * A * K, by positivity, ?_⟩
  intro s hs r hr
  have hc : Continuous (fun y : E => f (s,y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hH := hAb (sub_pos.mpr hr.1) hK0 hc.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hM s hs) (hK s hs) x
  rw [(hasDerivAt_heat_integrand hs hr.1 hf hM x).deriv, laplacian_eq_hessian_trace]
  calc
    |∑ i : Fin 3, fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤
      ∑ i : Fin 3, ‖fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ :=
      by
        simpa only [Real.norm_eq_abs] using
          (norm_sum_le Finset.univ (fun i : Fin 3 =>
            fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x
              (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)))
    _ ≤ ∑ _i : Fin 3, A * K * (r-s)^(α/2-1) := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans _ hH
      simpa only [OrthonormalBasis.norm_eq_one, mul_one] using
        ContinuousLinearMap.le_opNorm₂
          (fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)
    _ = (3 * A * K) * (r-s)^(α/2-1) := by simp; ring

/-- The Duhamel solution satisfies the frozen inhomogeneous heat equation. -/
theorem duhamel_solves_heat_equation :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  (∀ x : E, u 0 x = 0) ∧
  ∀ t ∈ Icc 0 T, ∀ x : E,
    HasDerivWithinAt (fun r : ℝ => u r x)
      (f (t, x) + ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (u t)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (Icc 0 T) t := by
  intro α hα hα1 T hT hT1 f M K hM0 hK0 hf hM hK
  dsimp only
  refine ⟨fun x => duhamel_zero f x, ?_⟩
  intro t ht x
  rw [← laplacian_eq_hessian_trace]
  rw [← (duhamel_time_derivative_integral hα hα1 ht hf hM hK x).2]
  let F : ℝ → ℝ → ℝ := fun r s => if r-s = 0 then f (s,x)
    else heatSolution (r-s) (fun y => f (s,y)) x
  have hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1} :=
    (continuousOn_heat_integrand_extension hf hM x).comp
      ((continuous_fst.sub continuous_snd).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨sub_nonneg.mpr hp.2.2, hp.1⟩)
  have hd : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T,
      HasDerivAt (fun ρ => F ρ s)
        (deriv (fun ρ => heatSolution (ρ-s) (fun y => f (s,y)) x) r) r := by
    intro s hs r hr
    have hd0 := (hasDerivAt_heat_integrand hs hr.1 hf hM x).differentiableAt.hasDerivAt
    apply hd0.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr.1] with ρ hρ
    simp only [F, if_neg (ne_of_gt (sub_pos.mpr (show s < ρ from hρ)))]
  obtain ⟨C, hC, hCb⟩ := exists_heat_integrand_deriv_bound hα hα1 hK0 hf hM hK x
  have hsolve := hasDerivWithinAt_integral_moving_limit
    (F := F) (b := f (t,x))
    (D := fun r s => deriv (fun ρ => heatSolution (ρ-s) (fun y => f (s,y)) x) r)
    ht (β := α / 2) (by linarith) (by linarith) hC hc (by simp only [F, sub_self, if_true]) hd hCb
  apply hsolve.congr_of_mem _ ht
  intro r hr
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hr.1, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp only [F, if_neg (ne_of_gt (sub_pos.mpr hs.2))]

end Poincare.MovingLimitLeibniz

end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval Laplacian

namespace Poincare.DuhamelSolutionOperatorBound

local notation "E" => Poincare.ClosedSmoothModel 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

open HeatDuhamelHessianDifferentiation HeatDuhamelHeatEquation ParabolicHolder

/-- The three coordinate diagonal evaluations are bounded by three operator norms. -/
theorem abs_trace_le (A : E →L[ℝ] E →L[ℝ] ℝ) :
    |∑ i : Fin 3, A (e i) (e i)| ≤ 3 * ‖A‖ := by
  calc
    |∑ i : Fin 3, A (e i) (e i)| ≤ ∑ i : Fin 3, ‖A (e i) (e i)‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le Finset.univ (fun i : Fin 3 => A (e i) (e i))
    _ ≤ ∑ _i : Fin 3, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [OrthonormalBasis.norm_eq_one, mul_one] using
        ContinuousLinearMap.le_opNorm₂ A (e i) (e i)
    _ = 3 * ‖A‖ := by simp

/-- The within-interval time derivative has the expected sup estimate. -/
theorem duhamel_time_derivative_bound :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    ∀ t ∈ Icc 0 T, ∀ x : E,
      HasDerivWithinAt (fun r => u r x) (f (t,x) + (Δ (u t)) x) (Icc 0 T) t ∧
      |f (t,x) + (Δ (u t)) x| ≤ M + 3 * C * K * t ^ (α / 2) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro t ht x
  have hd := (MovingLimitLeibniz.duhamel_solves_heat_equation
    α hα hα1 T hT hT1 f M K hM hK hf hfM hfK).2 t ht x
  rw [← laplacian_eq_hessian_trace] at hd
  refine ⟨hd, ?_⟩
  have hb := ((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht x).2.2.2
  rw [laplacian_eq_hessian_trace]
  calc
    _ ≤ |f (t,x)| + 3 * ‖fderiv ℝ (fderiv ℝ (fun z : E =>
        ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) z)) x‖ :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_trace_le _))
    _ ≤ M + 3 * (C * K * t ^ (α / 2)) :=
      add_le_add (hfM t ht x) (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = M + 3 * C * K * t ^ (α / 2) := by ring

/-- Tracing the parabolic Hessian increment controls the time derivative increment. -/
theorem duhamel_time_derivative_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    HasHolderBound α (cylinder T) f K →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    HasHolderBound α (cylinder T) (fun p => f p + (Δ (u p.1)) p.2)
      (K + 3 * C * K) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ :=
    DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder α hα hα1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using
      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  dsimp only
  intro p hp q hq
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  have hb := hCb T hT hT1 f M K hM hK hf hfM hspace p hp q hq
  have htrace : |(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2| ≤
      3 * ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 -
        fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
    simpa only [laplacian_eq_hessian_trace, ContinuousLinearMap.sub_apply,
      Finset.sum_sub_distrib] using abs_trace_le
        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
  change ‖(f p + (Δ (u p.1)) p.2) - (f q + (Δ (u q.1)) q.2)‖ ≤ _
  rw [add_sub_add_comm]
  calc
    _ ≤ ‖f p - f q‖ + ‖(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2‖ := norm_add_le _ _
    _ ≤ K * parabolicDist p q ^ α + 3 * (C * K * parabolicDist p q ^ α) :=
      add_le_add (hfK p hp q hq)
        (htrace.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
    _ = (K + 3 * C * K) * parabolicDist p q ^ α := by ring

/-- Integrating the gradient kernel gives the sharp square-root time factor. -/
theorem duhamel_gradient_bound {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
    ‖fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t-s) (fun y => f (s,y)) z) x‖ ≤
      2 * M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * Real.sqrt t := by
  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
  let A := M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖)
  have hb : ‖∫ s in (0 : ℝ)..t,
      fderiv ℝ (heatSolution (t-s) (fun y => f (s,y))) x‖ ≤
      ∫ s in (0 : ℝ)..t, A * (t-s) ^ (-(1/2 : ℝ)) := by
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
      ← restrict_Ioo_eq_restrict_Ioc]
    apply MeasureTheory.norm_integral_le_of_norm_le
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
        (intervalIntegrable_gradient_majorant t A))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s,y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) hc.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hM s hsT) x
  have he := HeatDuhamelSpatialHolderHessian.integral_hessian_majorant zero_lt_one t A
  norm_num only [div_one, show (1 : ℝ) / 2 - 1 = -(1/2 : ℝ) by norm_num] at he
  rw [he] at hb
  simpa [A, Real.sqrt_eq_rpow, mul_assoc, mul_left_comm, mul_comm] using hb

/-- A uniform time-derivative bound controls all value increments and the initial trace. -/
theorem duhamel_value_time_estimates :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    (∀ t ∈ Icc 0 T, ∀ x : E, |u t x| ≤ t * (M + 3 * C * K * T ^ (α/2))) ∧
    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x : E,
      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s|) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  have hd := hCb T hT hT1 f M K hM hK hf hfM hfK
  have hb (r : ℝ) (hr : r ∈ Icc 0 T) (x : E) :
      ‖f (r,x) + (Δ (u r)) x‖ ≤ M + 3 * C * K * T ^ (α/2) := by
    apply (hd r hr x).2.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.1 hr.2 (by linarith)) (by positivity))
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Icc 0 T) (x : E) :
      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r hr => (hd r hr x).1) (fun r hr => hb r hr x) (convex_Icc (0 : ℝ) T) hs ht
  refine ⟨?_, hi⟩
  intro t ht x
  simpa [u, abs_of_nonneg ht.1, mul_comm] using hi t ht 0 ⟨le_rfl, hT.le⟩ x

/-- Bounded Lipschitz increments give every intermediate Hölder exponent. -/
theorem holder_of_bounded_lipschitz {F : Type*} [NormedAddCommGroup F]
    {α A B : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {g : E → F} (hg : ∀ x, ‖g x‖ ≤ A)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ B * ‖x-y‖) (x y : E) :
    ‖g x - g y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
  by_cases hr : ‖x-y‖ ≤ 1
  · have hp : ‖x-y‖ ≤ ‖x-y‖ ^ α := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x-y)) hr hα hα1
    exact (hlip x y).trans ((mul_le_mul_of_nonneg_left hp hB).trans
      (mul_le_mul_of_nonneg_right (by linarith : B ≤ 2*A+B)
        (Real.rpow_nonneg (norm_nonneg _) _)))
  · have hp : 1 ≤ ‖x-y‖ ^ α := Real.one_le_rpow (le_of_not_ge hr) hα
    calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2*A := by linarith [hg x, hg y]
      _ ≤ (2*A+B) * ‖x-y‖ ^ α := by
        calc
          2*A ≤ 2*A+B := by linarith
          _ ≤ (2*A+B) * ‖x-y‖ ^ α := le_mul_of_one_le_right (by positivity) hp

/-- The gradient is spatially Hölder with a constant uniform on short time intervals. -/
theorem duhamel_gradient_spatial_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    ∀ t ∈ Icc 0 T, ∀ x y : E,
      ‖fderiv ℝ (u t) x - fderiv ℝ (u t) y‖ ≤ C * (M+K) * ‖x-y‖ ^ α := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨4*J+C, by positivity, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro t ht x y
  let u : E → ℝ := fun z => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun w => f (s,w)) z
  have hg (z : E) : ‖fderiv ℝ u z‖ ≤ 2*M*J :=
    (duhamel_gradient_bound ht hf hfM z).trans
      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
  have hh (z : E) : ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ C*K :=
    (((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht z).2.2.2).trans
      (mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)))
  have hdiff : Differentiable ℝ (fderiv ℝ u) :=
    ((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
      (m := 1) (by norm_num)).differentiable_one
  have hlip (a b : E) : ‖fderiv ℝ u a - fderiv ℝ u b‖ ≤ C*K*‖a-b‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
      (fun z _ => hh z) (convex_univ : Convex ℝ (univ : Set E)) (mem_univ b) (mem_univ a)
  have hb := holder_of_bounded_lipschitz hα.le hα1.le
    (by positivity : 0 ≤ 2*M*J) (by positivity : 0 ≤ C*K) hg hlip x y
  exact hb.trans (mul_le_mul_of_nonneg_right
    (by nlinarith [mul_nonneg hJ hK, mul_nonneg hC.le hM] :
      2*(2*M*J)+C*K ≤ (4*J+C)*(M+K)) (Real.rpow_nonneg (norm_nonneg _) _))

/-- Value increments obey a parabolic Hölder bound uniform for times at most one. -/
theorem duhamel_value_parabolic_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    HasHolderBound α (cylinder T)
      (fun p : ℝ × E => ∫ s in (0 : ℝ)..p.1,
        heatSolution (p.1-s) (fun y => f (s,y)) p.2) (C * (M+K)) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_value_time_estimates α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨3+9*C+2*J, by positivity, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  let D := M+3*C*K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hd : M+3*C*K*T^(α/2) ≤ D := by
    exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one hT.le hT1 (by linarith)))
  have hv := hCb T hT hT1 f M K hM hK hf hfM hfK
  have hu (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖u t x‖ ≤ D := by
    exact (hv.1 t ht x).trans ((mul_le_mul_of_nonneg_left hd ht.1).trans
      (mul_le_of_le_one_left hD (ht.2.trans hT1)))
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖fderiv ℝ (u t) x‖ ≤ 2*M*J :=
    (duhamel_gradient_bound ht hf hfM x).trans
      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
  intro p hp q hq
  have hs : ‖u p.1 p.2 - u p.1 q.2‖ ≤ (2*D+2*M*J)*‖p.2-q.2‖^α := by
    apply holder_of_bounded_lipschitz hα.le hα1.le hD (by positivity) (hu p.1 hp.1)
    intro a b
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hasFDerivAt_duhamel hp.1 hf hfM z).differentiableAt)
      (fun z _ => hg p.1 hp.1 z) (convex_univ : Convex ℝ (univ : Set E))
      (mem_univ b) (mem_univ a)
  have hab : |p.1-q.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2],
    by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]⟩
  have htp : |p.1-q.1| ≤ parabolicDist p q ^ α := by
    calc
      |p.1-q.1| ≤ |p.1-q.1|^(α/2) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
          (abs_nonneg (p.1-q.1)) hab (by linarith : 0 ≤ α/2) (by linarith : α/2 ≤ 1)
      _ = (Real.sqrt |p.1-q.1|)^α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have ht : ‖u p.1 q.2 - u q.1 q.2‖ ≤ D * parabolicDist p q ^ α :=
    (hv.2 p.1 hp.1 q.1 hq.1 q.2).trans
      ((mul_le_mul_of_nonneg_right hd (abs_nonneg _)).trans (mul_le_mul_of_nonneg_left htp hD))
  calc
    ‖u p.1 p.2 - u q.1 q.2‖ ≤ ‖u p.1 p.2 - u p.1 q.2‖ + ‖u p.1 q.2 - u q.1 q.2‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ (2*D+2*M*J)*parabolicDist p q ^ α + D*parabolicDist p q ^ α :=
      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity))) ht
    _ ≤ (3+9*C+2*J)*(M+K)*parabolicDist p q ^ α := by
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (parabolicDist_nonneg _ _) _)
      dsimp [D]
      nlinarith [mul_nonneg hC.le hM, mul_nonneg hJ hK]

/-- A difference of bounded data has the same gradient kernel estimate. -/
theorem gradient_heatSolution_sub_bound {t M N L : ℝ} (ht : 0 < t)
    {f g : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (hfM : ∀ y, ‖f y‖ ≤ M)
    (hgN : ∀ y, ‖g y‖ ≤ N) (hL : ∀ y, ‖f y - g y‖ ≤ L) (x : E) :
    ‖fderiv ℝ (heatSolution t f) x - fderiv ℝ (heatSolution t g) x‖ ≤
      L * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * t ^ (-(1/2 : ℝ)) := by
  have hi := integrable_smul_fderiv_heatKernel_sub ht hf hfM x
  have hj := integrable_smul_fderiv_heatKernel_sub ht hg hgN x
  rw [(heatSolution_hasFDerivAt ht hf hfM x).fderiv,
    (heatSolution_hasFDerivAt ht hg hgN x).fderiv, ← integral_sub hi hj]
  have he : (fun y : E => f y • fderiv ℝ (heatKernel t) (x-y) -
      g y • fderiv ℝ (heatKernel t) (x-y)) =
      fun y => (f y - g y) • fderiv ℝ (heatKernel t) (x-y) := by
    ext y v
    simp [sub_smul]
  rw [he]
  have hb := norm_gradient_heatSolution_le ht (hf.sub hg) hL x
  rw [(heatSolution_hasFDerivAt ht (hf.sub hg) hL x).fderiv] at hb
  exact hb

/-- Reversing Duhamel time keeps the gradient kernel fixed when comparing forcing times. -/
theorem duhamel_gradient_reversed {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
    fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t-s) (fun y => f (s,y)) z) x =
      ∫ s in (0 : ℝ)..t, fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x := by
  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
  have he := intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x)
    (a := 0) (b := t) t
  simpa only [sub_sub_cancel, sub_self, sub_zero] using he

/-- The inverse square-root majorant controls an arbitrary nonnegative time interval. -/
theorem norm_integral_inverse_sqrt_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {a b A : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A)
    {g : ℝ → F} (hg : ∀ r ∈ Ioo a b, ‖g r‖ ≤ A * r ^ (-(1/2 : ℝ))) :
    ‖∫ r in a..b, g r‖ ≤ 2*A*Real.sqrt (b-a) := by
  have hb : 0 ≤ b := ha.trans hab
  have hi : IntervalIntegrable (fun r : ℝ => A * r ^ (-(1/2 : ℝ))) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))).const_mul A
  have hbound : ‖∫ r in a..b, g r‖ ≤ ∫ r in a..b, A * r ^ (-(1/2 : ℝ)) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      ← restrict_Ioo_eq_restrict_Ioc]
    apply MeasureTheory.norm_integral_le_of_norm_le
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hg r hr
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))] at hbound
  norm_num only [show -(1/2 : ℝ)+1 = 1/2 by norm_num] at hbound
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hbound
  have hs : Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b-a) := by
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have h3 := Real.sq_sqrt (sub_nonneg.mpr hab)
    have h4 := Real.sqrt_nonneg a
    have h5 := Real.sqrt_nonneg b
    have h6 := Real.sqrt_nonneg (b-a)
    nlinarith [mul_nonneg h4 h6]
  calc
    _ ≤ A * ((Real.sqrt b - Real.sqrt a) / (1/2)) := hbound
    _ = 2*A*(Real.sqrt b - Real.sqrt a) := by ring
    _ ≤ 2*A*Real.sqrt (b-a) := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Reversed time separates a forcing increment from a short gradient tail. -/
theorem duhamel_gradient_time_holder_of_le {α T s t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT1 : T ≤ 1)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t)
    (hM : 0 ≤ M) (hK : 0 ≤ K) {f : ℝ × E → ℝ}
    (hf : ContinuousOn f (cylinder T))
    (hfM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r,y)| ≤ M)
    (hfK : HasHolderBound α (cylinder T) f K) (x : E) :
    let u : ℝ → E → ℝ := fun r z =>
      ∫ v in (0 : ℝ)..r, heatSolution (r-v) (fun y => f (v,y)) z
    ‖fderiv ℝ (u t) x - fderiv ℝ (u s) x‖ ≤
      2 * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * (M+K) * (t-s)^(α/2) := by
  dsimp only
  rw [duhamel_gradient_reversed ht hf hfM, duhamel_gradient_reversed hs hf hfM]
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  let v : ℝ → ℝ → E →L[ℝ] ℝ := fun a r =>
    fderiv ℝ (heatSolution r (fun y => f (a-r,y))) x
  have hi (a : ℝ) (ha : a ∈ Icc 0 T) : IntervalIntegrable (v a) volume 0 a := by
    have h := (intervalIntegrable_gradient_heatSolution_time ha hf hfM x).comp_sub_left a
    simpa only [v, sub_zero, sub_self, sub_sub_cancel] using h.symm
  have hsub0 : uIcc (0 : ℝ) s ⊆ uIcc 0 t := by
    simpa only [uIcc_of_le hs.1, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl hst
  have hsub1 : uIcc s t ⊆ uIcc 0 t := by
    simpa only [uIcc_of_le hst, uIcc_of_le ht.1] using Icc_subset_Icc hs.1 le_rfl
  have hit0 := (hi t ht).mono_set hsub0
  have hit1 := (hi t ht).mono_set hsub1
  have hc (a : ℝ) (ha : a ∈ Icc 0 T) (r : ℝ) (hr : r ∈ Icc 0 a) :
      Continuous (fun y : E => f (a-r,y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨⟨by linarith [hr.2], by linarith [hr.1, ha.2]⟩, mem_univ y⟩)
  have hδ : 0 ≤ t-s := sub_nonneg.mpr hst
  have hb0 : ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ ≤
      2 * (K * (t-s)^(α/2) * J) * Real.sqrt s := by
    simpa only [sub_zero] using norm_integral_inverse_sqrt_le
      (a := 0) (b := s) le_rfl hs.1 (by positivity : 0 ≤ K*(t-s)^(α/2)*J)
      (g := fun r => v t r - v s r) (by
        intro r hr
        have hrt : r ∈ Icc 0 t := ⟨hr.1.le, hr.2.le.trans hst⟩
        have hrs : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le⟩
        apply gradient_heatSolution_sub_bound hr.1 (hc t ht r hrt).aestronglyMeasurable
          (hc s hs r hrs).aestronglyMeasurable
          (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y)
          (fun y => hfM (s-r) ⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩ y)
        intro y
        have h := hfK (t-r,y) ⟨⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩, mem_univ y⟩
          (s-r,y) ⟨⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩, mem_univ y⟩
        simpa [parabolicDist, sub_sub_sub_cancel_right, abs_of_nonneg (sub_nonneg.mpr hst),
          Real.sqrt_eq_rpow, ← Real.rpow_mul (sub_nonneg.mpr hst), mul_comm, div_eq_mul_inv] using h)
  have hb1 : ‖∫ r in s..t, v t r‖ ≤ 2*(M*J)*Real.sqrt (t-s) := by
    apply norm_integral_inverse_sqrt_le hs.1 hst (by positivity)
    intro r hr
    have hrt : r ∈ Icc 0 t := ⟨hs.1.trans hr.1.le, hr.2.le⟩
    exact norm_gradient_heatSolution_le (lt_of_le_of_lt hs.1 hr.1)
      (hc t ht r hrt).aestronglyMeasurable
      (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y) x
  have hδ1 : t-s ≤ 1 := by linarith [ht.2, hs.1]
  have hpow : Real.sqrt (t-s) ≤ (t-s)^(α/2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 (by linarith) (by linarith)
  change ‖(∫ r in (0 : ℝ)..t, v t r) - ∫ r in (0 : ℝ)..s, v s r‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hit0 hit1,
    add_sub_right_comm, ← intervalIntegral.integral_sub hit0 (hi s hs)]
  calc
    _ ≤ ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ + ‖∫ r in s..t, v t r‖ := norm_add_le _ _
    _ ≤ 2*(K*(t-s)^(α/2)*J)*Real.sqrt s + 2*(M*J)*Real.sqrt (t-s) := add_le_add hb0 hb1
    _ ≤ 2*(K*(t-s)^(α/2)*J) + 2*(M*J)*(t-s)^(α/2) :=
      add_le_add (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hs.2.trans hT1)))
        (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = 2*J*(M+K)*(t-s)^(α/2) := by ring

/-- Spatial interpolation and reversed-time integration give the full gradient estimate. -/
theorem duhamel_gradient_parabolic_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    HasHolderBound α (cylinder T) f K →
    HasHolderBound α (cylinder T)
      (fun p : ℝ × E => fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..p.1,
        heatSolution (p.1-s) (fun y => f (s,y)) z) p.2) (C * (M+K)) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_gradient_spatial_holder α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨C+2*J, by positivity, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using
      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  intro p hp q hq
  have hs := hCb T hT hT1 f M K hM hK hf hfM hspace p.1 hp.1 p.2 q.2
  have ht : ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ ≤
      2*J*(M+K)*|p.1-q.1|^(α/2) := by
    rcases le_total q.1 p.1 with hqp | hpq
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hqp)] using
        duhamel_gradient_time_holder_of_le hα hα1 hT1 hq.1 hp.1 hqp hM hK hf hfM hfK q.2
    · simpa only [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hpq), neg_sub] using
        duhamel_gradient_time_holder_of_le hα hα1 hT1 hp.1 hq.1 hpq hM hK hf hfM hfK q.2
  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have htp : |p.1-q.1|^(α/2) ≤ parabolicDist p q ^ α := by
    calc
      _ = (Real.sqrt |p.1-q.1|)^α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  calc
    ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u q.1) q.2‖ ≤
        ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u p.1) q.2‖ +
        ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ C*(M+K)*parabolicDist p q ^ α + 2*J*(M+K)*parabolicDist p q ^ α :=
      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity)))
        (ht.trans (mul_le_mul_of_nonneg_left htp (by positivity)))
    _ = (C+2*J)*(M+K)*parabolicDist p q ^ α := by ring

/-- Positive parabolic Hölder control implies continuity on the cylinder. -/
theorem continuousOn_of_hasHolderBound {F : Type*} [NormedAddCommGroup F]
    {α T K : ℝ} (hα : 0 < α) {g : ℝ × E → F}
    (hg : HasHolderBound α (cylinder T) g K) : ContinuousOn g (cylinder T) := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun q : ℝ × E => K * parabolicDist q p ^ α) := by
    dsimp [parabolicDist]
    fun_prop (disch := positivity)
  have hz : K * parabolicDist p p ^ α = 0 := by
    simp [parabolicDist, Real.zero_rpow hα.ne']
  have hlim : Filter.Tendsto (fun q => K * parabolicDist q p ^ α)
      (nhdsWithin p (cylinder T)) (nhds (K * parabolicDist p p ^ α)) :=
    hc.continuousAt.continuousWithinAt
  rw [hz] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun q => norm_nonneg (g q - g p))) _ hlim
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact hg q hq p hp

set_option maxHeartbeats 800000 in
/-- The constant-coefficient Duhamel solution is bounded in the full solution graph norm. -/
theorem exists_solution_graph_bound :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ p ∈ ParabolicHolder.cylinder («E» := E) T,
        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1
  obtain ⟨A, hA, hAb⟩ := duhamel_hessian_bound α hα hα1
  obtain ⟨B, hB, hBb⟩ := DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
  obtain ⟨D, hD, hDb⟩ := duhamel_time_derivative_holder α hα hα1
  obtain ⟨V, hV, hVb⟩ := duhamel_value_time_estimates α hα hα1
  obtain ⟨W, hW, hWb⟩ := duhamel_value_parabolic_holder α hα hα1
  obtain ⟨Q, hQ, hQb⟩ := duhamel_gradient_parabolic_holder α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨(1+3*V)+2*W+(1+3*C)+(1+3*D)+2*J+2*Q+A+B, by positivity, ?_⟩
  intro T hT hT1 f
  let N := ‖f‖
  have hN : 0 ≤ N := norm_nonneg f
  have hfH : HasHolderBound α (cylinder T) f N := ParabolicHolder.hasHolderBound f
  have hf : ContinuousOn f (cylinder T) := continuousOn_of_hasHolderBound hα hfH
  have hfM : ∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ N :=
    fun t _ x => ParabolicHolder.norm_le f (t,x)
  have hfK : ∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x)-f (t,y)| ≤ N*‖x-y‖^α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using hfH (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  let u : ℝ → E → ℝ := fun t x => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  let v : ℝ × E → ℝ := fun p => f p + (Δ (u p.1)) p.2
  let d : ℝ × E → E →L[ℝ] ℝ := fun p => fderiv ℝ (u p.1) p.2
  let dd : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2
  have hpow (t : ℝ) (ht : t ∈ Icc 0 T) : t^(α/2) ≤ 1 :=
    Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)
  have htime := hCb T hT hT1 f N N hN hN hf hfM hfK
  have hvalue := hVb T hT hT1 f N N hN hN hf hfM hfK
  have huB : ∀ p ∈ cylinder T, ‖u p.1 p.2‖ ≤ (1+3*V)*N := by
    intro p hp
    have hb : N+3*V*N*T^(α/2) ≤ (1+3*V)*N := by
      have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*V*N)
        (hpow T ⟨hT.le, le_rfl⟩)
      nlinarith
    exact (hvalue.1 p.1 hp.1 p.2).trans ((mul_le_mul_of_nonneg_left hb hp.1.1).trans
      (mul_le_of_le_one_left (by positivity) (hp.1.2.trans hT1)))
  have hvB : ∀ p ∈ cylinder T, ‖v p‖ ≤ (1+3*C)*N := by
    intro p hp
    have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*C*N) (hpow p.1 hp.1)
    have hb := (htime p.1 hp.1 p.2).2
    change |f p + (Δ (u p.1)) p.2| ≤ _
    nlinarith
  have hdB : ∀ p ∈ cylinder T, ‖d p‖ ≤ 2*J*N := by
    intro p hp
    have h := (duhamel_gradient_bound hp.1 hf hfM p.2).trans
      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hp.1.2.trans hT1)))
    simpa only [d, J, mul_comm, mul_left_comm, mul_assoc] using h
  have hddB : ∀ p ∈ cylinder T, ‖dd p‖ ≤ A*N := by
    intro p hp
    exact (((hAb T hT hT1 f N N hN hN hf hfM hfK).2 p.1 hp.1 p.2).2.2.2).trans
      (mul_le_of_le_one_right (by positivity) (hpow p.1 hp.1))
  have huH : HasHolderBound α (cylinder T) (fun p => u p.1 p.2) (2*W*N) := by
    convert hWb T hT hT1 f N N hN hN hf hfM hfK using 1
    ring
  have hvH : HasHolderBound α (cylinder T) v ((1+3*D)*N) := by
    convert hDb T hT hT1 f N N hN hN hf hfM hfH using 1
    ring
  have hdH : HasHolderBound α (cylinder T) d (2*Q*N) := by
    convert hQb T hT hT1 f N N hN hN hf hfM hfH using 1
    ring
  have hddH : HasHolderBound α (cylinder T) dd (B*N) := hBb T hT hT1 f N N hN hN hf hfM hfK
  have liftB {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
      (hb : ∀ p ∈ cylinder T, ‖g p‖ ≤ b) :
      ∀ p ∈ cylinder T, ‖(cylinder T).indicator g p‖ ≤ b := by
    intro p hp
    simpa only [indicator_of_mem hp] using hb p hp
  have liftH {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
      (hb : HasHolderBound α (cylinder T) g b) :
      HasHolderBound α (cylinder T) ((cylinder T).indicator g) b := by
    intro p hp q hq
    simpa only [indicator_of_mem hp, indicator_of_mem hq] using hb p hp q hq
  let iu := (cylinder T).indicator (fun p : ℝ × E => u p.1 p.2)
  let iv := (cylinder T).indicator v
  let idu := (cylinder T).indicator d
  let iddu := (cylinder T).indicator dd
  have huS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => iu (t,z)) = u t := by
    funext z
    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
  have hdS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => idu (t,z)) = fderiv ℝ (u t) := by
    funext z
    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
  have hzero : ∀ x : E, iu (0,x) = 0 := by
    intro x
    rw [show iu (0,x) = u 0 x from congrFun (huS 0 ⟨le_rfl, hT.le⟩) x]
    exact intervalIntegral.integral_same
  have hdu : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z => iu (t,z)) (idu (t,x)) x := by
    intro t ht x
    rw [huS t ht]
    have hd0 : idu (t,x) = fderiv ℝ (u t) x := congrFun (hdS t ht) x
    rw [hd0]
    exact (hasFDerivAt_duhamel ht hf hfM x).differentiableAt.hasFDerivAt
  have hddu : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z => idu (t,z)) (iddu (t,x)) x := by
    intro t ht x
    rw [hdS t ht]
    change HasFDerivAt (fderiv ℝ (u t)) ((cylinder T).indicator dd (t,x)) x
    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
    exact (((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
      (m := 1) (by norm_num)).differentiable_one x).hasFDerivAt
  have hut : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasDerivWithinAt (fun s => iu (s,x)) (iv (t,x)) (Icc 0 T) t := by
    intro t ht x
    change HasDerivWithinAt _ ((cylinder T).indicator v (t,x)) _ _
    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
    exact ((htime t ht x).1).congr_of_mem (fun s hs => congrFun (huS s hs) x) ht
  let G : ParabolicSolutionGraph.Graph («E» := E) α T :=
    ParabolicSolutionGraph.ofDerivatives iu iv idu iddu
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB (fun p => u p.1 p.2) huB⟩ ⟨_, liftH (fun p => u p.1 p.2) huH⟩
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB v hvB⟩ ⟨_, liftH v hvH⟩
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB d hdB⟩ ⟨_, liftH d hdH⟩
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB dd hddB⟩ ⟨_, liftH dd hddH⟩
      hzero hdu hddu hut
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    change (cylinder T).indicator (fun q : ℝ × E => u q.1 q.2) p = u p.1 p.2
    exact indicator_of_mem hp _
  · have huN : ‖G.u‖ ≤ (1+3*V)*N+2*W*N :=
      norm_le_of_bounds G.u (by positivity) (by positivity) (liftB (fun p => u p.1 p.2) huB) (liftH (fun p => u p.1 p.2) huH)
    have hvN : ‖G.ut‖ ≤ (1+3*C)*N+(1+3*D)*N :=
      norm_le_of_bounds G.ut (by positivity) (by positivity) (liftB v hvB) (liftH v hvH)
    have hdN : ‖G.du‖ ≤ 2*J*N+2*Q*N :=
      norm_le_of_bounds G.du (by positivity) (by positivity) (liftB d hdB) (liftH d hdH)
    have hddN : ‖G.ddu‖ ≤ A*N+B*N :=
      norm_le_of_bounds G.ddu (by positivity) (by positivity) (liftB dd hddB) (liftH dd hddH)
    rw [ParabolicSolutionGraph.norm_eq]
    change ‖G.u‖+‖G.ut‖+‖G.du‖+‖G.ddu‖ ≤ _ * N
    nlinarith

end Poincare.DuhamelSolutionOperatorBound

end
end

section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Poincare.ParabolicSolutionGraph

/-- Values determine all derivatives, including at both time endpoints. -/
theorem Graph.ext_of_u {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α T : ℝ} (hT : 0 < T) {G H : Graph (E := E) α T} (hu : G.u = H.u) : G = H := by
  have hd : G.du = H.du := by
    apply ParabolicHolder.ext
    intro p hp
    have h := G.hasFDeriv p.1 hp.1 p.2
    rw [hu] at h
    exact h.unique (H.hasFDeriv p.1 hp.1 p.2)
  have hdd : G.ddu = H.ddu := by
    apply ParabolicHolder.ext
    intro p hp
    have h := G.hasFDeriv_du p.1 hp.1 p.2
    rw [hd] at h
    exact h.unique (H.hasFDeriv_du p.1 hp.1 p.2)
  have ht : G.ut = H.ut := by
    apply ParabolicHolder.ext
    intro p hp
    have h := G.hasDeriv_time p.1 hp.1 p.2
    rw [hu] at h
    exact (h.derivWithin (uniqueDiffOn_Icc hT p.1 hp.1)).symm.trans
      ((H.hasDeriv_time p.1 hp.1 p.2).derivWithin (uniqueDiffOn_Icc hT p.1 hp.1))
  cases G
  cases H
  cases hu
  cases ht
  cases hd
  cases hdd
  rfl

end Poincare.ParabolicSolutionGraph

namespace Poincare.DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3

open ParabolicHolder DuhamelSolutionOperatorBound

/-- A short-time bound depending only on the exponent. -/
def boundConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ :=
  Classical.choose (exists_solution_graph_bound α hα hα1)

/-- The chosen constant retains the complete landed existence estimate. -/
theorem boundConstant_spec (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < boundConstant α hα hα1 ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ f : Y («E» := E) α T ℝ, ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ p ∈ cylinder T, G.u p =
        ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2) ∧
      ‖G‖ ≤ boundConstant α hα hα1 * ‖f‖ :=
  Classical.choose_spec (exists_solution_graph_bound α hα hα1)

/-- The unique graph selected by the landed existence theorem. -/
def duhamelGraph (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) : ParabolicSolutionGraph.Graph («E» := E) α T :=
  Classical.choose ((boundConstant_spec α hα hα1).2 T hT hT1 f)

/-- The selected graph has the integral values and the uniform norm estimate. -/
theorem duhamelGraph_spec (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
    (∀ p ∈ cylinder T, (duhamelGraph α T hα hα1 hT hT1 f).u p =
      ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2) ∧
    ‖duhamelGraph α T hα hα1 hT hT1 f‖ ≤ boundConstant α hα hα1 * ‖f‖ :=
  Classical.choose_spec ((boundConstant_spec α hα hα1).2 T hT hT1 f)

/-- The Duhamel integral is additive for parabolic Hölder data. -/
theorem duhamel_integral_add {α T t : ℝ} (hα : 0 < α) (ht : t ∈ Icc 0 T)
    (f g : Y («E» := E) α T ℝ) (x : E) :
    (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => (f+g) (s,y)) x) =
      (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x) +
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => g (s,y)) x := by
  have hc (v : Y («E» := E) α T ℝ) : ContinuousOn v (cylinder T) :=
    continuousOn_of_hasHolderBound hα (hasHolderBound v)
  have hi (v : Y («E» := E) α T ℝ) :=
    HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time ht (hc v)
      (fun s _ y => ParabolicHolder.norm_le v (s,y)) x
  rw [← intervalIntegral.integral_add (hi f) (hi g)]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have he (v : Y («E» := E) α T ℝ) :=
    heatKernel_convolutionExistsAt_of_bounded_continuous (sub_pos.mpr hs.2)
      ((hc v).comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩))
      (fun y => ParabolicHolder.norm_le v (s,y)) x
  exact (he f).distrib_add (he g)

/-- Scalar multiplication commutes with the Duhamel integral. -/
theorem duhamel_integral_smul {α T t : ℝ} (c : ℝ)
    (f : Y («E» := E) α T ℝ) (x : E) :
    (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => (c • f) (s,y)) x) =
      c • ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x := by
  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul]
  simp_rw [mul_left_comm (heatKernel _ _) c, integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- Integral linearity and graph uniqueness give a linear solution map. -/
def duhamelLinearMap (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →ₗ[ℝ] ParabolicSolutionGraph.Graph («E» := E) α T where
  toFun := duhamelGraph α T hα hα1 hT hT1
  map_add' f g := by
    apply ParabolicSolutionGraph.Graph.ext_of_u hT
    apply ParabolicHolder.ext
    intro p hp
    change (duhamelGraph α T hα hα1 hT hT1 (f+g)).u p =
      (duhamelGraph α T hα hα1 hT hT1 f).u p +
      (duhamelGraph α T hα hα1 hT hT1 g).u p
    rw [(duhamelGraph_spec α T hα hα1 hT hT1 (f+g)).1 p hp,
      (duhamelGraph_spec α T hα hα1 hT hT1 f).1 p hp,
      (duhamelGraph_spec α T hα hα1 hT hT1 g).1 p hp]
    exact duhamel_integral_add hα hp.1 f g p.2
  map_smul' c f := by
    apply ParabolicSolutionGraph.Graph.ext_of_u hT
    apply ParabolicHolder.ext
    intro p hp
    change (duhamelGraph α T hα hα1 hT hT1 (c • f)).u p =
      c • (duhamelGraph α T hα hα1 hT hT1 f).u p
    rw [(duhamelGraph_spec α T hα hα1 hT hT1 (c • f)).1 p hp,
      (duhamelGraph_spec α T hα hα1 hT hT1 f).1 p hp]
    exact duhamel_integral_smul c f p.2

/-- The bounded constant-coefficient inverse in continuous linear form. -/
def duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] ParabolicSolutionGraph.Graph («E» := E) α T :=
  (duhamelLinearMap α T hα hα1 hT hT1).mkContinuous (boundConstant α hα hα1)
    (fun f => (duhamelGraph_spec α T hα hα1 hT hT1 f).2)

/-- The operator's value component is the Duhamel integral on the cylinder. -/
theorem duhamelOperator_u (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
    ∀ p ∈ cylinder T, (duhamelOperator α T hα hα1 hT hT1 f).u p =
      ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2 :=
  (duhamelGraph_spec α T hα hα1 hT hT1 f).1

/-- The operator norms are uniformly bounded for all short positive intervals. -/
theorem duhamelOperator_norm_le :
    ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1), ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1),
        ‖duhamelOperator α T hα hα1 hT hT1‖ ≤ C := by
  intro α hα hα1
  refine ⟨boundConstant α hα hα1, (boundConstant_spec α hα hα1).1, ?_⟩
  intro T hT hT1
  exact LinearMap.mkContinuous_norm_le _ (boundConstant_spec α hα hα1).1.le _

/-- The graph satisfies the inhomogeneous heat equation, including both endpoints. -/
theorem duhamelOperator_solves (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (duhamelOperator α T hα hα1 hT hT1 f).ut (t,x) = f (t,x) +
        ∑ i : Fin 3, (duhamelOperator α T hα hα1 hT hT1 f).ddu (t,x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  let G := duhamelOperator α T hα hα1 hT hT1 f
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  have hu (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => G.u (t,z)) = u t := by
    funext z
    exact duhamelOperator_u α T hα hα1 hT hT1 f (t,z) ⟨ht, mem_univ z⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => G.du (t,z)) = fderiv ℝ (u t) := by
    funext z
    have h := (G.hasFDeriv t ht z).fderiv
    rw [hu t ht] at h
    exact h.symm
  have hdd (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
      G.ddu (t,x) = fderiv ℝ (fderiv ℝ (u t)) x := by
    have h := (G.hasFDeriv_du t ht x).fderiv
    rw [hd t ht] at h
    exact h.symm
  have hf : ContinuousOn f (cylinder T) :=
    continuousOn_of_hasHolderBound hα (hasHolderBound f)
  have hfM : ∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ ‖f‖ :=
    fun t _ x => ParabolicHolder.norm_le f (t,x)
  have hfK : ∀ t ∈ Icc 0 T, ∀ x y : E,
      |f (t,x)-f (t,y)| ≤ ‖f‖ * ‖x-y‖^α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using
      hasHolderBound f (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  intro t ht x
  change G.ut (t,x) = f (t,x) + ∑ i : Fin 3, G.ddu (t,x) _ _
  rw [hdd t ht x]
  have htime := (MovingLimitLeibniz.duhamel_solves_heat_equation α hα hα1 T hT hT1
    f ‖f‖ ‖f‖ (norm_nonneg f) (norm_nonneg f) hf hfM hfK).2 t ht x
  have htimeG := htime.congr_of_mem (fun s hs => congrFun (hu s hs) x) ht
  exact ((G.hasDeriv_time t ht x).derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
    (htimeG.derivWithin (uniqueDiffOn_Icc hT t ht))

end Poincare.DuhamelSolutionOperatorCLM

end
end
