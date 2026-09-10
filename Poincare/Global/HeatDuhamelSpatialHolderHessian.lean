import Poincare.Global.HeatKernelHessianMoments
import Poincare.Global.HeatCauchyNext2
import Poincare.Global.HeatMildBUCPositiveHolder

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

end Poincare.HeatDuhamelSpatialHolderHessian
