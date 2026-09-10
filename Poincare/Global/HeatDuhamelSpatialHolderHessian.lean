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

end Poincare.HeatDuhamelSpatialHolderHessian
