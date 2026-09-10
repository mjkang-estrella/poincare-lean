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

end Poincare.HeatDuhamelSpatialHolderHessian
