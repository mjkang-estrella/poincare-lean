import Poincare.Global.HeatDuhamelSpatialHolderHessian

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

end Poincare.HeatDuhamelHessianDifferentiation
