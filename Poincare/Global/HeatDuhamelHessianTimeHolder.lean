import Poincare.Global.HeatDuhamelHessianSpatialHolder
set_option autoImplicit false
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

end Poincare.HeatDuhamelHessianTimeHolder
