import Poincare.Global.HeatDuhamelHessianSpatialHolder
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

end Poincare.HeatDuhamelHessianTimeHolder
