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

end Poincare.HeatDuhamelHessianTimeHolder
