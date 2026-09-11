import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology InnerProductSpace Interval

namespace Poincare.HeatDuhamelHessianSpatialHolder

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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
  ring

end Poincare.HeatDuhamelHessianSpatialHolder
