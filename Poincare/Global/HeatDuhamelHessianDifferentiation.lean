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

end Poincare.HeatDuhamelHessianDifferentiation
