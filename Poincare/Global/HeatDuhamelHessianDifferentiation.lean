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

end Poincare.HeatDuhamelHessianDifferentiation
