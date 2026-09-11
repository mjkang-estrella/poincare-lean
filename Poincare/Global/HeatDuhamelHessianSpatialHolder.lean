import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology InnerProductSpace Interval

namespace Poincare.HeatDuhamelHessianSpatialHolder

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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

/-- The unit-time third derivative has a cubic Gaussian envelope. -/
theorem norm_third_one_le (x : E) :
    ‖Third 1 x‖ ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by
  have hk : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
  have hB : 0 ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg u))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [third_apply one_ne_zero]
  norm_num only [one_pow, mul_one]
  rw [norm_mul, Real.norm_of_nonneg hk]
  calc
    _ ≤ heatKernel 1 x *
        (‖⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ‖ / 8 +
          ((‖⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ‖ + ‖⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ‖) +
            ‖⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ‖) / 4) := by
      gcongr
      calc
        _ ≤ ‖-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / 8‖ +
            ‖(⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ +
              ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / 4‖ := norm_add_le _ _
        _ ≤ _ := by
          simp only [norm_div, norm_neg, Real.norm_ofNat]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ heatKernel 1 x *
        (((‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) / 8 +
          (((‖u‖ * ‖v‖) * (‖x‖ * ‖w‖) + (‖x‖ * ‖v‖) * (‖u‖ * ‖w‖)) +
            (‖x‖ * ‖u‖) * (‖v‖ * ‖w‖)) / 4) := by
      simp only [norm_mul]
      gcongr <;> apply norm_inner_le_norm
    _ = _ := by ring

/-- The weighted third derivative is integrable at unit time. -/
theorem integrable_weighted_third_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    Integrable (fun x : E => ‖Third 1 x‖ * ‖x‖ ^ α) := by
  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hweight : Continuous (fun x : E => ‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))) :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ α + 1)).comp continuous_norm).mul
      (((continuous_norm.pow 2).div_const 8).neg.rexp)
  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
      («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
      hweight.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => show
        ‖‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
          rw [Real.norm_of_nonneg (by positivity)]
          exact rpow_mul_gaussian_le_eight (by linarith) (by linarith) (norm_nonneg x))
  have hcont : ContDiff ℝ 0 (Third 1) :=
    (((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)
  refine (hbound.const_mul c).mono'
    (hcont.continuous.norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  have hK : heatKernel (1 : ℝ) x =
      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
    rw [← Real.exp_add]
    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
      Nat.cast_ofNat, mul_one]
    congr 1
    congr 1
    ring
  have hw : ‖x‖ ^ (α + 1) = ‖x‖ ^ α * ‖x‖ :=
    Real.rpow_add_one' (norm_nonneg x) (by linarith)
  calc
    ‖Third 1 x‖ * ‖x‖ ^ α ≤
        (heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)) * ‖x‖ ^ α :=
      mul_le_mul_of_nonneg_right (norm_third_one_le x) (Real.rpow_nonneg (norm_nonneg x) α)
    _ ≤ (heatKernel 1 x * (‖x‖ * (1 + ‖x‖ ^ 2))) * ‖x‖ ^ α := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg x) 3]
    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
        (‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK, hw]; ring

/-- Parabolic dilation of the full third spatial derivative. -/
theorem third_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    Third (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹) • Third 1 x := by
  ext u v w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [third_apply (pow_ne_zero _ ha.ne'), third_apply one_ne_zero,
    heatKernel_sq_smul a ha x]
  simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
  field_simp

/-- Pointwise parabolic dilation including the radial weight. -/
theorem weighted_third_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
    ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
      ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (‖Third 1 x‖ * ‖x‖ ^ α) := by
  rw [third_sq_smul a ha x,
    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 3)⁻¹ by positivity) (Third 1 x),
    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
  ring

/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
theorem weighted_third_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
    (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
      ((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => ‖Third (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
  calc
    (a ^ 3)⁻¹ * (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
        ∫ x : E, ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
    _ = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
      simp_rw [weighted_third_sq_smul a ha]
      rw [integral_const_mul]
    _ = (a ^ 3)⁻¹ * (((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α)) := by ring

/-- Weighted Bochner integrability at every positive time. -/
theorem integrable_weighted_third {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) := by
  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [← Real.sq_sqrt ht.le]
  apply (integrable_comp_smul_iff volume _ ha.ne').1
  simp_rw [weighted_third_sq_smul (Real.sqrt t) ha]
  exact (integrable_weighted_third_one hα hα1).const_mul _

/-- Exact scaling of the third spatial derivative moment. -/
theorem weighted_third_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
    (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) =
      t ^ (α / 2 - 3 / 2) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
  have h := weighted_third_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
  rw [Real.sq_sqrt ht.le] at h
  rw [h]
  congr 1
  have hp : (Real.sqrt t) ^ 3 = t ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
    congr 1
    norm_num
  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht]
  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
  ring

/-- The third Gaussian moment has a positive constant independent of time. -/
theorem third_moment_bound :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) ∧
      (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 3 / 2) := by
  intro α hα hα1
  refine ⟨max 1 (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  refine ⟨integrable_weighted_third hα.le hα1.le ht, ?_⟩
  rw [weighted_third_integral ht, mul_comm (t ^ (α / 2 - 3 / 2))]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

/-- The near-time cancelled integral is bounded by the length of its time interval. -/
theorem norm_integral_cancelled_hessian_near_le {α K a t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hat : a ≤ t) {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * (t - a) ^ (α / 2) := by
  have hb := norm_integral_cancelled_hessian_time_le hα hα1 (sub_nonneg.mpr hat)
    (f := fun p => f (p.1 + a, p.2))
    (fun s hs => hK (s + a) ⟨by linarith [hs.1], by linarith [hs.2]⟩) x
  have he := intervalIntegral.integral_comp_add_right
    (a := (0 : ℝ)) (b := t - a)
    (fun s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) a
  simp only [zero_add, sub_add_cancel] at he
  have htau (s : ℝ) : t - a - s = t - (s + a) := by ring
  simp only [htau] at hb
  rw [he] at hb
  exact hb

end Poincare.HeatDuhamelHessianSpatialHolder
