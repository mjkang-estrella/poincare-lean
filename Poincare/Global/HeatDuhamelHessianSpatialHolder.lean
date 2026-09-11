import Poincare.Global.HeatDuhamelHessianDifferentiation
import Mathlib.Analysis.MeanInequalitiesPow

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
  ring_nf

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

/-- The near part of the spatial increment has the required Hölder power. -/
theorem near_hessian_difference_le {α K a t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hat : a ≤ t)
    {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hscale : t - a ≤ ‖x - z‖ ^ 2) :
    ‖(∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
      (∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
  let J := ∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α
  have hJ : 0 ≤ J := integral_nonneg (fun y => by positivity)
  have hp : (t - a) ^ (α / 2) ≤ ‖x - z‖ ^ α := by
    calc
      (t - a) ^ (α / 2) ≤ (‖x - z‖ ^ 2) ^ (α / 2) :=
        Real.rpow_le_rpow (sub_nonneg.mpr hat) hscale (by linarith)
      _ = ‖x - z‖ ^ α := by
        rw [← Real.rpow_natCast_mul (norm_nonneg (x - z))]
        congr 1
        norm_num
        ring
  calc
    _ ≤ ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ +
        ‖∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y‖ :=
      norm_sub_le _ _
    _ ≤ (K * J) * (2 / α) * (t - a) ^ (α / 2) +
        (K * J) * (2 / α) * (t - a) ^ (α / 2) :=
      add_le_add (norm_integral_cancelled_hessian_near_le hα hα1 hat hK x)
        (norm_integral_cancelled_hessian_near_le hα hα1 hat hK z)
    _ = (2 * J * (2 / α)) * K * (t - a) ^ (α / 2) := by ring
    _ ≤ (2 * J * (2 / α)) * K * ‖x - z‖ ^ α :=
      mul_le_mul_of_nonneg_left hp
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hJ)
          (div_nonneg (by norm_num) hα.le)) hK0)

/-- The spatial Hölder estimate for the actual Duhamel Hessian when the near interval is all of time. -/
theorem duhamel_hessian_spatial_holder_of_time_le_dist_sq {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hscale : t ≤ ‖x - z‖ ^ 2) :
    let u : E → ℝ := fun x => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) x
    ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
  dsimp only
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
  exact near_hessian_difference_le hα hα1 hK0 ht.1
    (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x z (by simpa using hscale)

/-- The far-time power integral supplies the factor two over one minus the exponent. -/
theorem far_time_power_integral_le {α ρ t : ℝ}
    (hα1 : α < 1) (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ t) :
    ρ * (∫ s in (0 : ℝ)..(t - ρ ^ 2), (t - s) ^ (α / 2 - 3 / 2)) ≤
      (2 / (1 - α)) * ρ ^ α := by
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hq : α / 2 - 3 / 2 + 1 < 0 := by linarith
  rw [intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => r ^ (α / 2 - 3 / 2)) t, sub_sub_cancel, sub_zero]
  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
  · calc
      ρ * ((t ^ (α / 2 - 3 / 2 + 1) - (ρ ^ 2) ^ (α / 2 - 3 / 2 + 1)) /
          (α / 2 - 3 / 2 + 1)) ≤
          ρ * (-(ρ ^ 2) ^ (α / 2 - 3 / 2 + 1) / (α / 2 - 3 / 2 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hρ.le
        simp only [div_eq_mul_inv]
        apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
        have hnn := Real.rpow_nonneg (hρ2.le.trans ht) (α / 2 - 3 / 2 + 1)
        simp only [div_eq_mul_inv] at hnn
        linarith only [hnn]
      _ = (2 / (1 - α)) * ρ ^ α := by
        rw [← Real.rpow_natCast_mul hρ.le]
        simp only [Nat.cast_ofNat]
        rw [show (2 : ℝ) * (α / 2 - 3 / 2 + 1) = α - 1 by ring]
        rw [Real.rpow_sub hρ, Real.rpow_one]
        have hden : 1 - α ≠ 0 := by linarith
        have hden' : α / 2 - 3 / 2 + 1 ≠ 0 := hq.ne
        field_simp [hρ.ne', hden, hden', show -1 + α ≠ 0 by linarith]
        ring_nf
        all_goals
          have hi := mul_inv_cancel₀ (show -1 + α ≠ 0 by linarith)
          nlinarith only [hi]
  · rw [uIcc_of_le ht]
    intro hz
    exact (not_le.mpr hρ2) hz.1

/-- Both observation points can use the same cancellation constant. -/
theorem hessian_heatSolution_eq_common_cancelled_integral {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
    fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
      ∫ y : E, (f (x - y) - f x) • Hess t (y + (z - x)) := by
  have hi : Integrable (fun y : E => f y • Hess t (z - y)) :=
    integrable_data_smul_hessian_sub ht hf hM z
  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
    ((integrable_hessian ht).comp_sub_left z).smul (f x)
  have hz : (∫ y : E, Hess t (z - y)) = 0 := by
    rw [integral_sub_left_eq_self, integral_hessian_eq_zero ht]
  have he : (∫ y : E, (f y - f x) • Hess t (z - y)) =
      fderiv ℝ (fderiv ℝ (heatSolution t f)) z := by
    simp_rw [sub_smul]
    rw [integral_sub hi hc, integral_smul, hz, smul_zero, sub_zero,
      hessian_heatSolution_eq_integral ht hf hM]
  rw [← he]
  have hchange := integral_sub_left_eq_self
    (fun y : E => (f y - f x) • Hess t (z - y)) volume x
  have halg (y : E) : z - (x - y) = y + (z - x) := by abel
  simpa only [halg] using hchange.symm

/-- The Hessian increment is the cancelled integral of a kernel translation difference. -/
theorem hessian_heatSolution_difference_eq_integral {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
    fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
      fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
      ∫ y : E, (f (x - y) - f x) • (Hess t y - Hess t (y + (z - x))) := by
  have hi := integrable_data_smul_hessian_sub ht hf hM z
  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
    ((integrable_hessian ht).comp_sub_left z).smul (f x)
  have hij : Integrable (fun y : E => (f (x - y) - f x) • Hess t (y + (z - x))) := by
    have h := (hi.sub hc).comp_sub_left x
    have halg (y : E) : z - (x - y) = y + (z - x) := by abel
    simpa only [Pi.sub_apply, halg, ← sub_smul] using h
  rw [hessian_heatSolution_eq_cancelled_integral ht hf hM x,
    hessian_heatSolution_eq_common_cancelled_integral ht hf hM x z]
  simp_rw [smul_sub]
  rw [integral_sub (integrable_cancelled_hessian ht hf hM x) hij]

/-- A translated Hessian difference is bounded by the third derivative along its segment. -/
theorem norm_hessian_translation_le (t : ℝ) (y w : E) :
    ‖Hess t (y + w) - Hess t y‖ ≤
      ∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖ := by
  have hH : ContDiff ℝ 1 (Hess t) :=
    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hD : Continuous (Third t) := (hH.fderiv_right (m := 0) (by norm_num)).continuous
  have hline (r : ℝ) : HasDerivAt (fun q : ℝ => y + q • w) w r := by
    simpa only [one_smul] using ((hasDerivAt_id r).smul_const w).const_add y
  have hd (r : ℝ) : HasDerivAt (fun q : ℝ => Hess t (y + q • w))
      (Third t (y + r • w) w) r :=
    ((hH.differentiable (by norm_num) (y + r • w)).hasFDerivAt).comp_hasDerivAt r (hline r)
  have hbound : Continuous (fun r : ℝ => ‖Third t (y + r • w)‖ * ‖w‖) :=
    (hD.comp (continuous_const.add (continuous_id.smul continuous_const))).norm.mul continuous_const
  have hi : IntervalIntegrable (fun r : ℝ => Third t (y + r • w) w) volume 0 1 :=
    ((hD.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun r _ => hd r) hi
  simp only [one_smul, zero_smul, add_zero] at he
  rw [← he]
  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall fun r _ => ContinuousLinearMap.le_opNorm _ _)
    (hbound.intervalIntegrable 0 1)

/-- Translating the third derivative costs one unweighted moment in addition to its weighted moment. -/
theorem weighted_third_translation {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (ht : 0 < t) (w : E) :
    Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) ∧
    (∫ y : E, ‖Third t (y + w)‖ * ‖y‖ ^ α) ≤
      (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖) := by
  have hiα := (integrable_weighted_third hα hα1 ht).comp_add_right w
  have hi0 : Integrable (fun y : E => ‖Third t y‖) := by
    simpa using integrable_weighted_third (α := 0) (by norm_num) (by norm_num) ht
  have hiw := (hi0.comp_add_right w).const_mul (‖w‖ ^ α)
  have hmajor := hiα.add hiw
  have hb (y : E) : ‖Third t (y + w)‖ * ‖y‖ ^ α ≤
      ‖Third t (y + w)‖ * ‖y + w‖ ^ α + ‖w‖ ^ α * ‖Third t (y + w)‖ := by
    have hnorm : ‖y‖ ≤ ‖y + w‖ + ‖w‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (y + w) w
    have hp : ‖y‖ ^ α ≤ ‖y + w‖ ^ α + ‖w‖ ^ α :=
      (Real.rpow_le_rpow (norm_nonneg y) hnorm hα).trans
        (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hα hα1)
    calc
      _ ≤ ‖Third t (y + w)‖ * (‖y + w‖ ^ α + ‖w‖ ^ α) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = _ := by ring
  have hD : Continuous (Third t) :=
    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuous
  have hi : Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) :=
    hmajor.mono' ((hD.comp (continuous_id.add continuous_const)).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
        exact hb y)
  refine ⟨hi, (integral_mono hi hmajor hb).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add hiα hiw, integral_const_mul,
    integral_add_right_eq_self (fun y : E => ‖Third t y‖ * ‖y‖ ^ α) w,
    integral_add_right_eq_self (fun y : E => ‖Third t y‖) w]

/-- The segment parameter and the weighted spatial third derivative form an integrable product. -/
theorem integrable_segment_weighted_third {α t : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
    Integrable (fun p : ℝ × E => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
  have hD : Continuous (Third t) :=
    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuous
  have hg : Continuous G :=
    (hD.comp (continuous_snd.add (continuous_fst.smul continuous_const))).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_snd.norm)
  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall fun r => (weighted_third_translation hα hα1 ht (r • w)).1, ?_⟩
  have hm := hg.norm.stronglyMeasurable.integral_prod_right' (ν := volume)
  refine (integrable_const C).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have he : (∫ y : E, ‖G (r, y)‖) = ∫ y : E, G (r, y) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
  have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
    rw [norm_smul_of_nonneg hr.1]
    nlinarith [norm_nonneg w, hr.2]
  exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
      (integral_nonneg (fun y => norm_nonneg _))))

/-- Integrating the segment estimate gives a weighted translation estimate for the Hessian. -/
theorem weighted_hessian_translation {α t : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
    Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ∧
    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
      ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := by
  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
  have hg : Integrable G ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
    integrable_segment_weighted_third hα hα1 ht w
  have hiMajor := hg.integral_prod_right.const_mul ‖w‖
  have hb (y : E) : ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α ≤
      ‖w‖ * (∫ r in Icc (0 : ℝ) 1, G (r, y)) := by
    calc
      _ ≤ (∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖) * ‖y‖ ^ α :=
        mul_le_mul_of_nonneg_right (norm_hessian_translation_le t y w)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by
        change _ = ‖w‖ * (∫ r in Icc (0 : ℝ) 1, ‖Third t (y + r • w)‖ * ‖y‖ ^ α)
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
        ring
  have hH : Continuous (Hess t) :=
    (((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hi : Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) :=
    hiMajor.mono' (((hH.comp (continuous_id.add continuous_const)).sub hH).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
        exact hb y)
  refine ⟨hi, (integral_mono hi hiMajor hb).trans ?_⟩
  rw [integral_const_mul]
  have hswap : (∫ y : E, ∫ r in Icc (0 : ℝ) 1, G (r, y)) =
      ∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y) :=
    (integral_integral_swap hg).symm
  rw [hswap]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
  calc
    (∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y)) ≤ ∫ _r in Icc (0 : ℝ) 1, C := by
      apply integral_mono_ae hg.integral_prod_left (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
        apply Real.rpow_le_rpow (norm_nonneg _) _ hα
        rw [norm_smul_of_nonneg hr.1]
        nlinarith [norm_nonneg w, hr.2]
      exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
          (integral_nonneg (fun y => norm_nonneg _))))
    _ = C := by simp

/-- Beyond the spatial time scale, both translation terms have the same time power. -/
theorem weighted_hessian_translation_far {α t : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) (hw : ‖w‖ ^ 2 ≤ t) :
    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
      ‖w‖ * t ^ (α / 2 - 3 / 2) *
        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) := by
  have hp : ‖w‖ ^ α ≤ t ^ (α / 2) := by
    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (show 0 ≤ α / 2 by linarith)
    rw [← Real.rpow_natCast_mul (norm_nonneg w)] at h
    have he : (2 : ℝ) * (α / 2) = α := by ring
    simpa only [Nat.cast_ofNat, he] using h
  have hzero : (∫ y : E, ‖Third t y‖) =
      t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖) := by
    simpa using weighted_third_integral ht 0
  have hJ : 0 ≤ ∫ y : E, ‖Third 1 y‖ := integral_nonneg (fun y => norm_nonneg _)
  calc
    _ ≤ ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) +
        ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := (weighted_hessian_translation hα hα1 ht w).2
    _ = ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
        ‖w‖ ^ α * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
      rw [weighted_third_integral ht, hzero]
    _ ≤ ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
        t ^ (α / 2) * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hp
        (mul_nonneg (Real.rpow_nonneg ht.le _) hJ))
    _ = _ := by
      rw [← mul_assoc (t ^ (α / 2)), ← Real.rpow_add ht]
      rw [show α / 2 + -(3 / 2 : ℝ) = α / 2 - 3 / 2 by ring]
      ring

/-- The far-time spatial heat Hessian increment is linear in the observation distance. -/
theorem norm_heat_hessian_difference_far_le {α t M K : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (hK0 : 0 ≤ K)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (hM : ∀ y, ‖f y‖ ≤ M)
    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hscale : ‖x - z‖ ^ 2 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
      fderiv ℝ (fderiv ℝ (heatSolution t f)) z‖ ≤
      ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
        K * ‖x - z‖ * t ^ (α / 2 - 3 / 2) := by
  rw [hessian_heatSolution_difference_eq_integral ht hf hM x z]
  have hi := (weighted_hessian_translation hα hα1 ht (z - x)).1.const_mul K
  have hb (y : E) : ‖(f (x - y) - f x) • (Hess t y - Hess t (y + (z - x)))‖ ≤
      K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := by
    have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
      have he : x - y - x = -y := by abel
      simpa only [he, norm_neg, Real.norm_eq_abs] using hK (x - y) x
    calc
      _ ≤ ‖f (x - y) - f x‖ * ‖Hess t y - Hess t (y + (z - x))‖ :=
        norm_real_smul_continuousLinearMap_two_le _ _
      _ ≤ (K * ‖y‖ ^ α) * ‖Hess t y - Hess t (y + (z - x))‖ :=
        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev (Hess t y)]; ring
  calc
    _ ≤ ∫ y : E, K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
    _ = K * (∫ y : E, ‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := integral_const_mul _ _
    _ ≤ K * (‖z - x‖ * t ^ (α / 2 - 3 / 2) *
        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖))) :=
      mul_le_mul_of_nonneg_left (weighted_hessian_translation_far hα hα1 ht (z - x)
        (by simpa only [norm_sub_rev z x] using hscale)) hK0
    _ = _ := by rw [norm_sub_rev z x]; ring

/-- The far part of the cancelled Duhamel Hessian has the spatial Hölder bound. -/
theorem far_hessian_difference_le {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x z : E) (hρ : 0 < ‖x - z‖) (hscale : ‖x - z‖ ^ 2 < t) :
    ‖(∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
        (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
      (∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
        (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
      (((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
        (2 / (1 - α))) * K * ‖x - z‖ ^ α := by
  let a := t - ‖x - z‖ ^ 2
  let J := (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)
  let F := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
  have ha : 0 < a := sub_pos.mpr hscale
  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
  have hρ2 : 0 < ‖x - z‖ ^ 2 := sq_pos_of_pos hρ
  have hJ : 0 ≤ J := add_nonneg
    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (integral_nonneg (fun y => norm_nonneg _))
  have hFi (p : E) : IntervalIntegrable (fun s => F s p) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
        (Ioo_subset_Ioo le_rfl hat))
  have hip : IntervalIntegrable (fun r : ℝ => r ^ (α / 2 - 3 / 2)) volume (‖x - z‖ ^ 2) t := by
    apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
    rw [uIcc_of_le hscale.le]
    intro hz
    exact (not_le.mpr hρ2) hz.1
  have hiB : IntervalIntegrable
      (fun s : ℝ => J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2)) volume 0 a := by
    have h := (hip.comp_sub_left t).symm
    simp only [sub_self] at h
    exact h.const_mul (J * K * ‖x - z‖)
  have hbound : ‖∫ s in (0 : ℝ)..a, F s x - F s z‖ ≤
      ∫ s in (0 : ℝ)..a, J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ha.le _ hiB
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, (hs.2.trans hat).trans ht.2⟩
    have hsτ : ‖x - z‖ ^ 2 ≤ t - s := by dsimp [a] at hs; linarith [hs.2]
    have hτ : 0 < t - s := hρ2.trans_le hsτ
    have hfc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM s hsT
    dsimp only [F]
    rw [← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs x,
      ← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs z]
    exact norm_heat_hessian_difference_far_le hα.le hα1.le hτ hK0
      hfc.aestronglyMeasurable hMs (hK s hsT) x z hsτ
  change ‖(∫ s in (0 : ℝ)..a, F s x) - (∫ s in (0 : ℝ)..a, F s z)‖ ≤ _
  rw [← intervalIntegral.integral_sub (hFi x) (hFi z)]
  refine hbound.trans ?_
  rw [intervalIntegral.integral_const_mul]
  calc
    (J * K * ‖x - z‖) * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2)) =
        (J * K) * (‖x - z‖ * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2))) := by ring
    _ ≤ (J * K) * ((2 / (1 - α)) * ‖x - z‖ ^ α) :=
      mul_le_mul_of_nonneg_left (far_time_power_integral_le hα1 hρ hscale.le) (mul_nonneg hJ hK0)
    _ = _ := by ring

/-- The spatial Hölder estimate for the actual Duhamel Hessian. -/
theorem duhamel_hessian_spatial_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t ∈ Icc 0 T, ∀ x z : E,
    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α := by
  intro α hα hα1
  let N := 2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
  let F := ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) * (2 / (1 - α))
  have hN : 0 ≤ N := mul_nonneg
    (mul_nonneg (by norm_num) (integral_nonneg (fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))))
    (div_nonneg (by norm_num) hα.le)
  have hF : 0 ≤ F := mul_nonneg
    (add_nonneg (integral_nonneg (fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
      (integral_nonneg (fun y => norm_nonneg _)))
    (div_nonneg (by norm_num) (by linarith))
  refine ⟨max 1 (N + F), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro T _ _ f M K _ hK0 hf hM hK
  dsimp only
  intro t ht x z
  have hC : N + F ≤ max 1 (N + F) := le_max_right _ _
  have hpow : 0 ≤ ‖x - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  suffices hraw : ‖fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) x)) x -
      fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) x)) z‖ ≤ (N + F) * K * ‖x - z‖ ^ α by
    exact hraw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hK0) hpow)
  by_cases he : x = z
  · subst z
    simp [Real.zero_rpow hα.ne']
  have hρ : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  by_cases htime : t ≤ ‖x - z‖ ^ 2
  · exact (duhamel_hessian_spatial_holder_of_time_le_dist_sq hα hα1 ht hK0 hf hM hK x z htime).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show N ≤ N + F by linarith) hK0) hpow)
  have hscale : ‖x - z‖ ^ 2 < t := lt_of_not_ge htime
  let a := t - ‖x - z‖ ^ 2
  let H := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
  have ha : 0 < a := sub_pos.mpr hscale
  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
  have h0t (p : E) : IntervalIntegrable (fun s => H s p) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK p)
  have h0a (p : E) : IntervalIntegrable (fun s => H s p) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
        (Ioo_subset_Ioo le_rfl hat))
  have hsplit (p : E) : (∫ s in (0 : ℝ)..t, H s p) =
      (∫ s in (0 : ℝ)..a, H s p) + (∫ s in a..t, H s p) :=
    (intervalIntegral.integral_add_adjacent_intervals (h0a p) ((h0a p).symm.trans (h0t p))).symm
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
  change ‖(∫ s in (0 : ℝ)..t, H s x) - (∫ s in (0 : ℝ)..t, H s z)‖ ≤ _
  rw [hsplit x, hsplit z]
  have hnear : ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ ≤ N * K * ‖x - z‖ ^ α := by
    apply near_hessian_difference_le hα hα1 hK0 hat
    · intro s hs
      exact hK s ⟨ha.le.trans hs.1.le, hs.2.le.trans ht.2⟩
    · dsimp only [a]
      linarith
  have hfar : ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ ≤ F * K * ‖x - z‖ ^ α :=
    far_hessian_difference_le hα hα1 ht hK0 hf hM hK x z hρ hscale
  calc
    _ = ‖((∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)) +
        ((∫ s in a..t, H s x) - (∫ s in a..t, H s z))‖ := by congr 1; abel
    _ ≤ ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ +
        ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ := norm_add_le _ _
    _ ≤ F * K * ‖x - z‖ ^ α + N * K * ‖x - z‖ ^ α := add_le_add hfar hnear
    _ = (N + F) * K * ‖x - z‖ ^ α := by ring

end Poincare.HeatDuhamelHessianSpatialHolder
