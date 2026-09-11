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


/-- The quartic envelope remains integrable after a fractional radial weight. -/
theorem integrable_weighted_hessian_time_deriv_one {α : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) :
    Integrable (fun x : E => ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmajor := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
    («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).const_mul (512 * c)
  apply hmajor.mono'
    ((continuous_hessian_time_deriv zero_lt_one).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun x => ?_
  change ‖‖DtHess 1 x‖ * ‖x‖ ^ α‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
  have hk0 : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
  have hw : ‖x‖ ^ α ≤ 1 + ‖x‖ ^ 2 := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx hα).trans (by nlinarith [sq_nonneg ‖x‖])
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hα2
      rw [Real.rpow_two] at h
      linarith
  have hbase : 1 + ‖x‖ ^ 2 ≤ 16 * Real.exp (‖x‖ ^ 2 / 16) := by
    have h := Real.add_one_le_exp (‖x‖ ^ 2 / 16)
    linarith
  have hsquare : (1 + ‖x‖ ^ 2) ^ 2 ≤ 256 * Real.exp (‖x‖ ^ 2 / 8) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖ ^ 2) hbase 2
    have he : Real.exp (‖x‖ ^ 2 / 16) ^ 2 = Real.exp (‖x‖ ^ 2 / 8) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow, he, show (16 : ℝ) ^ 2 = 256 by norm_num] using h
  have hpoly : ‖x‖ ^ 4 + ‖x‖ ^ 2 + 2 ≤ 2 * (1 + ‖x‖ ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ ^ 2), sq_nonneg ‖x‖]
  have hk : heatKernel (1 : ℝ) x = c * Real.exp (-(‖x‖ ^ 2 / 4)) := by
    simp [heatKernel, c, ClosedSmoothModel, neg_div]
  calc
    _ ≤ (heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2)) * ‖x‖ ^ α :=
      mul_le_mul_of_nonneg_right (norm_hessian_time_deriv_one_le x) (by positivity)
    _ ≤ (heatKernel 1 x * (2 * (1 + ‖x‖ ^ 2) ^ 2)) * (1 + ‖x‖ ^ 2) := by
      gcongr
    _ ≤ (heatKernel 1 x * (2 * (256 * Real.exp (‖x‖ ^ 2 / 8)))) * (1 + ‖x‖ ^ 2) := by
      gcongr
    _ = (512 * c) * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) := by
      rw [hk]
      have he : Real.exp (-(‖x‖ ^ 2 / 4)) * Real.exp (‖x‖ ^ 2 / 8) =
          Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (512 * c) * ((1 + ‖x‖ ^ 2) *
          (Real.exp (-(‖x‖ ^ 2 / 4)) * Real.exp (‖x‖ ^ 2 / 8))) := by ring
        _ = _ := by rw [he]


/-- Parabolic dilation of the time derivative of the Gaussian Hessian. -/
theorem hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    DtHess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) • DtHess 1 x := by
  change deriv (fun r : ℝ => Hess r (a • x)) (a ^ 2) =
    ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) • deriv (fun r : ℝ => Hess r x) 1
  rw [(hasDerivAt_hessian_time (sq_pos_of_pos ha) (a • x)).deriv,
    (hasDerivAt_hessian_time zero_lt_one x).deriv]
  ext v w
  change (heatKernel (a ^ 2) (a • x) *
      (‖a • x‖ ^ 2 / (16 * (a ^ 2) ^ 4) - 7 / (8 * (a ^ 2) ^ 3))) *
        (⟪a • x, v⟫_ℝ * ⟪a • x, w⟫_ℝ) -
      (heatKernel (a ^ 2) (a • x) *
        (‖a • x‖ ^ 2 / (8 * (a ^ 2) ^ 3) - 5 / (4 * (a ^ 2) ^ 2))) * ⟪v, w⟫_ℝ =
    ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) *
      ((heatKernel 1 x * (‖x‖ ^ 2 / (16 * 1 ^ 4) - 7 / (8 * 1 ^ 3))) *
        (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) -
      (heatKernel 1 x * (‖x‖ ^ 2 / (8 * 1 ^ 3) - 5 / (4 * 1 ^ 2))) * ⟪v, w⟫_ℝ)
  rw [heatKernel_sq_smul a ha x, norm_smul_of_nonneg ha.le]
  simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
  field_simp

/-- Pointwise parabolic dilation including the radial weight. -/
theorem weighted_hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
    ‖DtHess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
      ((a ^ 3)⁻¹ * (a ^ 4)⁻¹ * a ^ α) * (‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  rw [hessian_time_deriv_sq_smul a ha x,
    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 4)⁻¹ by positivity) (DtHess 1 x),
    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
  ring


/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
theorem weighted_hessian_time_deriv_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
    (∫ x : E, ‖DtHess (a ^ 2) x‖ * ‖x‖ ^ α) =
      ((a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => ‖DtHess (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
  calc
    (a ^ 3)⁻¹ * (∫ x : E, ‖DtHess (a ^ 2) x‖ * ‖x‖ ^ α) =
        ∫ x : E, ‖DtHess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
    _ = ((a ^ 3)⁻¹ * (a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
      simp_rw [weighted_hessian_time_deriv_sq_smul a ha]
      rw [integral_const_mul]
    _ = (a ^ 3)⁻¹ * (((a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α)) := by ring


/-- Weighted Bochner integrability at every positive time. -/
theorem integrable_weighted_hessian_time_deriv {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => ‖DtHess t x‖ * ‖x‖ ^ α) := by
  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [← Real.sq_sqrt ht.le]
  apply (integrable_comp_smul_iff volume _ ha.ne').1
  simp_rw [weighted_hessian_time_deriv_sq_smul (Real.sqrt t) ha]
  exact (integrable_weighted_hessian_time_deriv_one hα hα2).const_mul _


/-- Exact scaling of the weighted Hessian time-derivative moment. -/
theorem weighted_hessian_time_deriv_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
    (∫ x : E, ‖DtHess t x‖ * ‖x‖ ^ α) =
      t ^ (α / 2 - 2) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
  have h := weighted_hessian_time_deriv_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
  rw [Real.sq_sqrt ht.le] at h
  rw [h]
  congr 1
  have hp : (Real.sqrt t) ^ 4 = t ^ 2 := by nlinarith [Real.sq_sqrt ht.le]
  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_two]
  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
  ring

/-- The weighted time derivative has a positive constant uniform for all positive times. -/
theorem hessian_time_deriv_moment_bound :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : E => ‖DtHess t x‖ * ‖x‖ ^ α) ∧
      (∫ x : E, ‖DtHess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 2) := by
  intro α hα hα1
  refine ⟨max 1 (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  refine ⟨integrable_weighted_hessian_time_deriv hα.le (by linarith) ht, ?_⟩
  rw [weighted_hessian_time_deriv_integral ht, mul_comm (t ^ (α / 2 - 2))]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

/-- The new time interval contributes only the half-exponent Hölder tail. -/
theorem hessian_tail_bound {α K T t₁ t₂ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht₁ : t₁ ∈ Icc 0 T)
    (ht₂ : t₂ ∈ Icc 0 T) (h12 : t₁ ≤ t₂) {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖∫ s in t₁..t₂, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y‖ ≤
      ((∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * |t₂ - t₁| ^ (α / 2) := by
  have h := norm_integral_cancelled_hessian_near_le hα hα1 h12
    (fun s hs => hK s ⟨ht₁.1.trans hs.1.le, hs.2.le.trans ht₂.2⟩) x
  rw [abs_of_nonneg (sub_nonneg.mpr h12)]
  convert h using 1
  ring

/-- An interval ending before the observation time obeys the same short-interval bound. -/
theorem norm_integral_cancelled_hessian_before_le {α K a b t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hab : a ≤ b) (hbt : b ≤ t)
    {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a b, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖∫ s in a..b, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * (b - a) ^ (α / 2) := by
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
  have hA : 0 ≤ A := mul_nonneg hK0 (integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
  have hi : IntervalIntegrable (fun s : ℝ => A * (b - s) ^ (α / 2 - 1)) volume a b := by
    have h := ((intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := b - a) (r := α / 2 - 1) (by linarith)).comp_sub_left b).symm
    simp only [sub_zero, sub_sub_cancel] at h
    exact h.const_mul A
  have hb : ‖∫ s in Ioo a b, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
      ∫ s in Ioo a b, A * (b - s) ^ (α / 2 - 1) := by
    apply norm_integral_le_of_norm_le
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (norm_cancelled_hessian_integral_le hα.le (by linarith)
      (by linarith [hs.2] : 0 < t - s) (hK s hs) x).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hs.2) (by linarith) (by linarith)) hA)
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hab] at hb
  refine hb.trans_eq ?_
  have he := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := b - a)
    (fun s : ℝ => A * (b - s) ^ (α / 2 - 1)) a
  simp only [zero_add, sub_add_cancel] at he
  have hs (s : ℝ) : b - (s + a) = b - a - s := by ring
  simp only [hs] at he
  rw [← he, integral_hessian_majorant hα]

/-- The recent part of a time increment costs twice the Hessian majorant. -/
theorem near_hessian_time_difference_le {α K a t₁ t₂ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (ha : a ≤ t₁) (h12 : t₁ ≤ t₂)
    (hscale : t₁ - a ≤ t₂ - t₁) {f : ℝ × E → ℝ}
    (hK : ∀ s ∈ Ioo a t₁, ∀ x y : E,
      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
    ‖(∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y) -
      (∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y)‖ ≤
      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * (t₂ - t₁) ^ (α / 2) := by
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hK0 (integral_nonneg (fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))))
    (div_nonneg (by norm_num) hα.le)
  have hp : (t₁ - a) ^ (α / 2) ≤ (t₂ - t₁) ^ (α / 2) :=
    Real.rpow_le_rpow (sub_nonneg.mpr ha) hscale (by linarith)
  calc
    _ ≤ ‖∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y‖ +
      ‖∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y‖ :=
      norm_sub_le _ _
    _ ≤ A * (t₁ - a) ^ (α / 2) + A * (t₁ - a) ^ (α / 2) :=
      add_le_add (norm_integral_cancelled_hessian_before_le hα hα1 hK0 ha h12 hK x)
        (norm_integral_cancelled_hessian_before_le hα hα1 hK0 ha le_rfl hK x)
    _ ≤ A * (t₂ - t₁) ^ (α / 2) + A * (t₂ - t₁) ^ (α / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hp hA) (mul_le_mul_of_nonneg_left hp hA)
    _ = _ := by dsimp [A]; ring

/-- Dilation gives joint continuity of the full DtHessian at positive times. -/
theorem continuous_hessian_time_deriv_pos :
    Continuous (fun p : Ioi (0 : ℝ) × E => DtHess p.1 p.2) := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  have hunit : Continuous (DtHess 1) := continuous_hessian_time_deriv zero_lt_one
  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
    Real.sqrt_pos.2 p.1.property
  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * ((Real.sqrt (p.1 : ℝ)) ^ 4)⁻¹) •
        DtHess 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
      ((ha.pow 4).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')) |>.smul
      (hunit.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
  apply hc.congr
  intro p
  have h := hessian_time_deriv_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm


set_option maxHeartbeats 800000 in
/-- The weighted time derivative is integrable jointly on every positive time slab. -/
theorem integrable_time_weighted_hessian_deriv {α a : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (b : ℝ) :
    Integrable (fun p : ℝ × E => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α)
      ((volume.restrict (Icc a b)).prod volume) := by
  let G : ℝ × E → ℝ := fun p => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α
  have hpos (p : ℝ × E) : 0 < max a p.1 := ha.trans_le (le_max_left _ _)
  have hD : Continuous (fun p : ℝ × E => DtHess (max a p.1) p.2) :=
    continuous_hessian_time_deriv_pos.comp
      (((continuous_const.max continuous_fst).subtype_mk hpos).prodMk continuous_snd)
  have hg : Continuous G := hD.norm.mul
    ((Real.continuous_rpow_const hα).comp continuous_snd.norm)
  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro r
    change Integrable (fun y : E => ‖DtHess (max a r) y‖ * ‖y‖ ^ α) volume
    exact integrable_weighted_hessian_time_deriv hα hα2 (ha.trans_le (le_max_left a r))
  · have hm := hg.norm.stronglyMeasurable.integral_prod_right' (ν := volume)
    refine (integrable_const (a ^ (α / 2 - 2) * J)).mono' hm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun r => ?_
    have he : (∫ y : E, ‖G (r, y)‖) = ∫ y : E, G (r, y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
    change (∫ y : E, ‖DtHess (max a r) y‖ * ‖y‖ ^ α) ≤ _
    rw [weighted_hessian_time_deriv_integral (ha.trans_le (le_max_left _ _))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos ha (le_max_left _ _) (by linarith)) hJ

/-- Integrating the actual time derivative bounds a kernel Hessian increment. -/
theorem norm_hessian_time_difference_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : E) :
    ‖Hess b y - Hess a y‖ ≤ ∫ r in a..b, ‖DtHess (max a r) y‖ := by
  have hD : Continuous (fun r : ℝ => DtHess (max a r) y) :=
    continuous_hessian_time_deriv_pos.comp
      (((continuous_const.max continuous_id).subtype_mk
        (fun r => ha.trans_le (le_max_left _ _))).prodMk continuous_const)
  have hd (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => Hess t y) (DtHess (max a r) y) r := by
    rw [uIcc_of_le hab] at hr
    rw [max_eq_right hr.1]
    exact (hasDerivAt_hessian_time (ha.trans_le hr.1) y).differentiableAt.hasDerivAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hD.intervalIntegrable a b)
  rw [← he]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- A weighted kernel Hessian time increment is linear away from time zero. -/
theorem weighted_hessian_time_difference {α a b : ℝ}
    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (hab : a ≤ b) :
    Integrable (fun y : E => ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) ∧
    (∫ y : E, ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) ≤
      (b - a) * a ^ (α / 2 - 2) * (∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) := by
  let G : ℝ × E → ℝ := fun p => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α
  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  have hg : Integrable G ((volume.restrict (Icc a b)).prod volume) :=
    integrable_time_weighted_hessian_deriv hα hα2 ha b
  have hiMajor := hg.integral_prod_right
  have hb (y : E) : ‖Hess b y - Hess a y‖ * ‖y‖ ^ α ≤ ∫ r in Icc a b, G (r, y) := by
    calc
      _ ≤ (∫ r in a..b, ‖DtHess (max a r) y‖) * ‖y‖ ^ α :=
        mul_le_mul_of_nonneg_right (norm_hessian_time_difference_le ha hab y)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
        exact (intervalIntegral.integral_mul_const _ _).symm
  have hH (t : ℝ) : Continuous (Hess t) :=
    (((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hi : Integrable (fun y : E => ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) :=
    hiMajor.mono' (((hH b).sub (hH a)).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        change ‖‖Hess b y - Hess a y‖ * ‖y‖ ^ α‖ ≤ _
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
        exact hb y)
  refine ⟨hi, (integral_mono hi hiMajor hb).trans ?_⟩
  rw [← integral_integral_swap hg]
  calc
    (∫ r in Icc a b, ∫ y : E, G (r, y)) ≤ ∫ _r in Icc a b, a ^ (α / 2 - 2) * J := by
      apply integral_mono_ae hg.integral_prod_left (integrable_const _)
      refine Filter.Eventually.of_forall fun r => ?_
      change (∫ y : E, ‖DtHess (max a r) y‖ * ‖y‖ ^ α) ≤ _
      rw [weighted_hessian_time_deriv_integral (ha.trans_le (le_max_left _ _))]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos ha (le_max_left _ _) (by linarith)) hJ
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_const, smul_eq_mul]
      ring

end Poincare.HeatDuhamelHessianTimeHolder
