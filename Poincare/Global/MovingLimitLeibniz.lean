import Poincare.Global.HeatDuhamelHeatEquation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace Poincare.MovingLimitLeibniz

/-- Integrable bounds on secants permit differentiation within an arbitrary real set. -/
theorem hasDerivWithinAt_integral_of_dominated_secants
    {G : ℝ → ℝ → ℝ} {D B : ℝ → ℝ} {μ : Measure ℝ} {S : Set ℝ} {t : ℝ}
    (hG : ∀ᶠ r in 𝓝[S] t, Integrable (G r) μ)
    (hGt : Integrable (G t) μ) (hB : Integrable B μ)
    (hbound : ∀ᶠ r in 𝓝[S] t, ∀ᵐ s ∂μ,
      ‖G r s - G t s‖ ≤ B s * ‖r - t‖)
    (hD : ∀ᵐ s ∂μ, HasDerivWithinAt (fun r => G r s) (D s) S t) :
    HasDerivWithinAt (fun r => ∫ s, G r s ∂μ) (∫ s, D s ∂μ) S t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hle : 𝓝[S \ {t}] t ≤ 𝓝[S] t := nhdsWithin_mono _ diff_subset
  have hi := tendsto_integral_filter_of_dominated_convergence B
    (by
      filter_upwards [hG.filter_mono hle] with r hr
      exact (hr.aestronglyMeasurable.sub hGt.aestronglyMeasurable).const_mul (r-t)⁻¹)
    (by
      filter_upwards [hbound.filter_mono hle, self_mem_nhdsWithin] with r hr hrt
      have hn : r - t ≠ 0 := sub_ne_zero.mpr (by simpa using hrt.2)
      filter_upwards [hr] with s hs
      rw [norm_mul, norm_inv]
      calc
        ‖r - t‖⁻¹ * ‖G r s - G t s‖ ≤ ‖r - t‖⁻¹ * (B s * ‖r - t‖) :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (norm_nonneg _))
        _ = B s := by rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn), mul_one])
    hB (by
      filter_upwards [hD] with s hs
      simpa only [slope, smul_eq_mul] using
        (hasDerivWithinAt_iff_tendsto_slope.mp hs))
  apply hi.congr'
  filter_upwards [hG.filter_mono hle] with r hr
  simp only [slope, smul_eq_mul, Pi.sub_apply, vsub_eq_sub,
    integral_const_mul, integral_sub hr hGt]

/-- The primitive of a continuous function has the expected derivative at both endpoints. -/
theorem hasDerivWithinAt_integral_Icc {g : ℝ → ℝ} {T t : ℝ}
    (ht : t ∈ Icc 0 T) (hg : ContinuousOn g (Icc 0 T)) :
    HasDerivWithinAt (fun r => ∫ s in (0 : ℝ)..r, g s) (g t) (Icc 0 T) t := by
  let c : ℝ → ℝ := fun r => max 0 (min T r)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (r : ℝ) : c r ∈ Icc 0 T :=
    ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (min_le_left _ _)⟩
  have hce (r : ℝ) (hr : r ∈ Icc 0 T) : c r = r := by
    simp only [c, min_eq_right hr.2, max_eq_right hr.1]
  have hg' : Continuous (fun r => g (c r)) := hg.comp_continuous hc hcm
  have hd := intervalIntegral.integral_hasDerivAt_right (hg'.intervalIntegrable 0 t)
    hg'.aestronglyMeasurable.stronglyMeasurableAtFilter hg'.continuousAt
  rw [hce t ht] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro r hr
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hr.1] at hs
  change g s = g (c s)
  rw [hce s ⟨hs.1, hs.2.trans hr.2⟩]

/-- Clipping below the diagonal reduces the moving limit to dominated secants on a fixed interval. -/
theorem hasDerivWithinAt_integral_moving_limit_of_secants
    {F D : ℝ → ℝ → ℝ} {b T t : ℝ} (ht : t ∈ Icc 0 T)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1})
    (hdiag : F t t = b)
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t)
    (hbound : ∃ B : ℝ → ℝ, IntegrableOn B (Ioc 0 T) ∧
      ∀ᶠ r in 𝓝[Icc 0 T] t, ∀ᵐ s ∂volume.restrict (Ioc 0 T),
        ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r-t‖) :
    HasDerivWithinAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, F r s)
      (b + ∫ s in (0 : ℝ)..t, D t s) (Icc 0 T) t := by
  let G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
  let d : ℝ → ℝ := (Iic t).indicator (D t)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T) :=
    hcont.comp (continuous_id.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hs, hs, le_rfl⟩)
  have hcG (r : ℝ) (hr : r ∈ Icc 0 T) : ContinuousOn (G r) (Icc 0 T) :=
    (hcont.comp ((continuous_const.max continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨hs, ⟨hr.1.trans (le_max_left _ _), max_le hr.2 hs.2⟩,
        le_max_right _ _⟩)).sub hcdiag
  have hiG (r : ℝ) (hr : r ∈ Icc 0 T) : IntegrableOn (G r) (Ioc 0 T) :=
    (hcG r hr).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  obtain ⟨B, hB, hb⟩ := hbound
  have hdG : HasDerivWithinAt (fun r => ∫ s in Ioc 0 T, G r s)
      (∫ s in Ioc 0 T, d s) (Icc 0 T) t := by
    apply hasDerivWithinAt_integral_of_dominated_secants
      (B := B) (Eventually.mono self_mem_nhdsWithin hiG) (hiG t ht) hB
    · filter_upwards [hb] with r hr
      filter_upwards [hr] with s hs
      simpa only [G, sub_sub_sub_cancel_right] using hs
    · filter_upwards [ae_restrict_mem measurableSet_Ioc,
        (volume.restrict (Ioc 0 T)).ae_ne t] with s hs hst
      by_cases hlt : s < t
      · have hd := (hderiv s ⟨hs.1, hlt⟩).sub_const (F s s)
        have he : (G · s) =ᶠ[𝓝 t] (fun r => F r s - F s s) := by
          filter_upwards [Ioi_mem_nhds hlt] with r hr
          simp only [G, max_eq_left (le_of_lt (show s < r from hr))]
        have hd' := hd.congr_of_eventuallyEq he
        simpa only [d, indicator_of_mem (show s ∈ Iic t from hlt.le)] using
          hd'.hasDerivWithinAt (s := Icc 0 T)
      · have hgt : t < s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
        have he : (G · s) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          filter_upwards [Iio_mem_nhds hgt] with r hr
          simp only [G, max_eq_right (le_of_lt (show r < s from hr)), sub_self]
        have hd' := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
        simpa only [d, indicator_of_notMem (show s ∉ Iic t from not_le.mpr hgt)] using
          hd'.hasDerivWithinAt (s := Icc 0 T)
  have hdint : (∫ s in Ioc 0 T, d s) = ∫ s in (0 : ℝ)..t, D t s := by
    rw [← intervalIntegral.integral_of_le hT]
    exact intervalIntegral.integral_indicator (f := D t) ht
  rw [hdint] at hdG
  have hde := hdG.add (hasDerivWithinAt_integral_Icc ht hcdiag)
  rw [hdiag, add_comm (∫ s in (0 : ℝ)..t, D t s) b] at hde
  apply hde.congr_of_mem _ ht
  intro r hr
  have he : G r = (Iic r).indicator (fun s => F r s - F s s) := by
    funext s
    by_cases hs : s ≤ r
    · simp only [G, indicator_of_mem (show s ∈ Iic r from hs), max_eq_left hs]
    · simp only [G, indicator_of_notMem (show s ∉ Iic r from hs), max_eq_right (le_of_not_ge hs), sub_self]
  change (∫ s in (0 : ℝ)..r, F r s) =
    (∫ s in Ioc 0 T, G r s) + ∫ s in (0 : ℝ)..r, F s s
  rw [← intervalIntegral.integral_of_le hT, he]
  have hcut : (∫ s in (0 : ℝ)..T, (Iic r).indicator (fun s => F r s - F s s) s) =
      ∫ s in (0 : ℝ)..r, F r s - F s s :=
    intervalIntegral.integral_indicator hr
  rw [hcut]
  have hcF : ContinuousOn (F r) (Icc 0 r) :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨⟨hs.1, hs.2.trans hr.2⟩, hr, hs.2⟩)
  rw [intervalIntegral.integral_sub (hcF.intervalIntegrable_of_Icc hr.1)
    ((hcdiag.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1)]
  ring

/-- An interior derivative comparison controls increments even at singular endpoints. -/
theorem abs_sub_le_of_deriv_comparison
    {g g' v v' : ℝ → ℝ} {a z : ℝ} (haz : a ≤ z)
    (hg : ContinuousOn g (Icc a z)) (hv : ContinuousOn v (Icc a z))
    (hdg : ∀ r ∈ Ioo a z, HasDerivAt g (g' r) r)
    (hdv : ∀ r ∈ Ioo a z, HasDerivAt v (v' r) r)
    (hb : ∀ r ∈ Ioo a z, |g' r| ≤ v' r) :
    |g z - g a| ≤ v z - v a := by
  have hm : MonotoneOn (fun r => v r - g r) (Icc a z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hv.sub hg)
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hdv r hr).sub (hdg r hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      change 0 ≤ deriv (v - g) r
      rw [((hdv r hr).sub (hdg r hr)).deriv]
      exact sub_nonneg.mpr ((le_abs_self _).trans (hb r hr))
  have hp : MonotoneOn (fun r => v r + g r) (Icc a z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hv.add hg)
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hdv r hr).add (hdg r hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      change 0 ≤ deriv (v + g) r
      rw [((hdv r hr).add (hdg r hr)).deriv]
      have := (abs_le.mp (hb r hr)).1
      linarith
  have h1 := hm (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz) haz
  have h2 := hp (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz) haz
  exact abs_le.mpr ⟨by dsimp at h2; linarith, by dsimp at h1; linarith⟩

/-- Integrating a singular power bound requires no derivative at the initial endpoint. -/
theorem abs_sub_le_rpow_of_deriv_bound
    {g g' : ℝ → ℝ} {s T u v C β : ℝ} (hβ : 0 < β)
    (hc : ContinuousOn g (Icc s T))
    (hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r)
    (hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r-s) ^ (β-1))
    (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    |g v - g u| ≤ (C / β) * ((v-s)^β - (u-s)^β) := by
  have hdv (r : ℝ) (hr : r ∈ Ioo u v) :
      HasDerivAt (fun r : ℝ => (C / β) * (r-s)^β) (C * (r-s)^(β-1)) r := by
    have hp := (((hasDerivAt_id r).sub_const s).rpow_const (p := β)
      (Or.inl (ne_of_gt (sub_pos.mpr (hsu.trans_lt hr.1))))).const_mul (C / β)
    simp only [id_eq] at hp
    convert hp using 1 <;> field_simp [hβ.ne'] <;> ring
  have hi := abs_sub_le_of_deriv_comparison huv
    (hc.mono (Icc_subset_Icc hsu hvT))
    (continuousOn_const.mul ((continuous_id.sub continuous_const).continuousOn.rpow_const
      (fun _ _ => Or.inr hβ.le)))
    (fun r hr => hd r ⟨hsu.trans_lt hr.1, hr.2.le.trans hvT⟩)
    hdv (fun r hr => hb r ⟨hsu.trans_lt hr.1, hr.2.le.trans hvT⟩)
  change |g v - g u| ≤ (C / β) * (v-s)^β - (C / β) * (u-s)^β at hi
  nlinarith [hi]

/-- A fractional power has an integrable secant bound measured from a positive base point. -/
theorem abs_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hx : 0 ≤ x) (hy : 0 < y) :
    |x^β - y^β| ≤ y^(β-1) * |x-y| := by
  have hyid : y^β = y * y^(β-1) := by
    rw [Real.rpow_sub_one hy.ne']
    field_simp
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst x
    rw [Real.zero_rpow hβ.ne', zero_sub, abs_neg,
      abs_of_nonneg (Real.rpow_nonneg hy.le _), zero_sub, abs_neg, abs_of_pos hy, hyid]
    exact le_of_eq (mul_comm _ _)
  have hxid : x^β = x * x^(β-1) := by
    rw [Real.rpow_sub_one hx0.ne']
    field_simp
  rcases le_total x y with hxy | hyx
  · have hp := Real.rpow_le_rpow hx hxy hβ.le
    have hq := Real.rpow_le_rpow_of_nonpos hx0 hxy (sub_nonpos.mpr hβ1)
    rw [abs_of_nonpos (sub_nonpos.mpr hp), abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hm := mul_le_mul_of_nonneg_left hq hx
    rw [hxid, hyid]
    nlinarith [hm]
  · have hp := Real.rpow_le_rpow hy.le hyx hβ.le
    have hq := Real.rpow_le_rpow_of_nonpos hy hyx (sub_nonpos.mpr hβ1)
    rw [abs_of_nonneg (sub_nonneg.mpr hp), abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hm := mul_le_mul_of_nonneg_left hq hx
    rw [hxid, hyid]
    nlinarith [hm]

/-- The same bound survives clipping at zero, from either side of the base point. -/
theorem abs_clipped_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hy : y ≠ 0) :
    |(max x 0)^β - (max y 0)^β| ≤ |y|^(β-1) * |x-y| := by
  have hb : 0 ≤ |y|^(β-1) := Real.rpow_nonneg (abs_nonneg _) _
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · rw [max_eq_right hyneg.le, Real.zero_rpow hβ.ne', sub_zero,
      abs_of_nonneg (Real.rpow_nonneg (le_max_right x 0) _), abs_of_neg hyneg]
    by_cases hx : x ≤ 0
    · simp only [max_eq_right hx, Real.zero_rpow hβ.ne']
      exact mul_nonneg (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) _) (abs_nonneg _)
    have hxpos : 0 < x := lt_of_not_ge hx
    rw [max_eq_left hxpos.le, abs_of_pos (sub_pos.mpr (hyneg.trans hxpos))]
    rcases le_total x (-y) with hxy | hyx
    · have hp := Real.rpow_le_rpow hxpos.le hxy hβ.le
      have he : (-y)^β = (-y) * (-y)^(β-1) := by
        rw [Real.rpow_sub_one (neg_ne_zero.mpr hy)]
        field_simp
      rw [he] at hp
      have hq := mul_nonneg hxpos.le (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) (β-1))
      nlinarith
    · have hp := Real.rpow_le_rpow_of_nonpos (neg_pos.mpr hyneg) hyx (sub_nonpos.mpr hβ1)
      have he : x^β = x * x^(β-1) := by
        rw [Real.rpow_sub_one hxpos.ne']
        field_simp
      rw [he]
      have hq := mul_le_mul_of_nonneg_left hp hxpos.le
      have hz := mul_nonneg (neg_nonneg.mpr hyneg.le)
        (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) (β-1))
      nlinarith
  · rw [max_eq_left hypos.le, abs_of_pos hypos]
    have hh := abs_rpow_sub_le hβ hβ1 (le_max_right x 0) hypos
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hypos.le _)
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx]
    · have hx' : x < 0 := lt_of_not_ge hx
      rw [max_eq_right hx'.le, zero_sub, abs_neg, abs_of_pos hypos,
        abs_of_neg (sub_neg.mpr (hx'.trans hypos))]
      linarith

/-- The singularity of the secant majorant is integrable on either side of its base point. -/
theorem intervalIntegrable_abs_sub_rpow {β T t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume 0 T := by
  have hl : IntervalIntegrable (fun s : ℝ => (t-s)^(β-1)) volume 0 t := by
    simpa only [sub_zero, sub_self] using
      ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t)
        (r := β-1) (by linarith)).comp_sub_left t).symm
  have hr : IntervalIntegrable (fun s : ℝ => (s-t)^(β-1)) volume t T := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := T-t)
        (r := β-1) (by linarith)).comp_sub_right t
  have hl' : IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume 0 t := by
    apply hl.congr
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    simp only [abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hr' : IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume t T := by
    apply hr.congr
    intro s hs
    rw [uIoc_of_le ht.2] at hs
    simp only [abs_of_nonpos (sub_nonpos.mpr hs.1.le), neg_sub]
  exact hl'.trans hr'

/-- A power bound for the derivative supplies a common majorant for clipped secants. -/
theorem clipped_secant_le_of_deriv_rpow_bound
    {g g' : ℝ → ℝ} {s T r t C β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hC : 0 ≤ C) (hs : s ≤ T) (hr : r ≤ T) (ht : t ≤ T) (hst : t ≠ s)
    (hc : ContinuousOn g (Icc s T))
    (hd : ∀ z ∈ Ioc s T, HasDerivAt g (g' z) z)
    (hb : ∀ z ∈ Ioc s T, |g' z| ≤ C * (z-s)^(β-1)) :
    |g (max r s) - g (max t s)| ≤ (C / β) * |t-s|^(β-1) * |r-t| := by
  have hCβ : 0 ≤ C / β := div_nonneg hC hβ.le
  have hinc (a b : ℝ) (ha : a ∈ Icc s T) (hb' : b ∈ Icc s T) :
      |g a - g b| ≤ (C / β) * |(a-s)^β - (b-s)^β| := by
    rcases le_total a b with hab | hba
    · have hp := Real.rpow_le_rpow (sub_nonneg.mpr ha.1) (sub_le_sub_right hab s) hβ.le
      rw [abs_sub_comm (g a) (g b), abs_sub_comm ((a-s)^β) ((b-s)^β),
        abs_of_nonneg (sub_nonneg.mpr hp)]
      exact abs_sub_le_rpow_of_deriv_bound hβ hc hd hb ha.1 hab hb'.2
    · have hp := Real.rpow_le_rpow (sub_nonneg.mpr hb'.1) (sub_le_sub_right hba s) hβ.le
      rw [abs_of_nonneg (sub_nonneg.mpr hp)]
      exact abs_sub_le_rpow_of_deriv_bound hβ hc hd hb hb'.1 hba ha.2
  have hi := hinc (max r s) (max t s)
    ⟨le_max_right _ _, max_le hr hs⟩ ⟨le_max_right _ _, max_le ht hs⟩
  have hp := abs_clipped_rpow_sub_le (x := r-s) (y := t-s) hβ hβ1
    (sub_ne_zero.mpr hst)
  have he (z : ℝ) : max z s - s = max (z-s) 0 := by
    rw [← max_sub_sub_right, sub_self]
  rw [he r, he t] at hi
  have he' : r-s-(t-s) = r-t := by ring
  rw [he'] at hp
  exact hi.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hCβ)

/-- The Leibniz rule on a closed time interval under an integrable diagonal power singularity. -/
theorem hasDerivWithinAt_integral_moving_limit
    {F D : ℝ → ℝ → ℝ} {b T t C β : ℝ} (ht : t ∈ Icc 0 T)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1})
    (hdiag : F t t = b)
    (hderiv : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T,
      HasDerivAt (fun ρ => F ρ s) (D r s) r)
    (hbound : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T, |D r s| ≤ C * (r-s)^(β-1)) :
    HasDerivWithinAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, F r s)
      (b + ∫ s in (0 : ℝ)..t, D t s) (Icc 0 T) t := by
  apply hasDerivWithinAt_integral_moving_limit_of_secants ht hcont hdiag
    (fun s hs => hderiv s ⟨hs.1.le, hs.2.le.trans ht.2⟩ t ⟨hs.2, ht.2⟩)
  refine ⟨fun s => (C / β) * |t-s|^(β-1), ?_, ?_⟩
  · exact ((intervalIntegrable_abs_sub_rpow hβ ht).const_mul (C / β)).1
  · filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc 0 T)).ae_ne t] with s hs hst
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    have hc : ContinuousOn (fun r => F r s) (Icc s T) :=
      hcont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun z hz => ⟨hsT, ⟨hs.1.le.trans hz.1, hz.2⟩, hz.1⟩)
    simpa only [Real.norm_eq_abs] using
      clipped_secant_le_of_deriv_rpow_bound hβ hβ1 hC hs.2 hr.2 ht.2 hst.symm
        hc (hderiv s hsT) (hbound s hsT)

end Poincare.MovingLimitLeibniz
