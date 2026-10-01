import Poincare.Global.FiniteExtinctionSurgerySchedule

/-!
# Scalar-curvature Riccati barriers

In dimension three the scalar-curvature minimum along a smooth Ricci-flow
segment satisfies the maximum-principle inequality

`r' ≥ (2/3) r²`.

On any interval where `r` is negative, the quantity `-r⁻¹` therefore has
right derivative at least `2/3`.  This file integrates that elementary
Riccati comparison, proves the familiar lower barrier

`r(t) ≥ -3 / (2 (t + C))`,

and propagates it across surgery jumps that do not decrease the scalar
minimum.  The analytic statements are independent of the still-missing
geometric maximum-principle input.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Interval Topology

namespace Poincare

/-- Derivative of the negative reciprocal, in the normalization used for
scalar-curvature Riccati comparison. -/
theorem hasDerivWithinAt_neg_inv
    {r : ℝ → ℝ} {dr t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt r dr s t) (hne : r t ≠ 0) :
    HasDerivWithinAt (fun x => -(r x)⁻¹) (dr / (r t) ^ 2) s t := by
  convert (h.inv hne).neg using 1 <;> ring

/-- If a negative function satisfies `r' ≥ κ r²`, its negative reciprocal
grows at least linearly with slope `κ`. -/
theorem negative_reciprocal_growth_bound
    {a b κ : ℝ} (hab : a ≤ b)
    (r dr : ℝ → ℝ)
    (hcont : ContinuousOn r (Set.Icc a b))
    (hneg : ∀ t ∈ Set.Icc a b, r t < 0)
    (hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt r (dr t) (Set.Ioi t) t)
    (hriccati : ∀ t ∈ Set.Ioo a b, κ * (r t) ^ 2 ≤ dr t) :
    κ * (b - a) ≤ -(r b)⁻¹ - (-(r a)⁻¹) := by
  let q : ℝ → ℝ := fun t => -(r t)⁻¹
  let dq : ℝ → ℝ := fun t => dr t / (r t) ^ 2
  have hqcont : ContinuousOn q (Set.Icc a b) := by
    simpa [q] using (hcont.inv₀ (fun t ht => (hneg t ht).ne)).neg
  have hqderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt q (dq t) (Set.Ioi t) t := by
    intro t ht
    exact hasDerivWithinAt_neg_inv (hderiv t ht)
      (hneg t ⟨ht.1.le, ht.2.le⟩).ne
  have hdq : ∀ t ∈ Set.Ioo a b, κ ≤ dq t := by
    intro t ht
    have hrsq : 0 < (r t) ^ 2 := sq_pos_of_ne_zero
      (hneg t ⟨ht.1.le, ht.2.le⟩).ne
    rw [le_div_iff₀ hrsq]
    exact hriccati t ht
  have hconstInt : IntegrableOn (fun _ : ℝ => κ) (Set.Icc a b) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => κ) (Set.Icc a b)).integrableOn_Icc
  have hbound := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    hab hqcont hqderiv hconstInt hdq
  have hint : (∫ _t : ℝ in a..b, κ) = κ * (b - a) := by
    simp [mul_comm]
  simpa [q, hint] using hbound

/-- A nonnegative Riccati right derivative makes the scalar-minimum function
monotone on the whole smooth interval. -/
theorem riccati_monotoneOn
    {a b κ : ℝ} (hab : a ≤ b) (hκ : 0 ≤ κ)
    (r dr : ℝ → ℝ)
    (hcont : ContinuousOn r (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt r (dr t) (Set.Ioi t) t)
    (hriccati : ∀ t ∈ Set.Ioo a b, κ * (r t) ^ 2 ≤ dr t) :
    MonotoneOn r (Set.Icc a b) := by
  intro x hx y hy hxy
  have hcontXY : ContinuousOn r (Set.Icc x y) :=
    hcont.mono (Set.Icc_subset_Icc hx.1 hy.2)
  have hderivXY : ∀ t ∈ Set.Ioo x y,
      HasDerivWithinAt r (dr t) (Set.Ioi t) t := by
    intro t ht
    exact hderiv t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
  have hdrNonneg : ∀ t ∈ Set.Ioo x y, 0 ≤ dr t := by
    intro t ht
    have hric := hriccati t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
    exact (mul_nonneg hκ (sq_nonneg (r t))).trans hric
  have hzeroInt : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc x y) :=
    integrableOn_zero
  have hbound := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    hxy hcontXY hderivXY hzeroInt hdrNonneg
  have hdiff : 0 ≤ r y - r x := by
    simpa only [intervalIntegral.integral_zero] using hbound
  linarith

/-- Algebraic conversion of an initial negative lower bound into a lower
bound for the negative reciprocal. -/
theorem negative_reciprocal_initial_bound
    {r L : ℝ} (hr : r < 0) (hL : 0 < L) (hbarrier : -L⁻¹ ≤ r) :
    L ≤ -r⁻¹ := by
  have hnegpos : 0 < -r := neg_pos.mpr hr
  rw [show -r⁻¹ = 1 / (-r) by field_simp]
  rw [le_div_iff₀ hnegpos]
  have hmul := mul_le_mul_of_nonneg_left hbarrier hL.le
  have hrewrite : L * (-L⁻¹) = -1 := by
    field_simp
  rw [hrewrite] at hmul
  nlinarith

/-- Algebraic conversion back from a negative-reciprocal lower bound to a
lower bound for the original negative quantity. -/
theorem lower_bound_of_negative_reciprocal_bound
    {r L : ℝ} (hr : r < 0) (hL : 0 < L) (hrecip : L ≤ -r⁻¹) :
    -L⁻¹ ≤ r := by
  have hnegpos : 0 < -r := neg_pos.mpr hr
  have hmul : L * (-r) ≤ 1 := by
    have hrecip' : L ≤ 1 / (-r) := by
      simpa [one_div] using hrecip
    exact (le_div_iff₀ hnegpos).mp hrecip'
  have heq : -(L⁻¹) = -1 / L := by ring
  rw [heq]
  rw [div_le_iff₀ hL]
  nlinarith

/-- Riccati lower barrier on a single smooth interval.  The theorem is stated
on the negative branch; if scalar curvature becomes nonnegative, the same
negative reciprocal barrier is automatically no longer needed. -/
theorem riccati_lower_barrier_of_negative
    {a b κ C : ℝ} (hab : a ≤ b) (hκ : 0 < κ) (hC : 0 < C)
    (r dr : ℝ → ℝ)
    (hcont : ContinuousOn r (Set.Icc a b))
    (hneg : ∀ t ∈ Set.Icc a b, r t < 0)
    (hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt r (dr t) (Set.Ioi t) t)
    (hriccati : ∀ t ∈ Set.Ioo a b, κ * (r t) ^ 2 ≤ dr t)
    (hinitial : -(κ * C)⁻¹ ≤ r a) :
    -(κ * (C + (b - a)))⁻¹ ≤ r b := by
  have hκC : 0 < κ * C := mul_pos hκ hC
  have htime : 0 < κ * (C + (b - a)) := by
    exact mul_pos hκ (add_pos_of_pos_of_nonneg hC (sub_nonneg.mpr hab))
  have hqa : κ * C ≤ -(r a)⁻¹ :=
    negative_reciprocal_initial_bound (hneg a ⟨le_rfl, hab⟩) hκC hinitial
  have hgrowth := negative_reciprocal_growth_bound
    hab r dr hcont hneg hderiv hriccati
  have hqb : κ * (C + (b - a)) ≤ -(r b)⁻¹ := by
    nlinarith
  exact lower_bound_of_negative_reciprocal_bound
    (hneg b ⟨hab, le_rfl⟩) htime hqb

/-- Riccati lower barrier without a negativity hypothesis.  If the terminal
value is nonnegative the conclusion is immediate; otherwise Riccati
monotonicity forces the entire preceding interval onto the negative branch,
where `riccati_lower_barrier_of_negative` applies. -/
theorem riccati_lower_barrier
    {a b κ C : ℝ} (hab : a ≤ b) (hκ : 0 < κ) (hC : 0 < C)
    (r dr : ℝ → ℝ)
    (hcont : ContinuousOn r (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt r (dr t) (Set.Ioi t) t)
    (hriccati : ∀ t ∈ Set.Ioo a b, κ * (r t) ^ 2 ≤ dr t)
    (hinitial : -(κ * C)⁻¹ ≤ r a) :
    -(κ * (C + (b - a)))⁻¹ ≤ r b := by
  have hscale : 0 < κ * (C + (b - a)) :=
    mul_pos hκ (add_pos_of_pos_of_nonneg hC (sub_nonneg.mpr hab))
  by_cases hb : 0 ≤ r b
  · exact (neg_nonpos.mpr (inv_nonneg.mpr hscale.le)).trans hb
  · have hbneg : r b < 0 := lt_of_not_ge hb
    have hmonoR : MonotoneOn r (Set.Icc a b) :=
      riccati_monotoneOn hab hκ.le r dr hcont hderiv hriccati
    have hneg : ∀ t ∈ Set.Icc a b, r t < 0 := by
      intro t ht
      exact (hmonoR ht ⟨hab, le_rfl⟩ ht.2).trans_lt hbneg
    exact riccati_lower_barrier_of_negative
      hab hκ hC r dr hcont hneg hderiv hriccati hinitial

/-- The dimension-three scalar-curvature minimum barrier in its standard
normalization. -/
theorem three_dimensional_scalar_curvature_lower_barrier_of_negative
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 < C)
    (r dr : ℝ → ℝ)
    (hcont : ContinuousOn r (Set.Icc a b))
    (hneg : ∀ t ∈ Set.Icc a b, r t < 0)
    (hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt r (dr t) (Set.Ioi t) t)
    (hriccati : ∀ t ∈ Set.Ioo a b,
      ((2 : ℝ) / 3) * (r t) ^ 2 ≤ dr t)
    (hinitial : -(3 / (2 * C)) ≤ r a) :
    -(3 / (2 * (C + (b - a)))) ≤ r b := by
  have hκ : (0 : ℝ) < 2 / 3 := by norm_num
  have hraw := riccati_lower_barrier_of_negative
    hab hκ hC r dr hcont hneg hderiv hriccati
      (show -(((2 : ℝ) / 3) * C)⁻¹ ≤ r a by
        convert hinitial using 1 <;> field_simp <;> ring)
  convert hraw using 1 <;> field_simp <;> ring

/-- Standard three-dimensional scalar-curvature barrier without assuming the
minimum stays negative. -/
theorem three_dimensional_scalar_curvature_lower_barrier
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 < C)
    (r dr : ℝ → ℝ)
    (hcont : ContinuousOn r (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt r (dr t) (Set.Ioi t) t)
    (hriccati : ∀ t ∈ Set.Ioo a b,
      ((2 : ℝ) / 3) * (r t) ^ 2 ≤ dr t)
    (hinitial : -(3 / (2 * C)) ≤ r a) :
    -(3 / (2 * (C + (b - a)))) ≤ r b := by
  have hκ : (0 : ℝ) < 2 / 3 := by norm_num
  have hraw := riccati_lower_barrier
    hab hκ hC r dr hcont hderiv hriccati
      (show -(((2 : ℝ) / 3) * C)⁻¹ ≤ r a by
        convert hinitial using 1 <;> field_simp <;> ring)
  convert hraw using 1 <;> field_simp <;> ring

/-- Negative-reciprocal growth across segment-indexed Ricci-flow pieces.  A
surgery jump is allowed provided it does not decrease the scalar minimum. -/
theorem segmented_negative_reciprocal_growth_bound
    {κ : ℝ} (r dr : ℕ → ℝ → ℝ) (start : ℕ → ℝ) (n : ℕ)
    (hmono : ∀ k < n, start k ≤ start (k + 1))
    (hcont : ∀ k < n,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hneg : ∀ k ≤ n, r k (start k) < 0)
    (hnegSegment : ∀ k < n, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      r k t < 0)
    (hderiv : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hriccati : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      κ * (r k t) ^ 2 ≤ dr k t)
    (hsurgery : ∀ k < n,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1))) :
    κ * (start n - start 0) ≤
      -(r n (start n))⁻¹ - (-(r 0 (start 0))⁻¹) := by
  let q : ℕ → ℝ := fun k => -(r k (start k))⁻¹
  have hstep : ∀ k < n,
      -q (k + 1) - (-q k) ≤
        -(κ * (start (k + 1) - start k)) := by
    intro k hk
    have hgrowth := negative_reciprocal_growth_bound
      (hmono k hk) (r k) (dr k) (hcont k hk) (hnegSegment k hk)
      (hderiv k hk) (hriccati k hk)
    have hjump : -(r k (start (k + 1)))⁻¹ ≤
        -(r (k + 1) (start (k + 1)))⁻¹ := by
      have hleft := hnegSegment k hk (start (k + 1))
        ⟨hmono k hk, le_rfl⟩
      have hright := hneg (k + 1) (Nat.succ_le_iff.mpr hk)
      have hposleft : 0 < -r k (start (k + 1)) := neg_pos.mpr hleft
      have hposright : 0 < -r (k + 1) (start (k + 1)) := neg_pos.mpr hright
      have hnegOrder : -r (k + 1) (start (k + 1)) ≤
          -r k (start (k + 1)) := neg_le_neg (hsurgery k hk)
      have hinv : (-r k (start (k + 1)))⁻¹ ≤
          (-r (k + 1) (start (k + 1)))⁻¹ :=
        (inv_le_inv₀ hposleft hposright).mpr hnegOrder
      simpa only [inv_neg] using hinv
    dsimp [q]
    nlinarith
  have htel := sub_le_sum_range_of_step_decay (fun k => -q k)
    (fun k => -(κ * (start (k + 1) - start k))) n hstep
  have htimeSum :
      ∑ k ∈ Finset.range n, (start (k + 1) - start k) =
        start n - start 0 := by
    calc
      (∑ k ∈ Finset.range n, (start (k + 1) - start k)) =
          -(∑ k ∈ Finset.range n, (start k - start (k + 1))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = -(start 0 - start n) := by rw [Finset.sum_range_sub']
      _ = start n - start 0 := by ring
  have hforcing :
      ∑ k ∈ Finset.range n, -(κ * (start (k + 1) - start k)) =
        -(κ * (start n - start 0)) := by
    calc
      (∑ k ∈ Finset.range n, -(κ * (start (k + 1) - start k))) =
          -κ * ∑ k ∈ Finset.range n, (start (k + 1) - start k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = -(κ * (start n - start 0)) := by rw [htimeSum]; ring
  rw [hforcing] at htel
  dsimp [q] at htel
  nlinarith

/-- Riccati lower barrier propagated through finitely many smooth segments and
nondecreasing scalar-minimum surgery jumps. -/
theorem segmented_riccati_lower_barrier_of_negative
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (r dr : ℕ → ℝ → ℝ) (start : ℕ → ℝ) (n : ℕ)
    (hduration : 0 ≤ start n - start 0)
    (hmono : ∀ k < n, start k ≤ start (k + 1))
    (hcont : ∀ k < n,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hneg : ∀ k ≤ n, r k (start k) < 0)
    (hnegSegment : ∀ k < n, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      r k t < 0)
    (hderiv : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hriccati : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      κ * (r k t) ^ 2 ≤ dr k t)
    (hsurgery : ∀ k < n,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hinitial : -(κ * C)⁻¹ ≤ r 0 (start 0)) :
    -(κ * (C + (start n - start 0)))⁻¹ ≤ r n (start n) := by
  have hκC : 0 < κ * C := mul_pos hκ hC
  have hterminalScale : 0 < κ * (C + (start n - start 0)) :=
    mul_pos hκ (add_pos_of_pos_of_nonneg hC hduration)
  have hq0 : κ * C ≤ -(r 0 (start 0))⁻¹ :=
    negative_reciprocal_initial_bound (hneg 0 (Nat.zero_le n)) hκC hinitial
  have hgrowth := segmented_negative_reciprocal_growth_bound
    r dr start n hmono hcont hneg hnegSegment hderiv hriccati hsurgery
  have hqn : κ * (C + (start n - start 0)) ≤
      -(r n (start n))⁻¹ := by
    nlinarith
  exact lower_bound_of_negative_reciprocal_bound
    (hneg n le_rfl) hterminalScale hqn

/-- Standard three-dimensional scalar-curvature lower barrier across a finite
surgery schedule. -/
theorem three_dimensional_scalar_curvature_segmented_lower_barrier_of_negative
    {C : ℝ} (hC : 0 < C)
    (r dr : ℕ → ℝ → ℝ) (start : ℕ → ℝ) (n : ℕ)
    (hduration : 0 ≤ start n - start 0)
    (hmono : ∀ k < n, start k ≤ start (k + 1))
    (hcont : ∀ k < n,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hneg : ∀ k ≤ n, r k (start k) < 0)
    (hnegSegment : ∀ k < n, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      r k t < 0)
    (hderiv : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hriccati : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      ((2 : ℝ) / 3) * (r k t) ^ 2 ≤ dr k t)
    (hsurgery : ∀ k < n,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hinitial : -(3 / (2 * C)) ≤ r 0 (start 0)) :
    -(3 / (2 * (C + (start n - start 0)))) ≤ r n (start n) := by
  have hκ : (0 : ℝ) < 2 / 3 := by norm_num
  have hraw := segmented_riccati_lower_barrier_of_negative
    hκ hC r dr start n hduration hmono hcont hneg hnegSegment hderiv
      hriccati hsurgery
      (show -(((2 : ℝ) / 3) * C)⁻¹ ≤ r 0 (start 0) by
        convert hinitial using 1 <;> field_simp <;> ring)
  convert hraw using 1 <;> field_simp <;> ring

/-- Pointwise form of the segmented Riccati barrier.  It first propagates the
barrier to the beginning of the chosen segment and then applies the smooth
comparison on the partial interval ending at `t`. -/
theorem segmented_riccati_pointwise_lower_barrier_of_negative
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (r dr : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hcont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hnegStart : ∀ k, r k (start k) < 0)
    (hnegSegment : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      r k t < 0)
    (hderiv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hriccati : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      κ * (r k t) ^ 2 ≤ dr k t)
    (hsurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hinitial : -(κ * C)⁻¹ ≤ r 0 (start 0)) :
    ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      -(κ * (C + (t - start 0)))⁻¹ ≤ r k t := by
  intro k t ht
  have hstartMonotone : Monotone start :=
    monotone_nat_of_le_succ hmono
  have hduration : 0 ≤ start k - start 0 :=
    sub_nonneg.mpr (hstartMonotone (Nat.zero_le k))
  have hendpoint :
      -(κ * (C + (start k - start 0)))⁻¹ ≤ r k (start k) := by
    exact segmented_riccati_lower_barrier_of_negative
      hκ hC r dr start k hduration
      (fun j hj => hmono j)
      (fun j hj => hcont j)
      (fun j hj => hnegStart j)
      (fun j hj s hs => hnegSegment j s hs)
      (fun j hj s hs => hderiv j s hs)
      (fun j hj s hs => hriccati j s hs)
      (fun j hj => hsurgery j) hinitial
  have hCk : 0 < C + (start k - start 0) :=
    add_pos_of_pos_of_nonneg hC hduration
  have hcontPartial : ContinuousOn (r k) (Set.Icc (start k) t) :=
    (hcont k).mono (by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩)
  have hnegPartial : ∀ s ∈ Set.Icc (start k) t, r k s < 0 := by
    intro s hs
    exact hnegSegment k s ⟨hs.1, hs.2.trans ht.2⟩
  have hderivPartial : ∀ s ∈ Set.Ioo (start k) t,
      HasDerivWithinAt (r k) (dr k s) (Set.Ioi s) s := by
    intro s hs
    exact hderiv k s ⟨hs.1, hs.2.trans_le ht.2⟩
  have hriccatiPartial : ∀ s ∈ Set.Ioo (start k) t,
      κ * (r k s) ^ 2 ≤ dr k s := by
    intro s hs
    exact hriccati k s ⟨hs.1, hs.2.trans_le ht.2⟩
  have hpartial := riccati_lower_barrier_of_negative
    ht.1 hκ hCk (r k) (dr k) hcontPartial hnegPartial
      hderivPartial hriccatiPartial hendpoint
  convert hpartial using 1 <;> ring

/-- Pointwise segmented Riccati barrier without any negativity assumption.
The proof propagates the lower barrier inductively across each smooth segment
using `riccati_lower_barrier`, then across surgery by monotonicity of the
scalar minimum. -/
theorem segmented_riccati_pointwise_lower_barrier
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (r dr : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hcont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hderiv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hriccati : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      κ * (r k t) ^ 2 ≤ dr k t)
    (hsurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hinitial : -(κ * C)⁻¹ ≤ r 0 (start 0)) :
    ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      -(κ * (C + (t - start 0)))⁻¹ ≤ r k t := by
  have hstartMonotone : Monotone start := monotone_nat_of_le_succ hmono
  have hendpoint : ∀ k,
      -(κ * (C + (start k - start 0)))⁻¹ ≤ r k (start k) := by
    intro k
    induction k with
    | zero => simpa using hinitial
    | succ k ih =>
        have hduration : 0 ≤ start k - start 0 :=
          sub_nonneg.mpr (hstartMonotone (Nat.zero_le k))
        have hCk : 0 < C + (start k - start 0) :=
          add_pos_of_pos_of_nonneg hC hduration
        have hsmooth := riccati_lower_barrier
          (hmono k) hκ hCk (r k) (dr k) (hcont k) (hderiv k)
            (hriccati k) ih
        have hsmooth' :
            -(κ * (C + (start (k + 1) - start 0)))⁻¹ ≤
              r k (start (k + 1)) := by
          convert hsmooth using 1 <;> ring
        exact hsmooth'.trans (hsurgery k)
  intro k t ht
  have hduration : 0 ≤ start k - start 0 :=
    sub_nonneg.mpr (hstartMonotone (Nat.zero_le k))
  have hCk : 0 < C + (start k - start 0) :=
    add_pos_of_pos_of_nonneg hC hduration
  have hcontPartial : ContinuousOn (r k) (Set.Icc (start k) t) :=
    (hcont k).mono (by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩)
  have hderivPartial : ∀ s ∈ Set.Ioo (start k) t,
      HasDerivWithinAt (r k) (dr k s) (Set.Ioi s) s := by
    intro s hs
    exact hderiv k s ⟨hs.1, hs.2.trans_le ht.2⟩
  have hriccatiPartial : ∀ s ∈ Set.Ioo (start k) t,
      κ * (r k s) ^ 2 ≤ dr k s := by
    intro s hs
    exact hriccati k s ⟨hs.1, hs.2.trans_le ht.2⟩
  have hpartial := riccati_lower_barrier
    ht.1 hκ hCk (r k) (dr k) hcontPartial hderivPartial
      hriccatiPartial (hendpoint k)
  convert hpartial using 1 <;> ring

/-- Pointwise three-dimensional scalar-curvature barrier on every smooth
segment of an infinite locally finite surgery schedule. -/
theorem three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier_of_negative
    {C : ℝ} (hC : 0 < C)
    (r dr : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hcont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hnegStart : ∀ k, r k (start k) < 0)
    (hnegSegment : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      r k t < 0)
    (hderiv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hriccati : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      ((2 : ℝ) / 3) * (r k t) ^ 2 ≤ dr k t)
    (hsurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hinitial : -(3 / (2 * C)) ≤ r 0 (start 0)) :
    ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      -(3 / (2 * (C + (t - start 0)))) ≤ r k t := by
  have hκ : (0 : ℝ) < 2 / 3 := by norm_num
  have hraw := segmented_riccati_pointwise_lower_barrier_of_negative
    hκ hC r dr start hmono hcont hnegStart hnegSegment hderiv hriccati
      hsurgery
      (show -(((2 : ℝ) / 3) * C)⁻¹ ≤ r 0 (start 0) by
        convert hinitial using 1 <;> field_simp <;> ring)
  intro k t ht
  have h := hraw k t ht
  convert h using 1 <;> field_simp <;> ring

/-- Pointwise three-dimensional scalar-curvature barrier across surgery,
without assuming scalar curvature remains negative. -/
theorem three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier
    {C : ℝ} (hC : 0 < C)
    (r dr : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hcont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hderiv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hriccati : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      ((2 : ℝ) / 3) * (r k t) ^ 2 ≤ dr k t)
    (hsurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hinitial : -(3 / (2 * C)) ≤ r 0 (start 0)) :
    ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      -(3 / (2 * (C + (t - start 0)))) ≤ r k t := by
  have hκ : (0 : ℝ) < 2 / 3 := by norm_num
  have hraw := segmented_riccati_pointwise_lower_barrier
    hκ hC r dr start hmono hcont hderiv hriccati hsurgery
      (show -(((2 : ℝ) / 3) * C)⁻¹ ≤ r 0 (start 0) by
        convert hinitial using 1 <;> field_simp <;> ring)
  intro k t ht
  have h := hraw k t ht
  convert h using 1 <;> field_simp <;> ring

end Poincare
