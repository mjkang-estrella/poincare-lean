import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Integrating-factor extinction inequalities

This file isolates the scalar analytic mechanism in finite-extinction
arguments.  If a nonnegative geometric quantity satisfies a differential
inequality after multiplication by a positive integrating factor, then it
cannot remain nonnegative beyond a time at which the accumulated negative
forcing exceeds its initial weighted value.

The statements use right derivatives, matching piecewise-smooth Ricci flows
between surgery times.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Interval Topology

namespace Poincare

/-- Algebraic cancellation behind the integrating-factor method for an
inequality `W' ≤ -c + a W` and factor equation `μ' = -a μ`. -/
theorem integratingFactor_decay_of_linear_inequality
    {c μ W dμ dW rate : ℝ}
    (hμ : 0 ≤ μ) (hfactor : dμ = -rate * μ)
    (hlinear : dW ≤ -c + rate * W) :
    dμ * W + μ * dW ≤ -c * μ := by
  rw [hfactor]
  calc
    (-rate * μ) * W + μ * dW ≤
        (-rate * μ) * W + μ * (-c + rate * W) := by
      gcongr
    _ = -c * μ := by ring

/-- A reciprocal time shift is a convenient stronger integrating factor for
Perelman's characteristic coefficient `3/(4(t+C))`.  Nonnegativity of `W`
absorbs the extra negative quarter. -/
theorem reciprocal_decay_of_three_quarter_linear_inequality
    {x c W dW : ℝ} (hx : 0 < x) (hW : 0 ≤ W)
    (hlinear : dW ≤ -c + ((3 : ℝ) / 4) * x⁻¹ * W) :
    (-(x⁻¹ * x⁻¹)) * W + x⁻¹ * dW ≤ -c * x⁻¹ := by
  have hxinv : 0 ≤ x⁻¹ := (inv_pos.mpr hx).le
  calc
    (-(x⁻¹ * x⁻¹)) * W + x⁻¹ * dW ≤
        (-(x⁻¹ * x⁻¹)) * W +
          x⁻¹ * (-c + ((3 : ℝ) / 4) * x⁻¹ * W) := by
      gcongr
    _ = -c * x⁻¹ - ((1 : ℝ) / 4) * (x⁻¹ * x⁻¹) * W := by ring
    _ ≤ -c * x⁻¹ := sub_le_self _ (mul_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg hxinv hxinv)) hW)

/-- Integral of the reciprocal shift on a nonnegative time interval. -/
theorem integral_reciprocal_time_shift
    {C b : ℝ} (hC : 0 < C) (hb : 0 ≤ b) :
    (∫ t : ℝ in (0 : ℝ)..b, (t + C)⁻¹) =
      Real.log (b + C) - Real.log C := by
  let primitive : ℝ → ℝ := fun t => Real.log (t + C)
  let integrand : ℝ → ℝ := fun t => (t + C)⁻¹
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) b,
      HasDerivAt primitive (integrand t) t := by
    intro t ht
    have hpos : 0 < t + C := add_pos_of_nonneg_of_pos ht.1 hC
    simpa [primitive, integrand, div_eq_mul_inv] using
      (((hasDerivAt_id t).add_const C).log (ne_of_gt hpos))
  have hprimitiveCont : ContinuousOn primitive (Set.Icc (0 : ℝ) b) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hintegrandCont : ContinuousOn integrand (Set.Icc (0 : ℝ) b) := by
    apply (continuousOn_id.add continuousOn_const).inv₀
    intro t ht
    exact ne_of_gt (add_pos_of_nonneg_of_pos ht.1 hC)
  have hint : IntervalIntegrable integrand volume 0 b := by
    have hcontU : ContinuousOn integrand (Set.uIcc (0 : ℝ) b) := by
      simpa [Set.uIcc_of_le hb] using hintegrandCont
    exact hcontU.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
    hprimitiveCont
    (fun t ht => (hderiv t ⟨ht.1.le, ht.2.le⟩)) hint
  simpa [primitive, integrand] using hFTC

/-- Derivative of the reciprocal time shift, in the product form consumed by
the integrating-factor estimates. -/
theorem hasDerivAt_reciprocal_time_shift
    (C t : ℝ) (hne : t + C ≠ 0) :
    HasDerivAt (fun s : ℝ => (s + C)⁻¹)
      (-((t + C)⁻¹ * (t + C)⁻¹)) t := by
  have hbase : HasDerivAt (fun s : ℝ => s + C) 1 t := by
    simpa using (hasDerivAt_id t).add_const C
  have hinv := hbase.inv hne
  have hderivEq :
      -1 / (t + C) ^ 2 = -((t + C)⁻¹ * (t + C)⁻¹) := by
    field_simp
  rwa [hderivEq] at hinv

/-- The accumulated reciprocal time shift diverges. -/
theorem tendsto_integral_reciprocal_time_shift_atTop
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun b : ℝ => ∫ t : ℝ in (0 : ℝ)..b, (t + C)⁻¹)
      atTop atTop := by
  have hshift : Tendsto (fun b : ℝ => b + C) atTop atTop :=
    tendsto_atTop_add_const_right atTop C tendsto_id
  have hlog : Tendsto (fun b : ℝ => Real.log (b + C)) atTop atTop :=
    Real.tendsto_log_atTop.comp hshift
  have hrhs : Tendsto
      (fun b : ℝ => Real.log (b + C) - Real.log C) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-Real.log C) hlog
  apply hrhs.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  exact (integral_reciprocal_time_shift hC hb).symm

/-- Positive multiples of the accumulated reciprocal factor eventually exceed
any prescribed initial weighted value. -/
theorem exists_reciprocal_time_shift_forcing_exceeds
    {C c A : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∃ b, 0 ≤ b ∧ A < c * ∫ t : ℝ in (0 : ℝ)..b, (t + C)⁻¹ := by
  have hforce : Tendsto
      (fun b : ℝ => c * ∫ t : ℝ in (0 : ℝ)..b, (t + C)⁻¹)
      atTop atTop :=
    (tendsto_integral_reciprocal_time_shift_atTop C hC).const_mul_atTop hc
  rcases ((hforce.eventually_gt_atTop A).and
    (eventually_ge_atTop (0 : ℝ))).exists with ⟨b, hAb, hb⟩
  exact ⟨b, hb, hAb⟩

/-- Perelman-type scalar extinction mechanism.  No globally defined,
nonnegative `W` can satisfy

`W' ≤ -c + (3/4)(t+C)⁻¹ W`

for positive `c,C`.  The reciprocal factor `(t+C)⁻¹` is slightly stronger
than the exact fractional-power factor and its logarithmically divergent
integral forces finite-time failure of nonnegativity. -/
theorem no_global_nonnegative_of_three_quarter_width_inequality
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (W dW : ℝ → ℝ)
    (hWcont : Continuous W)
    (hWderiv : ∀ t, 0 < t →
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hWnonneg : ∀ t, 0 ≤ t → 0 ≤ W t)
    (hlinear : ∀ t, 0 < t →
      dW t ≤ -c + ((3 : ℝ) / 4) * (t + C)⁻¹ * W t) :
    False := by
  rcases exists_reciprocal_time_shift_forcing_exceeds
      (A := C⁻¹ * W 0) hC hc with ⟨b, hb, hforce⟩
  let μ : ℝ → ℝ := fun t => (t + C)⁻¹
  let dμ : ℝ → ℝ := fun t => -((t + C)⁻¹ * (t + C)⁻¹)
  have hμcont : ContinuousOn μ (Set.Icc (0 : ℝ) b) := by
    apply (continuousOn_id.add continuousOn_const).inv₀
    intro t ht
    exact ne_of_gt (add_pos_of_nonneg_of_pos ht.1 hC)
  have hμderiv : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t := by
    intro t ht
    have hpos : 0 < t + C := add_pos ht.1 hC
    simpa [μ, dμ] using
      (hasDerivAt_reciprocal_time_shift C t (ne_of_gt hpos)).hasDerivWithinAt
  have hdecay : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      dμ t * W t + μ t * dW t ≤ -c * μ t := by
    intro t ht
    simpa [μ, dμ] using
      (reciprocal_decay_of_three_quarter_linear_inequality
        (add_pos ht.1 hC) (hWnonneg t ht.1.le) (hlinear t ht.1))
  have hforce' : μ 0 * W 0 < c * ∫ t : ℝ in (0 : ℝ)..b, μ t := by
    simpa [μ] using hforce
  have hμb : 0 ≤ μ b := by
    exact (inv_pos.mpr (add_pos_of_nonneg_of_pos hb hC)).le
  have hproduct : ContinuousOn (fun t => μ t * W t) (Set.Icc (0 : ℝ) b) :=
    hμcont.mul hWcont.continuousOn
  have hproductDeriv : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      HasDerivWithinAt (fun s => μ s * W s)
        (dμ t * W t + μ t * dW t) (Set.Ioi t) t := by
    intro t ht
    exact (hμderiv t ht).mul (hWderiv t ht.1)
  have hint : IntegrableOn (fun t : ℝ => -c * μ t) (Set.Icc (0 : ℝ) b) :=
    ((hμcont.const_mul (-c)).integrableOn_Icc)
  have hbound := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hb hproduct hproductDeriv hint hdecay
  have hintegral :
      (∫ t : ℝ in (0 : ℝ)..b, -c * μ t) =
        -(c * ∫ t : ℝ in (0 : ℝ)..b, μ t) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [hintegral] at hbound
  have hterminal : 0 ≤ μ b * W b :=
    mul_nonneg hμb (hWnonneg b hb)
  linarith

/-- Product-rule form of the integrating-factor differential inequality,
integrated using the right-derivative fundamental theorem of calculus. -/
theorem integratingFactor_decay_bound
    {a b c : ℝ} (hab : a ≤ b)
    (μ W dμ dW : ℝ → ℝ)
    (hμcont : ContinuousOn μ (Set.Icc a b))
    (hWcont : ContinuousOn W (Set.Icc a b))
    (hμ : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ t ∈ Set.Ioo a b,
      dμ t * W t + μ t * dW t ≤ -c * μ t) :
    μ b * W b - μ a * W a ≤ ∫ t : ℝ in a..b, -c * μ t := by
  have hproduct : ContinuousOn (fun t => μ t * W t) (Set.Icc a b) :=
    hμcont.mul hWcont
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt (fun s => μ s * W s)
        (dμ t * W t + μ t * dW t) (Set.Ioi t) t := by
    intro t ht
    exact (hμ t ht).mul (hW t ht)
  have hint : IntegrableOn (fun t : ℝ => -c * μ t) (Set.Icc a b) :=
    ((hμcont.const_mul (-c)).integrableOn_Icc)
  exact intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hab hproduct hderiv hint hdecay

/-- Integrated linear differential inequality after deriving the product
decay algebraically from `W' ≤ -c + rate·W` and `μ' = -rate·μ`. -/
theorem integratingFactor_linear_inequality_bound
    {a b c : ℝ} (hab : a ≤ b)
    (μ W dμ dW rate : ℝ → ℝ)
    (hμcont : ContinuousOn μ (Set.Icc a b))
    (hWcont : ContinuousOn W (Set.Icc a b))
    (hμnonneg : ∀ t ∈ Set.Ioo a b, 0 ≤ μ t)
    (hfactor : ∀ t ∈ Set.Ioo a b, dμ t = -rate t * μ t)
    (hlinear : ∀ t ∈ Set.Ioo a b,
      dW t ≤ -c + rate t * W t)
    (hμ : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt W (dW t) (Set.Ioi t) t) :
    μ b * W b - μ a * W a ≤ ∫ t : ℝ in a..b, -c * μ t := by
  apply integratingFactor_decay_bound hab μ W dμ dW
    hμcont hWcont hμ hW
  intro t ht
  exact integratingFactor_decay_of_linear_inequality
    (hμnonneg t ht) (hfactor t ht) (hlinear t ht)

/-- A weighted quantity cannot stay nonnegative at the terminal time once the
integrated forcing exceeds its initial weighted value. -/
theorem not_terminal_nonnegative_of_integratingFactor_decay
    {a b c : ℝ} (hab : a ≤ b)
    (μ W dμ dW : ℝ → ℝ)
    (hμcont : ContinuousOn μ (Set.Icc a b))
    (hWcont : ContinuousOn W (Set.Icc a b))
    (hμ : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ t ∈ Set.Ioo a b,
      dμ t * W t + μ t * dW t ≤ -c * μ t)
    (hforcing : μ a * W a < c * ∫ t : ℝ in a..b, μ t) :
    ¬(0 ≤ μ b ∧ 0 ≤ W b) := by
  intro hterminal
  have hbound := integratingFactor_decay_bound hab μ W dμ dW
    hμcont hWcont hμ hW hdecay
  have hintegral :
      (∫ t : ℝ in a..b, -c * μ t) =
        -(c * ∫ t : ℝ in a..b, μ t) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [hintegral] at hbound
  have hterminalProduct : 0 ≤ μ b * W b :=
    mul_nonneg hterminal.1 hterminal.2
  have hcontra : c * (∫ t : ℝ in a..b, μ t) ≤ μ a * W a := by
    linarith
  exact (not_le_of_gt hforcing) hcontra

/-- If the integrating factor itself is nonnegative, terminal nonnegativity of
the geometric quantity alone contradicts the accumulated forcing criterion. -/
theorem not_terminal_quantity_nonnegative_of_integratingFactor_decay
    {a b c : ℝ} (hab : a ≤ b)
    (μ W dμ dW : ℝ → ℝ)
    (hμcont : ContinuousOn μ (Set.Icc a b))
    (hWcont : ContinuousOn W (Set.Icc a b))
    (hμ : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ t ∈ Set.Ioo a b,
      dμ t * W t + μ t * dW t ≤ -c * μ t)
    (hforcing : μ a * W a < c * ∫ t : ℝ in a..b, μ t)
    (hμb : 0 ≤ μ b) :
    ¬ 0 ≤ W b := by
  intro hWb
  exact not_terminal_nonnegative_of_integratingFactor_decay hab μ W dμ dW
    hμcont hWcont hμ hW hdecay hforcing ⟨hμb, hWb⟩

/-- Global finite-extinction criterion: if the accumulated integrating-factor
forcing eventually exceeds the initial weighted quantity, the evolving
quantity is negative at some finite time. -/
theorem exists_terminal_negative_of_integratingFactor_forcing
    {a c : ℝ} (μ W dμ dW : ℝ → ℝ)
    (hμcont : Continuous μ) (hWcont : Continuous W)
    (hμ : ∀ t, a < t →
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ t, a < t →
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ t, a < t →
      dμ t * W t + μ t * dW t ≤ -c * μ t)
    (hμnonneg : ∀ t, a ≤ t → 0 ≤ μ t)
    (hforcing : ∃ b, a ≤ b ∧
      μ a * W a < c * ∫ t : ℝ in a..b, μ t) :
    ∃ b, a ≤ b ∧ W b < 0 := by
  rcases hforcing with ⟨b, hab, hforce⟩
  refine ⟨b, hab, lt_of_not_ge ?_⟩
  apply not_terminal_quantity_nonnegative_of_integratingFactor_decay
    hab μ W dμ dW hμcont.continuousOn hWcont.continuousOn
  · intro t ht
    exact hμ t ht.1
  · intro t ht
    exact hW t ht.1
  · intro t ht
    exact hdecay t ht.1
  · exact hforce
  · exact hμnonneg b hab

/-- Uniform negative right derivative gives the elementary finite-time bound
`c (b-a) ≤ W(a)` as long as the terminal quantity is nonnegative. -/
theorem uniform_decay_time_mul_le_initial
    {a b c : ℝ} (hab : a ≤ b)
    (W dW : ℝ → ℝ)
    (hWcont : ContinuousOn W (Set.Icc a b))
    (hW : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ t ∈ Set.Ioo a b, dW t ≤ -c)
    (hWb : 0 ≤ W b) :
    c * (b - a) ≤ W a := by
  have hconstInt : IntegrableOn (fun _ : ℝ => -c) (Set.Icc a b) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => -c) (Set.Icc a b)).integrableOn_Icc
  have hbound : W b - W a ≤ ∫ _t : ℝ in a..b, -c :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      hab hWcont hW hconstInt hdecay
  have hintegral : (∫ _t : ℝ in a..b, -c) = -c * (b - a) := by
    simp
    ring
  rw [hintegral] at hbound
  linarith

/-- Dividing the uniform-decay estimate by a positive decay rate gives the
usual upper bound for the length of any nonnegative interval. -/
theorem uniform_decay_interval_length_le
    {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (W dW : ℝ → ℝ)
    (hWcont : ContinuousOn W (Set.Icc a b))
    (hW : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ t ∈ Set.Ioo a b, dW t ≤ -c)
    (hWb : 0 ≤ W b) :
    b - a ≤ W a / c := by
  rw [le_div_iff₀ hc]
  simpa [mul_comm] using
    uniform_decay_time_mul_le_initial hab W dW hWcont hW hdecay hWb

/-- Telescoping a finite sequence of one-step decay inequalities. -/
theorem sub_le_sum_range_of_step_decay
    (Y forcing : ℕ → ℝ) :
    ∀ n : ℕ, (∀ k < n, Y (k + 1) - Y k ≤ forcing k) →
      Y n - Y 0 ≤ ∑ k ∈ Finset.range n, forcing k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hstep
      have hlast : Y (n + 1) - Y n ≤ forcing n :=
        hstep n (Nat.lt_succ_self n)
      have hprev : Y n - Y 0 ≤ ∑ k ∈ Finset.range n, forcing k :=
        ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self n)))
      rw [Finset.sum_range_succ]
      linarith

/-- Piecewise decay survives nonincreasing surgery jumps.  The value evolves
from `start k` to `finish k` along a smooth flow segment, then may jump down to
`start (k+1)` at surgery. -/
theorem surgery_partition_decay_bound
    (Y : ℝ → ℝ) (start finish forcing : ℕ → ℝ)
    (n : ℕ)
    (hflow : ∀ k < n,
      Y (finish k) - Y (start k) ≤ forcing k)
    (hsurgery : ∀ k < n,
      Y (start (k + 1)) ≤ Y (finish k)) :
    Y (start n) - Y (start 0) ≤
      ∑ k ∈ Finset.range n, forcing k := by
  apply sub_le_sum_range_of_step_decay (fun k => Y (start k)) forcing n
  intro k hk
  have hf := hflow k hk
  have hs := hsurgery k hk
  linarith

/-- If the accumulated flow decay across a finite surgery partition exceeds
the initial value, a nonnegative quantity cannot remain nonnegative at the
terminal post-surgery time. -/
theorem not_terminal_nonnegative_of_surgery_partition_decay
    (Y : ℝ → ℝ) (start finish forcing : ℕ → ℝ)
    (n : ℕ)
    (hflow : ∀ k < n,
      Y (finish k) - Y (start k) ≤ forcing k)
    (hsurgery : ∀ k < n,
      Y (start (k + 1)) ≤ Y (finish k))
    (hforcing : Y (start 0) +
      (∑ k ∈ Finset.range n, forcing k) < 0) :
    ¬ 0 ≤ Y (start n) := by
  intro hterminal
  have hbound := surgery_partition_decay_bound
    Y start finish forcing n hflow hsurgery
  linarith

/-- Full finite-partition integrating-factor estimate across surgery times.
Each smooth segment supplies the product differential inequality, while each
surgery jump is only required not to increase the weighted quantity. -/
theorem integratingFactor_surgery_partition_decay_bound
    (μ W dμ dW : ℝ → ℝ) (start finish : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (horder : ∀ k < n, start k ≤ finish k)
    (hμcont : ∀ k < n, ContinuousOn μ (Set.Icc (start k) (finish k)))
    (hWcont : ∀ k < n, ContinuousOn W (Set.Icc (start k) (finish k)))
    (hμ : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      dμ t * W t + μ t * dW t ≤ -c * μ t)
    (hsurgery : ∀ k < n,
      μ (start (k + 1)) * W (start (k + 1)) ≤
        μ (finish k) * W (finish k)) :
    μ (start n) * W (start n) - μ (start 0) * W (start 0) ≤
      ∑ k ∈ Finset.range n,
        (∫ t : ℝ in start k..finish k, -c * μ t) := by
  apply surgery_partition_decay_bound
    (fun t => μ t * W t) start finish
    (fun k => ∫ t : ℝ in start k..finish k, -c * μ t) n
  · intro k hk
    exact integratingFactor_decay_bound (horder k hk) μ W dμ dW
      (hμcont k hk) (hWcont k hk) (hμ k hk) (hW k hk)
      (hdecay k hk)
  · exact hsurgery

/-- Extinction conclusion for the finite surgery partition: once the summed
weighted forcing drives the upper bound below zero, a nonnegative integrating
factor rules out a nonnegative terminal geometric quantity. -/
theorem not_terminal_quantity_nonnegative_of_integratingFactor_surgery_partition
    (μ W dμ dW : ℝ → ℝ) (start finish : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (horder : ∀ k < n, start k ≤ finish k)
    (hμcont : ∀ k < n, ContinuousOn μ (Set.Icc (start k) (finish k)))
    (hWcont : ∀ k < n, ContinuousOn W (Set.Icc (start k) (finish k)))
    (hμ : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hdecay : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      dμ t * W t + μ t * dW t ≤ -c * μ t)
    (hsurgery : ∀ k < n,
      μ (start (k + 1)) * W (start (k + 1)) ≤
        μ (finish k) * W (finish k))
    (hforcing : μ (start 0) * W (start 0) +
      (∑ k ∈ Finset.range n,
        (∫ t : ℝ in start k..finish k, -c * μ t)) < 0)
    (hμterminal : 0 ≤ μ (start n)) :
    ¬ 0 ≤ W (start n) := by
  intro hWterminal
  have hbound := integratingFactor_surgery_partition_decay_bound
    μ W dμ dW start finish c n horder hμcont hWcont hμ hW hdecay hsurgery
  have hproduct : 0 ≤ μ (start n) * W (start n) :=
    mul_nonneg hμterminal hWterminal
  linarith

/-- Finite-surgery version of the concrete three-quarter width inequality.
The reciprocal factor is constructed internally, so callers supply only the
width evolution, nonnegativity, and weighted surgery-drop laws. -/
theorem three_quarter_width_surgery_partition_decay_bound
    {C c : ℝ} (hC : 0 < C)
    (W dW : ℝ → ℝ) (start finish : ℕ → ℝ) (n : ℕ)
    (hstart : ∀ k ≤ n, 0 ≤ start k)
    (horder : ∀ k < n, start k ≤ finish k)
    (hWcont : ∀ k < n,
      ContinuousOn W (Set.Icc (start k) (finish k)))
    (hWderiv : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt W (dW t) (Set.Ioi t) t)
    (hWnonneg : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k), 0 ≤ W t)
    (hlinear : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      dW t ≤ -c + ((3 : ℝ) / 4) * (t + C)⁻¹ * W t)
    (hsurgery : ∀ k < n,
      (start (k + 1) + C)⁻¹ * W (start (k + 1)) ≤
        (finish k + C)⁻¹ * W (finish k)) :
    (start n + C)⁻¹ * W (start n) -
        (start 0 + C)⁻¹ * W (start 0) ≤
      ∑ k ∈ Finset.range n,
        (∫ t : ℝ in start k..finish k, -c * (t + C)⁻¹) := by
  let μ : ℝ → ℝ := fun t => (t + C)⁻¹
  let dμ : ℝ → ℝ := fun t => -((t + C)⁻¹ * (t + C)⁻¹)
  have hμcont : ∀ k < n,
      ContinuousOn μ (Set.Icc (start k) (finish k)) := by
    intro k hk
    apply (continuousOn_id.add continuousOn_const).inv₀
    intro t ht
    have ht0 : 0 ≤ t := (hstart k hk.le).trans ht.1
    exact ne_of_gt (add_pos_of_nonneg_of_pos ht0 hC)
  have hμderiv : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t := by
    intro k hk t ht
    have ht0 : 0 ≤ t := (hstart k hk.le).trans ht.1.le
    have hpos : 0 < t + C := add_pos_of_nonneg_of_pos ht0 hC
    simpa [μ, dμ] using
      (hasDerivAt_reciprocal_time_shift C t (ne_of_gt hpos)).hasDerivWithinAt
  have hdecay : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      dμ t * W t + μ t * dW t ≤ -c * μ t := by
    intro k hk t ht
    have ht0 : 0 ≤ t := (hstart k hk.le).trans ht.1.le
    simpa [μ, dμ] using
      (reciprocal_decay_of_three_quarter_linear_inequality
        (add_pos_of_nonneg_of_pos ht0 hC) (hWnonneg k hk t ht)
        (hlinear k hk t ht))
  simpa [μ] using
    integratingFactor_surgery_partition_decay_bound
      μ W dμ dW start finish c n horder hμcont hWcont hμderiv hWderiv
        hdecay (by simpa [μ] using hsurgery)

end Poincare
