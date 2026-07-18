import Poincare.Global.FiniteExtinctionIntegratingFactor

/-!
# Extinction across a genuine surgery schedule

The scalar finite-extinction estimates in
`FiniteExtinctionIntegratingFactor` use a single function on all smooth
segments.  At an actual surgery time, however, the geometric quantity has a
left-hand value before surgery and a potentially smaller right-hand value
after surgery.  This file models that distinction by giving every smooth
segment its own function.

The final theorem rules out an infinite, nonnegative, piecewise-smooth width
evolution satisfying Perelman's three-quarter differential inequality when
the (locally finite) surgery times tend to infinity and the weighted width
does not increase at surgery.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Interval Topology

namespace Poincare

/-- Integrating-factor decay for segment-indexed quantities.  The value
`W k (finish k)` is the left-hand value at the end of the `k`th smooth
segment, whereas `W (k+1) (start (k+1))` is the right-hand value after the
next surgery. -/
theorem integratingFactor_segmented_surgery_partition_decay_bound
    (μ dμ : ℝ → ℝ) (W dW : ℕ → ℝ → ℝ)
    (start finish : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (horder : ∀ k < n, start k ≤ finish k)
    (hμcont : ∀ k < n, ContinuousOn μ (Set.Icc (start k) (finish k)))
    (hWcont : ∀ k < n,
      ContinuousOn (W k) (Set.Icc (start k) (finish k)))
    (hμ : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt μ (dμ t) (Set.Ioi t) t)
    (hW : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hdecay : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      dμ t * W k t + μ t * dW k t ≤ -c * μ t)
    (hsurgery : ∀ k < n,
      μ (start (k + 1)) * W (k + 1) (start (k + 1)) ≤
        μ (finish k) * W k (finish k)) :
    μ (start n) * W n (start n) - μ (start 0) * W 0 (start 0) ≤
      ∑ k ∈ Finset.range n,
        (∫ t : ℝ in start k..finish k, -c * μ t) := by
  apply sub_le_sum_range_of_step_decay
    (fun k => μ (start k) * W k (start k))
    (fun k => ∫ t : ℝ in start k..finish k, -c * μ t) n
  intro k hk
  have hflow := integratingFactor_decay_bound
    (horder k hk) μ (W k) dμ (dW k)
    (hμcont k hk) (hWcont k hk) (hμ k hk) (hW k hk) (hdecay k hk)
  have hjump := hsurgery k hk
  linarith

/-- Concrete segmented form of Perelman's width estimate.  The reciprocal
integrating factor is constructed internally, while the caller supplies
separate pre- and post-surgery width functions. -/
theorem three_quarter_width_segmented_surgery_partition_decay_bound
    {C c : ℝ} (hC : 0 < C)
    (W dW : ℕ → ℝ → ℝ) (start finish : ℕ → ℝ) (n : ℕ)
    (hstart : ∀ k ≤ n, 0 ≤ start k)
    (horder : ∀ k < n, start k ≤ finish k)
    (hWcont : ∀ k < n,
      ContinuousOn (W k) (Set.Icc (start k) (finish k)))
    (hWderiv : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWnonneg : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      0 ≤ W k t)
    (hlinear : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (finish k),
      dW k t ≤ -c + ((3 : ℝ) / 4) * (t + C)⁻¹ * W k t)
    (hsurgery : ∀ k < n,
      (start (k + 1) + C)⁻¹ * W (k + 1) (start (k + 1)) ≤
        (finish k + C)⁻¹ * W k (finish k)) :
    (start n + C)⁻¹ * W n (start n) -
        (start 0 + C)⁻¹ * W 0 (start 0) ≤
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
      dμ t * W k t + μ t * dW k t ≤ -c * μ t := by
    intro k hk t ht
    have ht0 : 0 ≤ t := (hstart k hk.le).trans ht.1.le
    simpa [μ, dμ] using
      (reciprocal_decay_of_three_quarter_linear_inequality
        (add_pos_of_nonneg_of_pos ht0 hC) (hWnonneg k hk t ht)
        (hlinear k hk t ht))
  simpa [μ] using
    integratingFactor_segmented_surgery_partition_decay_bound
      μ dμ W dW start finish c n horder hμcont hWcont hμderiv hWderiv
        hdecay (by simpa [μ] using hsurgery)

/-- The reciprocal forcing integrals telescope over adjacent nonnegative
schedule intervals. -/
theorem sum_integral_reciprocal_time_shift_schedule
    {C : ℝ} (hC : 0 < C) (start : ℕ → ℝ) (n : ℕ)
    (hstart : ∀ k ≤ n, 0 ≤ start k)
    (hmono : ∀ k < n, start k ≤ start (k + 1)) :
    ∑ k ∈ Finset.range n,
        (∫ t : ℝ in start k..start (k + 1), (t + C)⁻¹) =
      ∫ t : ℝ in start 0..start n, (t + C)⁻¹ := by
  apply intervalIntegral.sum_integral_adjacent_intervals
  intro k hk
  have hcont : ContinuousOn (fun t : ℝ => (t + C)⁻¹)
      (Set.Icc (start k) (start (k + 1))) := by
    apply (continuousOn_id.add continuousOn_const).inv₀
    intro t ht
    have ht0 : 0 ≤ t := (hstart k hk.le).trans ht.1
    exact ne_of_gt (add_pos_of_nonneg_of_pos ht0 hC)
  exact hcont.intervalIntegrable_of_Icc (hmono k hk)

/-- A finite initial portion of a genuine surgery schedule cannot retain a
nonnegative terminal width after the accumulated reciprocal forcing exceeds
the initial weighted width. -/
theorem not_terminal_nonnegative_of_three_quarter_segmented_surgery_schedule
    {C c : ℝ} (hC : 0 < C)
    (W dW : ℕ → ℝ → ℝ) (start : ℕ → ℝ) (n : ℕ)
    (hstart : ∀ k ≤ n, 0 ≤ start k)
    (hmono : ∀ k < n, start k ≤ start (k + 1))
    (hWcont : ∀ k < n,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))) )
    (hWderiv : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWnonneg : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      0 ≤ W k t)
    (hlinear : ∀ k < n, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c + ((3 : ℝ) / 4) * (t + C)⁻¹ * W k t)
    (hsurgery : ∀ k < n,
      (start (k + 1) + C)⁻¹ * W (k + 1) (start (k + 1)) ≤
        (start (k + 1) + C)⁻¹ * W k (start (k + 1)))
    (hforcing : (start 0 + C)⁻¹ * W 0 (start 0) <
      c * ∫ t : ℝ in start 0..start n, (t + C)⁻¹)
    (hterminal : 0 ≤ W n (start n)) : False := by
  have hbound := three_quarter_width_segmented_surgery_partition_decay_bound
    hC W dW start (fun k => start (k + 1)) n hstart hmono hWcont
    hWderiv hWnonneg hlinear hsurgery
  have hsum := sum_integral_reciprocal_time_shift_schedule
    hC start n hstart hmono
  have hsumNeg :
      (∑ k ∈ Finset.range n,
          (∫ t : ℝ in start k..start (k + 1), -c * (t + C)⁻¹)) =
        -c * ∫ t : ℝ in start 0..start n, (t + C)⁻¹ := by
    calc
      (∑ k ∈ Finset.range n,
          (∫ t : ℝ in start k..start (k + 1), -c * (t + C)⁻¹)) =
          ∑ k ∈ Finset.range n,
            (-c * ∫ t : ℝ in start k..start (k + 1), (t + C)⁻¹) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [intervalIntegral.integral_const_mul]
      _ = -c * ∑ k ∈ Finset.range n,
          (∫ t : ℝ in start k..start (k + 1), (t + C)⁻¹) := by
            rw [Finset.mul_sum]
      _ = -c * ∫ t : ℝ in start 0..start n, (t + C)⁻¹ := by rw [hsum]
  rw [hsumNeg] at hbound
  have hfactor : 0 ≤ (start n + C)⁻¹ :=
    (inv_pos.mpr (add_pos_of_nonneg_of_pos (hstart n le_rfl) hC)).le
  have hproduct : 0 ≤ (start n + C)⁻¹ * W n (start n) :=
    mul_nonneg hfactor hterminal
  linarith

/-- A global, nonnegative, piecewise-smooth width evolution with locally
finite surgery cannot obey Perelman's three-quarter differential inequality.
The schedule may contain infinitely many surgeries, but its times must escape
to infinity and its weighted width must not increase at each surgery. -/
theorem no_global_nonnegative_of_three_quarter_segmented_surgery_schedule
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (W dW : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hWcont : ∀ k,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWderiv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWnonneg : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      0 ≤ W k t)
    (hlinear : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c + ((3 : ℝ) / 4) * (t + C)⁻¹ * W k t)
    (hsurgery : ∀ k,
      (start (k + 1) + C)⁻¹ * W (k + 1) (start (k + 1)) ≤
        (start (k + 1) + C)⁻¹ * W k (start (k + 1))) : False := by
  have hstartNonneg : ∀ k, 0 ≤ start k := by
    intro k
    induction k with
    | zero => simp [hstart0]
    | succ k ih => exact ih.trans (hmono k)
  have hforceTop : Tendsto
      (fun n : ℕ => c * ∫ t : ℝ in (0 : ℝ)..start n, (t + C)⁻¹)
      atTop atTop :=
    ((tendsto_integral_reciprocal_time_shift_atTop C hC).comp hstartTop)
      |>.const_mul_atTop hc
  have heventually : ∀ᶠ n : ℕ in atTop,
      C⁻¹ * W 0 0 < c * ∫ t : ℝ in (0 : ℝ)..start n, (t + C)⁻¹ :=
    hforceTop.eventually_gt_atTop (C⁻¹ * W 0 0)
  rcases heventually.exists with ⟨n, hn⟩
  apply not_terminal_nonnegative_of_three_quarter_segmented_surgery_schedule
    hC W dW start n
  · intro k hk
    exact hstartNonneg k
  · intro k hk
    exact hmono k
  · intro k hk
    exact hWcont k
  · intro k hk t ht
    exact hWderiv k t ht
  · intro k hk t ht
    exact hWnonneg k t ⟨ht.1.le, ht.2.le⟩
  · intro k hk t ht
    exact hlinear k t ht
  · intro k hk
    exact hsurgery k
  · simpa [hstart0] using hn
  · exact hWnonneg n (start n) ⟨le_rfl, hmono n⟩

end Poincare
