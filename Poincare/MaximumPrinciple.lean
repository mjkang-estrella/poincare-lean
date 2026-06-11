/-
The maximum-principle stratum.

Hamilton's curvature estimates all reduce, through the parabolic maximum
principle, to scalar ODE comparison: a quantity satisfying `u' ≤ C u` with
`u(0) ≤ 0` stays nonpositive. This module proves that backbone lemma and
its positivity twin — the first bricks of the analytic stratum.
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

open Set

namespace RicciFlow

/--
**ODE comparison (nonpositivity persists)**: if `u' ≤ C u` on `[0, T]` and
`u 0 ≤ 0`, then `u ≤ 0` on `[0, T]` — Hamilton's scalar maximum-principle
backbone, via the exponentially weighted antitone trick.
-/
theorem ode_comparison_nonpos {u u' : ℝ → ℝ} {C T : ℝ}
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (u' t) t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, u' t ≤ C * u t)
    (h0 : u 0 ≤ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : u t ≤ 0 := by
  set v : ℝ → ℝ := fun s ↦ Real.exp (-C * s) * u s with hv
  have hvd : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt v (Real.exp (-C * s) * -C * u s
        + Real.exp (-C * s) * u' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s' ↦ Real.exp (-C * s'))
        (Real.exp (-C * s) * -C) s := by
      simpa using ((hasDerivAt_id s).const_mul (-C)).exp
    simpa [hv] using h1.mul (hd s hs)
  have hmono : AntitoneOn v (Icc (0 : ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun s hs ↦ ((hvd s hs).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact ((hvd s (Ioo_subset_Icc_self hs)).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
      rw [(hvd s hs').deriv]
      have hexp : (0 : ℝ) < Real.exp (-C * s) := Real.exp_pos _
      have := hineq s hs'
      nlinarith
  have hv0 : v 0 ≤ 0 := by
    simp only [hv, neg_mul, mul_zero, neg_zero, Real.exp_zero, one_mul]
    exact h0
  have hvt : v t ≤ 0 := le_trans
    (hmono (left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1) hv0
  have hexp : (0 : ℝ) < Real.exp (-C * t) := Real.exp_pos _
  by_contra hpos
  push_neg at hpos
  nlinarith [hvt]

/--
**ODE comparison (nonnegativity persists)**: if `u' ≥ C u` on `[0, T]` and
`u 0 ≥ 0`, then `u ≥ 0` on `[0, T]` — the positivity-preservation twin,
the scalar shadow of "nonnegative curvature is preserved by the flow".
-/
theorem ode_comparison_nonneg {u u' : ℝ → ℝ} {C T : ℝ}
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (u' t) t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, C * u t ≤ u' t)
    (h0 : 0 ≤ u 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ u t := by
  have := ode_comparison_nonpos (u := fun s ↦ -u s) (u' := fun s ↦ -u' s)
    (C := C) (T := T)
    (fun s hs ↦ (hd s hs).neg)
    (fun s hs ↦ by
      have := hineq s hs
      simp only
      linarith)
    (by simpa using h0) ht
  simpa using this

end RicciFlow
