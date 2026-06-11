/-
The maximum-principle stratum.

Hamilton's curvature estimates all reduce, through the parabolic maximum
principle, to scalar ODE comparison: a quantity satisfying `u' ≤ C u` with
`u(0) ≤ 0` stays nonpositive. This module proves that backbone lemma and
its positivity twin — the first bricks of the analytic stratum.
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

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

namespace RicciFlow

/--
**Riccati comparison (Hamilton's blow-up core)**: if `u' ≥ a u²` with
`u 0 > 0`, then `u t ≥ u 0 / (1 − a u 0 t)` — the scalar mechanism by
which positive scalar curvature forces a finite-time singularity of the
Ricci flow.
-/
theorem riccati_lower_bound {u u' : ℝ → ℝ} {a T : ℝ} (ha : 0 ≤ a)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (u' t) t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, a * u t ^ 2 ≤ u' t)
    (h0 : 0 < u 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u 0 / (1 - a * u 0 * t) ≤ u t := by
  -- Positivity persists: `u` is monotone since `u' ≥ a u² ≥ 0`.
  have hmono : MonotoneOn u (Icc (0 : ℝ) T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact fun s hs ↦ ((hd s hs).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact ((hd s (Ioo_subset_Icc_self hs)).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
      rw [(hd s hs').deriv]
      have := hineq s hs'
      nlinarith [sq_nonneg (u s)]
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := left_mem_Icc.mpr (ht.1.trans ht.2)
  have hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 < u s := fun s hs ↦
    lt_of_lt_of_le h0 (hmono h0mem hs hs.1)
  -- The reciprocal-plus-linear function is antitone.
  set w : ℝ → ℝ := fun s ↦ (u s)⁻¹ + a * s with hw
  have hwd : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt w (-(u' s) / u s ^ 2 + a) s := by
    intro s hs
    have h1 : HasDerivAt (fun s' ↦ (u s')⁻¹) (-(u' s) / u s ^ 2) s := by
      simpa using (hd s hs).inv (ne_of_gt (hpos s hs))
    simpa [hw] using h1.add ((hasDerivAt_id s).const_mul a)
  have hwmono : AntitoneOn w (Icc (0 : ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun s hs ↦ ((hwd s hs).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact ((hwd s (Ioo_subset_Icc_self hs)).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
      rw [(hwd s hs').deriv]
      have hu2 : 0 < u s ^ 2 := pow_pos (hpos s hs') 2
      have hq : a ≤ u' s / u s ^ 2 :=
        (le_div_iff₀ hu2).mpr (by linarith [hineq s hs'])
      rw [neg_div]
      linarith
  -- Conclude: `1/u t ≤ 1/u 0 − a t`, hence the bound.
  have hwt : w t ≤ w 0 := hwmono h0mem ht ht.1
  simp only [hw, mul_zero, add_zero] at hwt
  have hut : 0 < u t := hpos t ht
  have hinv : (u t)⁻¹ ≤ (u 0)⁻¹ - a * t := by linarith
  have hden : 0 < 1 - a * u 0 * t := by
    have h1 : 0 < (u t)⁻¹ := by positivity
    have h2 : 0 < (u 0)⁻¹ - a * t := lt_of_lt_of_le h1 hinv
    calc 0 < u 0 * ((u 0)⁻¹ - a * t) := by positivity
      _ = 1 - a * u 0 * t := by field_simp
  rw [div_le_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_left hinv
    (le_of_lt (mul_pos hut h0))
  have e1 : (u t * u 0) * (u t)⁻¹ = u 0 := by field_simp
  have e2 : (u t * u 0) * ((u 0)⁻¹ - a * t) =
      u t * (1 - a * u 0 * t) := by field_simp
  rw [e1, e2] at hmul
  exact hmul

end RicciFlow
