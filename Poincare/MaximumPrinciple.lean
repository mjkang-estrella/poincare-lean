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

namespace RicciFlow

/--
**Finite-time singularity**: a quantity satisfying `u' ≥ a u²` (`a > 0`)
with `u 0 > 0` cannot persist to time `1/(a u 0)`: any interval of
validity `[0, T]` has `T < 1/(a u 0)`. This is Hamilton's theorem that
positive scalar curvature forces the Ricci flow to become singular in
finite time, at its scalar core.
-/
theorem riccati_forces_finite_time {u u' : ℝ → ℝ} {a T : ℝ}
    (ha : 0 < a) (hT0 : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (u' t) t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, a * u t ^ 2 ≤ u' t)
    (h0 : 0 < u 0) : T < 1 / (a * u 0) := by
  have hTmem : T ∈ Icc (0 : ℝ) T := right_mem_Icc.mpr hT0
  -- Reproduce the persistence and inverse-comparison arguments at `t = T`.
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
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := left_mem_Icc.mpr hT0
  have hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 < u s := fun s hs ↦
    lt_of_lt_of_le h0 (hmono h0mem hs hs.1)
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
  have hwt : w T ≤ w 0 := hwmono h0mem hTmem hT0
  simp only [hw, mul_zero, add_zero] at hwt
  have hut : 0 < u T := hpos T hTmem
  have hinvT : 0 < (u 0)⁻¹ - a * T := by
    have h1 : 0 < (u T)⁻¹ := by positivity
    linarith
  rw [lt_div_iff₀ (by positivity : 0 < a * u 0)]
  have := mul_lt_mul_of_pos_left hinvT (show (0:ℝ) < u 0 from h0)
  rw [mul_sub, mul_inv_cancel₀ (ne_of_gt h0), mul_zero] at this
  nlinarith

end RicciFlow

namespace RicciFlow

/--
**The Einstein scalar saturates the Riccati engine**: the verified
Einstein-flow scalar curvature `λn/(1 − 2λt)` satisfies the Riccati ODE
`u' = (2/n) u²` exactly — Hamilton's comparison is tight on the verified
solution, cross-validating the flow stratum against the maximum-principle
stratum.
-/
theorem einstein_scalar_hasDerivAt_riccati {lam n t : ℝ} (hn : n ≠ 0)
    (ht : 1 - 2 * lam * t ≠ 0) :
    HasDerivAt (fun s ↦ lam * n / (1 - 2 * lam * s))
      ((2 / n) * (lam * n / (1 - 2 * lam * t)) ^ 2) t := by
  have hf : HasDerivAt (fun s ↦ 1 - 2 * lam * s) (-(2 * lam)) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * lam)).const_sub 1
  have hinv : HasDerivAt (fun s ↦ (1 - 2 * lam * s)⁻¹)
      (2 * lam / (1 - 2 * lam * t) ^ 2) t := by
    have h2 := hf.inv ht
    convert h2 using 1
    rw [neg_neg]
  have := hinv.const_mul (lam * n)
  convert this using 1
  field_simp

end RicciFlow

namespace RicciFlow

/--
**Riccati upper bound**: a positive quantity with `u' ≤ a u²` obeys
`u t ≤ u 0 / (1 − a u 0 t)` while the denominator is positive — the
mechanism of curvature doubling-time estimates.
-/
theorem riccati_upper_bound {u u' : ℝ → ℝ} {a T : ℝ} (ha : 0 ≤ a)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (u' t) t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, u' t ≤ a * u t ^ 2)
    (hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < u t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hden : 0 < 1 - a * u 0 * t) :
    u t ≤ u 0 / (1 - a * u 0 * t) := by
  set w : ℝ → ℝ := fun s ↦ (u s)⁻¹ + a * s with hw
  have hwd : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt w (-(u' s) / u s ^ 2 + a) s := by
    intro s hs
    have h1 : HasDerivAt (fun s' ↦ (u s')⁻¹) (-(u' s) / u s ^ 2) s := by
      simpa using (hd s hs).inv (ne_of_gt (hpos s hs))
    simpa [hw] using h1.add ((hasDerivAt_id s).const_mul a)
  have hwmono : MonotoneOn w (Icc (0 : ℝ) T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact fun s hs ↦ ((hwd s hs).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact ((hwd s (Ioo_subset_Icc_self hs)).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
      rw [(hwd s hs').deriv]
      have hu2 : 0 < u s ^ 2 := pow_pos (hpos s hs') 2
      have hq : u' s / u s ^ 2 ≤ a :=
        (div_le_iff₀ hu2).mpr (by linarith [hineq s hs'])
      rw [neg_div]
      linarith
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := left_mem_Icc.mpr (ht.1.trans ht.2)
  have hwt : w 0 ≤ w t := hwmono h0mem ht ht.1
  simp only [hw, mul_zero, add_zero] at hwt
  have hut : 0 < u t := hpos t ht
  have h0 : 0 < u 0 := hpos 0 h0mem
  have hinv : (u 0)⁻¹ - a * t ≤ (u t)⁻¹ := by linarith
  have hdiff : 0 < (u 0)⁻¹ - a * t := by
    have : (u 0)⁻¹ - a * t = (1 - a * u 0 * t) / u 0 := by
      field_simp
    rw [this]
    positivity
  rw [le_div_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_left hinv
    (le_of_lt (mul_pos hut h0))
  have e1 : (u t * u 0) * (u t)⁻¹ = u 0 := by field_simp
  have e2 : (u t * u 0) * ((u 0)⁻¹ - a * t) =
      u t * (1 - a * u 0 * t) := by field_simp
  rw [e1, e2] at hmul
  exact hmul

/--
**The doubling-time estimate**: within time `1/(2 a u 0)`, a positive
Riccati-bounded quantity at most doubles — the form used in canonical
neighbourhood arguments.
-/
theorem riccati_doubling_time {u u' : ℝ → ℝ} {a T : ℝ} (ha : 0 < a)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (u' t) t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, u' t ≤ a * u t ^ 2)
    (hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < u t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hdt : t ≤ 1 / (2 * a * u 0)) :
    u t ≤ 2 * u 0 := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := left_mem_Icc.mpr (ht.1.trans ht.2)
  have h0 : 0 < u 0 := hpos 0 h0mem
  have hau : a * u 0 * t ≤ 1 / 2 := by
    have h2 : 0 < 2 * a * u 0 := by positivity
    calc a * u 0 * t ≤ a * u 0 * (1 / (2 * a * u 0)) := by
          apply mul_le_mul_of_nonneg_left hdt (by positivity)
      _ = 1 / 2 := by field_simp
  have hden : 0 < 1 - a * u 0 * t := by linarith
  have hbound := riccati_upper_bound (le_of_lt ha) hd hineq hpos ht hden
  calc u t ≤ u 0 / (1 - a * u 0 * t) := hbound
    _ ≤ u 0 / (1 / 2) := by
        apply div_le_div_of_nonneg_left (le_of_lt h0) (by linarith) ?_
        linarith
    _ = 2 * u 0 := by ring
end RicciFlow
