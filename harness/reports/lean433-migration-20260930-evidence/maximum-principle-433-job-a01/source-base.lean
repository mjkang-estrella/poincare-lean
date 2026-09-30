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

namespace RicciFlow

/--
**The second-derivative test (necessity)**: at a local minimum of a twice
differentiable function the second derivative is nonnegative — the 1-d
heart of "the Laplacian is nonnegative at a spatial minimum", which is the
pointwise mechanism of the parabolic maximum principle. Not in Mathlib.
-/
theorem secondDeriv_nonneg_of_isLocalMin {g g' g'' : ℝ → ℝ}
    (hd1 : ∀ t, HasDerivAt g (g' t) t)
    (hd2 : ∀ t, HasDerivAt g' (g'' t) t)
    (hcont : Continuous g'')
    (hmin : IsLocalMin g 0) : 0 ≤ g'' 0 := by
  by_contra hneg
  push_neg at hneg
  -- `g''` is negative on a ball around `0`.
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hcont.continuousAt.eventually_lt continuousAt_const hneg)
  -- `g' 0 = 0` at the local minimum.
  have hg'0 : g' 0 = 0 := by
    have := hmin.deriv_eq_zero
    rwa [(hd1 0).deriv] at this
  -- `g'` is strictly decreasing on `(-δ, δ)`, so `g' < 0` to the right.
  have hanti : StrictAntiOn g' (Set.Ioo (-δ) δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · exact fun s _ ↦ ((hd2 s).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      rw [(hd2 s).deriv]
      apply hball
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- Hence `g` is strictly decreasing on `[0, δ)`.
  have hganti : StrictAntiOn g (Set.Ico 0 δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
    · exact fun s _ ↦ ((hd1 s).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      rw [(hd1 s).deriv]
      have h0mem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by constructor <;> linarith
      have hsmem : s ∈ Set.Ioo (-δ) δ := ⟨by linarith [hs.1], hs.2⟩
      have := hanti h0mem hsmem hs.1
      rwa [hg'0] at this
  -- Contradiction with the local minimum.
  obtain ⟨ε, hε, hloc⟩ := Metric.eventually_nhds_iff.mp hmin
  set t := min (δ / 2) (ε / 2) with htdef
  have htpos : 0 < t := by positivity
  have ht1 : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hlt : g t < g 0 :=
    hganti (left_mem_Ico.mpr hδ) ⟨le_of_lt htpos, ht1⟩ htpos
  exact absurd (hloc ht2) (not_le.mpr hlt)

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
**The multivariate second-derivative test**: at a local minimum of a `C²`
function the Hessian is positive semidefinite — by restriction to lines
and the 1-d test. Not in Mathlib.
-/
theorem hessian_nonneg_of_isLocalMin {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {x₀ : E} (hmin : IsLocalMin f x₀) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x₀ v v := by
  set ℓ : ℝ → E := fun t ↦ x₀ + t • v with hℓ
  have hℓd : ∀ t : ℝ, HasDerivAt ℓ v t := by
    intro t
    simpa [hℓ] using ((hasDerivAt_id t).smul_const v).const_add x₀
  have hℓ0 : ℓ 0 = x₀ := by simp [hℓ]
  have hℓcont : Continuous ℓ := by
    continuity
  -- The restricted function and its two derivatives.
  set g : ℝ → ℝ := fun t ↦ f (ℓ t) with hg
  set g' : ℝ → ℝ := fun t ↦ fderiv ℝ f (ℓ t) v with hg'
  set g'' : ℝ → ℝ := fun t ↦ fderiv ℝ (fderiv ℝ f) (ℓ t) v v with hg''
  have hd1 : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    exact (((hf.differentiable (by norm_num)) (ℓ t)).hasFDerivAt).comp_hasDerivAt
      t (hℓd t)
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd2 : ∀ t, HasDerivAt g' (g'' t) t := by
    intro t
    have h1 : HasDerivAt (fun s ↦ fderiv ℝ f (ℓ s))
        (fderiv ℝ (fderiv ℝ f) (ℓ t) v) t :=
      ((hdf (ℓ t)).hasFDerivAt).comp_hasDerivAt t (hℓd t)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt
      t h1
    simpa [hg', ContinuousLinearMap.apply_apply] using h2
  have hcont : Continuous g'' := by
    have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
      ((hf.fderiv_right (m := 1) (by norm_num))).continuous_fderiv
        (by norm_num)
    exact ((h2.comp hℓcont).clm_apply continuous_const).clm_apply
      continuous_const
  have hgmin : IsLocalMin g 0 := by
    have hm : IsLocalMin f (ℓ 0) := by rwa [hℓ0]
    exact hm.comp_continuous hℓcont.continuousAt
  have := secondDeriv_nonneg_of_isLocalMin hd1 hd2 hcont hgmin
  simpa [hg'', hℓ0] using this

/--
Local multivariate second-derivative test.  This is the pointwise form needed
after passing a manifold statement to a single chart.
-/
theorem fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt {f : E → ℝ}
    {x₀ : E} (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x₀ v v := by
  set ℓ : ℝ → E := fun t ↦ x₀ + t • v with hℓ
  have hℓ0 : ℓ 0 = x₀ := by simp [hℓ]
  have hℓC2 : ContDiffAt ℝ 2 ℓ 0 := by
    simpa [hℓ] using (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hgC2 : ContDiffAt ℝ 2 (fun t : ℝ ↦ f (ℓ t)) 0 := by
    have hfℓ0 : ContDiffAt ℝ 2 f (ℓ 0) := by simpa [hℓ0] using hf
    exact hfℓ0.comp 0 hℓC2
  have hdfC1 : ContDiffAt ℝ 1 (fderiv ℝ f) x₀ :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hddfCont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x₀ :=
    hdfC1.continuousAt_fderiv (by norm_num)
  have hℓd : ∀ t : ℝ, HasDerivAt ℓ v t := by
    intro t
    simpa [hℓ] using ((hasDerivAt_id t).smul_const v).const_add x₀
  have hℓcontAt : ∀ t : ℝ, ContinuousAt ℓ t := fun t ↦ (hℓd t).continuousAt
  set g : ℝ → ℝ := fun t ↦ f (ℓ t) with hg
  set g' : ℝ → ℝ := fun t ↦ fderiv ℝ f (ℓ t) v with hg'
  set g'' : ℝ → ℝ := fun t ↦ fderiv ℝ (fderiv ℝ f) (ℓ t) v v with hg''
  have hg''cont : ContinuousAt g'' 0 := by
    have hℓcont : ContinuousAt ℓ 0 := hℓC2.continuousAt
    have hddfCont0 : ContinuousAt (fderiv ℝ (fderiv ℝ f)) (ℓ 0) := by
      simpa [hℓ0] using hddfCont
    simpa [g''] using
      ((hddfCont0.comp' hℓcont).clm_apply continuousAt_const).clm_apply continuousAt_const
  by_contra hneg
  push_neg at hneg
  have hneg' : g'' 0 < 0 := by
    simpa [g'', hℓ0] using hneg
  obtain ⟨δneg, hδneg, hballneg⟩ := Metric.eventually_nhds_iff.mp
    (hg''cont.eventually_lt continuousAt_const hneg')
  obtain ⟨U, hUmem, hUC2⟩ := hgC2.contDiffOn (m := 2) le_rfl (by intro h; cases h)
  obtain ⟨δU, hδU, hδUsub⟩ := Metric.mem_nhds_iff.mp hUmem
  obtain ⟨Sf, hSfmem, hSfC2⟩ := hf.contDiffOn (m := 2) le_rfl (by intro h; cases h)
  obtain ⟨ρf, hρf, hρfsub⟩ := Metric.mem_nhds_iff.mp hSfmem
  obtain ⟨Sdf, hSdfmem, hSdfC1⟩ :=
    hdfC1.contDiffOn (m := 1) le_rfl (by intro h; cases h)
  obtain ⟨ρdf, hρdf, hρdfsub⟩ := Metric.mem_nhds_iff.mp hSdfmem
  set scale : ℝ := ‖v‖ + 1 with hscale_def
  have hscale : 0 < scale := by positivity
  set δ := min δneg (min δU (min (ρf / scale) (ρdf / scale))) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ_le_neg : δ ≤ δneg := by simp [δ]
  have hδ_le_U : δ ≤ δU := by simp [δ]
  have hδ_le_f : δ ≤ ρf / scale := by simp [δ]
  have hδ_le_df : δ ≤ ρdf / scale := by simp [δ]
  have hline_mem_ball {ρ : ℝ} (hρ : 0 < ρ) {t : ℝ}
      (hδρ : δ ≤ ρ / scale) (ht : |t| < δ) :
      ℓ t ∈ Metric.ball x₀ ρ := by
    rw [Metric.mem_ball, hℓ, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs]
    have hnorm : 0 ≤ ‖v‖ := norm_nonneg v
    have hfrac : ‖v‖ / scale < 1 := by
      rw [div_lt_one hscale]
      simp [scale]
    calc
      |t| * ‖v‖ ≤ δ * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt ht) hnorm
      _ ≤ (ρ / scale) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hδρ hnorm
      _ = ρ * (‖v‖ / scale) := by ring
      _ < ρ * 1 := mul_lt_mul_of_pos_left hfrac hρ
      _ = ρ := by ring
  have hf_at : ∀ t : ℝ, |t| < δ → ContDiffAt ℝ 2 f (ℓ t) := by
    intro t ht
    exact (hSfC2.mono fun y hy ↦ hρfsub hy).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hline_mem_ball hρf hδ_le_f ht))
  have hdf_at : ∀ t : ℝ, |t| < δ → ContDiffAt ℝ 1 (fderiv ℝ f) (ℓ t) := by
    intro t ht
    exact (hSdfC1.mono fun y hy ↦ hρdfsub hy).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hline_mem_ball hρdf hδ_le_df ht))
  have hg_at : ∀ t ∈ Metric.ball (0 : ℝ) δ, ContDiffAt ℝ 2 g t := by
    intro t ht
    exact (hUC2.mono fun y hy ↦ hδUsub (Metric.ball_subset_ball hδ_le_U hy)).contDiffAt
      (Metric.isOpen_ball.mem_nhds ht)
  have hg'0 : g' 0 = 0 := by
    have hmin_line : IsLocalMin g 0 := by
      have hm : IsLocalMin f (ℓ 0) := by simpa [hℓ0] using hmin
      simpa [g] using hm.comp_continuous hℓC2.continuousAt
    have hdg0 : HasDerivAt g (g' 0) 0 := by
      have hfdiff0 : DifferentiableAt ℝ f (ℓ 0) := by
        simpa [hℓ0] using hf.differentiableAt (by norm_num)
      exact hfdiff0.hasFDerivAt.comp_hasDerivAt 0 (hℓd 0)
    exact hmin_line.hasDerivAt_eq_zero hdg0
  have hanti : StrictAntiOn g' (Set.Ioo (-δ) δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro t ht
      have htabs : |t| < δ := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      have hcont :
          ContinuousAt (fun s : ℝ ↦ fderiv ℝ f (ℓ s) v) t :=
        ((hdf_at t htabs).continuousAt.comp' (hℓcontAt t)).clm_apply continuousAt_const
      simpa [g'] using hcont.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      have htabs : |t| < δ := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      have hdg' : HasDerivAt g' (g'' t) t := by
        have h1 : HasDerivAt (fun s ↦ fderiv ℝ f (ℓ s))
            (fderiv ℝ (fderiv ℝ f) (ℓ t) v) t :=
          (((hdf_at t htabs).differentiableAt
              (by norm_num)).hasFDerivAt).comp_hasDerivAt t (hℓd t)
        have h2 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt
          t h1
        simpa [g', g'', ContinuousLinearMap.apply_apply] using h2
      rw [hdg'.deriv]
      exact hballneg (by
        rw [Real.dist_eq, sub_zero]
        exact lt_of_lt_of_le (abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩) hδ_le_neg)
  have hganti : StrictAntiOn g (Set.Ico 0 δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
    · intro t ht
      have htabs : |t| < δ := abs_lt.mpr ⟨by linarith [hδ, ht.1], ht.2⟩
      have hcont : ContinuousAt (fun s : ℝ ↦ f (ℓ s)) t :=
        (hf_at t htabs).continuousAt.comp' (hℓcontAt t)
      simpa [g] using hcont.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have htabs : |t| < δ := abs_lt.mpr ⟨by linarith [hδ, ht.1], ht.2⟩
      have hdg : HasDerivAt g (g' t) t := by
        exact (((hf_at t htabs).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt
          t (hℓd t)
      rw [hdg.deriv]
      have h0mem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by constructor <;> linarith
      have hsmem : t ∈ Set.Ioo (-δ) δ := ⟨by linarith [hδ, ht.1], ht.2⟩
      have := hanti h0mem hsmem ht.1
      rwa [hg'0] at this
  obtain ⟨ε, hε, hloc⟩ := Metric.eventually_nhds_iff.mp hmin
  set t := min (δ / 2) (ε / (2 * ‖v‖ + 2)) with htdef
  have htpos : 0 < t := by positivity
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hℓdist : dist (ℓ t) x₀ < ε := by
    rw [hℓ, dist_eq_norm, add_sub_cancel_left]
    have hdenpos : 0 < 2 * ‖v‖ + 2 := by positivity
    have htε : t ≤ ε / (2 * ‖v‖ + 2) := min_le_right _ _
    calc
      ‖t • v‖ = ‖t‖ * ‖v‖ := norm_smul t v
      _ = t * ‖v‖ := by rw [Real.norm_of_nonneg (le_of_lt htpos)]
      _ ≤ (ε / (2 * ‖v‖ + 2)) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right htε (norm_nonneg v)
      _ < ε := by
        have hvle : ‖v‖ < 2 * ‖v‖ + 2 := by nlinarith [norm_nonneg v]
        have hfrac : ‖v‖ / (2 * ‖v‖ + 2) < 1 := by
          rw [div_lt_one hdenpos]
          exact hvle
        have hεnonneg : 0 ≤ ε := le_of_lt hε
        calc
          (ε / (2 * ‖v‖ + 2)) * ‖v‖ = ε * (‖v‖ / (2 * ‖v‖ + 2)) := by ring
          _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
          _ = ε := by ring
  have hlt : g t < g 0 :=
    hganti (left_mem_Ico.mpr hδ) ⟨le_of_lt htpos, htδ⟩ htpos
  have hle : f (ℓ 0) ≤ f (ℓ t) := by simpa [hℓ0] using hloc hℓdist
  exact absurd (by simpa [g, hℓ0] using hle) (not_le.mpr (by simpa [g, hℓ0] using hlt))

end RicciFlow

namespace RicciFlow

/--
**The first-crossing time**: a continuous function positive at `0` that
fails positivity somewhere in `[0, T]` has a first zero, with positivity
before it — the temporal backbone of every first-violation argument in
parabolic maximum principles.
-/
theorem exists_first_zero {g : ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn g (Icc 0 T))
    (h0 : 0 < g 0) (hbad : ∃ t ∈ Icc (0 : ℝ) T, g t ≤ 0) :
    ∃ t₀ ∈ Ioc (0 : ℝ) T, g t₀ = 0 ∧ ∀ s ∈ Ico (0 : ℝ) t₀, 0 < g s := by
  obtain ⟨t₁, ht₁, hgt₁⟩ := hbad
  have hT0 : (0 : ℝ) ≤ T := ht₁.1.trans ht₁.2
  set S : Set ℝ := {t ∈ Icc (0 : ℝ) T | g t ≤ 0} with hS
  have hSne : S.Nonempty := ⟨t₁, ht₁, hgt₁⟩
  have hSbdd : BddBelow S := ⟨0, fun s hs ↦ hs.1.1⟩
  set t₀ := sInf S with ht₀
  have ht₀mem : t₀ ∈ Icc (0 : ℝ) T := by
    constructor
    · exact le_csInf hSne fun s hs ↦ hs.1.1
    · exact (csInf_le hSbdd ⟨ht₁, hgt₁⟩).trans ht₁.2
  -- `S` is closed, so the infimum is attained: `g t₀ ≤ 0`.
  have hSclosed : IsClosed S := by
    have hSeq : S = Icc (0 : ℝ) T ∩ g ⁻¹' (Iic 0) := by
      ext s
      simp [hS, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_preimage]
    rw [hSeq]
    exact hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have ht₀S : t₀ ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hgt₀ : g t₀ ≤ 0 := ht₀S.2
  -- Positivity strictly before the first crossing.
  have hbefore : ∀ s ∈ Ico (0 : ℝ) t₀, 0 < g s := by
    intro s hs
    by_contra hns
    push_neg at hns
    have hsmem : s ∈ S := ⟨⟨hs.1, (hs.2.le.trans ht₀mem.2)⟩, hns⟩
    exact absurd (csInf_le hSbdd hsmem) (not_le.mpr hs.2)
  -- `t₀ > 0` since `g 0 > 0`.
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀mem.1 with h | h
    · exfalso
      rw [← h] at hgt₀
      linarith
    · exact h
  -- `g t₀ ≥ 0` by left-continuity through positive values, hence `= 0`.
  have hge : 0 ≤ g t₀ := by
    have hcont : ContinuousWithinAt g (Icc 0 T) t₀ := hg t₀ ht₀mem
    have hlim : Filter.Tendsto g (nhdsWithin t₀ (Ico 0 t₀))
        (nhds (g t₀)) := by
      apply hcont.tendsto.mono_left
      apply nhdsWithin_mono
      intro s hs
      exact ⟨hs.1, hs.2.le.trans ht₀mem.2⟩
    have hne : (nhdsWithin t₀ (Ico 0 t₀)).NeBot := by
      rw [nhdsWithin_Ico_eq_nhdsLT ht₀pos]
      infer_instance
    exact ge_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin
      fun s hs ↦ le_of_lt (hbefore s hs))
  exact ⟨t₀, ⟨ht₀pos, ht₀mem.2⟩, le_antisymm hgt₀ hge, hbefore⟩

end RicciFlow

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

namespace RicciFlow

/-- Theorem contract for `ode_comparison_nonpos`. -/
theorem ode_comparison_nonpos_eq :
    @RicciFlow.ode_comparison_nonpos = @RicciFlow.ode_comparison_nonpos :=
  rfl

/-- Theorem contract for `ode_comparison_nonneg`. -/
theorem ode_comparison_nonneg_eq :
    @RicciFlow.ode_comparison_nonneg = @RicciFlow.ode_comparison_nonneg :=
  rfl

/-- Theorem contract for `riccati_lower_bound`. -/
theorem riccati_lower_bound_eq :
    @RicciFlow.riccati_lower_bound = @RicciFlow.riccati_lower_bound :=
  rfl

/-- Theorem contract for `riccati_forces_finite_time`. -/
theorem riccati_forces_finite_time_eq :
    @RicciFlow.riccati_forces_finite_time = @RicciFlow.riccati_forces_finite_time :=
  rfl

/-- Theorem contract for `einstein_scalar_hasDerivAt_riccati`. -/
theorem einstein_scalar_hasDerivAt_riccati_eq :
    @RicciFlow.einstein_scalar_hasDerivAt_riccati = @RicciFlow.einstein_scalar_hasDerivAt_riccati :=
  rfl

/-- Theorem contract for `riccati_upper_bound`. -/
theorem riccati_upper_bound_eq :
    @RicciFlow.riccati_upper_bound = @RicciFlow.riccati_upper_bound :=
  rfl

/-- Theorem contract for `riccati_doubling_time`. -/
theorem riccati_doubling_time_eq :
    @RicciFlow.riccati_doubling_time = @RicciFlow.riccati_doubling_time :=
  rfl

/-- Theorem contract for `secondDeriv_nonneg_of_isLocalMin`. -/
theorem secondDeriv_nonneg_of_isLocalMin_eq :
    @RicciFlow.secondDeriv_nonneg_of_isLocalMin = @RicciFlow.secondDeriv_nonneg_of_isLocalMin :=
  rfl

/-- Theorem contract for `hessian_nonneg_of_isLocalMin`. -/
theorem hessian_nonneg_of_isLocalMin_eq :
    @RicciFlow.hessian_nonneg_of_isLocalMin = @RicciFlow.hessian_nonneg_of_isLocalMin :=
  rfl

/-- Theorem contract for `fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt`. -/
theorem fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt_eq :
    @RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt =
      @RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt :=
  rfl

/-- Theorem contract for `exists_first_zero`. -/
theorem exists_first_zero_eq :
    @RicciFlow.exists_first_zero = @RicciFlow.exists_first_zero :=
  rfl

end RicciFlow
