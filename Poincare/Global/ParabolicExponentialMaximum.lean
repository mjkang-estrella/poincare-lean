import Poincare.Global.ParabolicMinimumContinuousOn

/-!
# Exponential parabolic maximum comparison

This file turns a pointwise coercive parabolic differential inequality into
an exponential pointwise bound on a compact spatial manifold.  It avoids any
differentiability assumption for the spatial supremum: the proof applies the
existing slab-local parabolic minimum principle to

`C * exp (-rate * t) - Q t x`.

The abstract Laplacian assumptions state only the two identities used by that
comparison: spatial constants disappear, and the Laplacian is nonpositive at
a spatial maximum of `Q`.
-/

noncomputable section

open Set
open scoped Topology

namespace Poincare

universe u

variable {M : Type u} [TopologicalSpace M]

/-- A pointwise inequality `∂ₜ Q ≤ ΔQ - rate * Q` gives the sharp exponential
maximum bound on every finite time slab.

Unlike a scalar-supremum ODE argument, this theorem assumes derivatives only
for the original pointwise track `Q t x`; no derivative of `sup_x Q t x` is
present. -/
theorem closed_parabolic_maximum_exp_decay_continuousOn
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {Q Q' : ℝ → M → ℝ} {T rate C : ℝ}
    (hT0 : 0 ≤ T)
    (hQ_cont : ContinuousOn (Function.uncurry Q)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hQd : ∀ x : M, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ Q s x) (Q' t x) t)
    (hlap_const_sub : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : ℝ, ∀ x : M,
      lap t (fun y : M ↦ a - Q t y) x = -lap t (Q t) x)
    (hQevol : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      Q' t x ≤ lap t (Q t) x - rate * Q t x)
    (hmax_lap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      IsMaxOn (Q t) Set.univ x → lap t (Q t) x ≤ 0)
    (hQ0 : ∀ x : M, Q 0 x ≤ C) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      Q t x ≤ C * Real.exp ((-rate) * t) := by
  let u : ℝ → M → ℝ := fun t x ↦
    C * Real.exp ((-rate) * t) - Q t x
  let u' : ℝ → M → ℝ := fun t x ↦
    (-rate) * C * Real.exp ((-rate) * t) - Q' t x
  have hu_cont : ContinuousOn (Function.uncurry u)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
    apply ContinuousOn.sub
    · exact
        (continuous_const.mul
          ((continuous_const.mul continuous_fst).rexp)).continuousOn
    · exact hQ_cont
  have hud : ∀ x : M, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t := by
    intro x t ht
    have hexp : HasDerivAt
        (fun s : ℝ ↦ C * Real.exp ((-rate) * s))
        ((-rate) * C * Real.exp ((-rate) * t)) t := by
      have h := (((hasDerivAt_id t).const_mul (-rate)).exp).const_mul C
      convert h using 1 <;> simp [id_eq] <;> ring
    simpa [u, u'] using hexp.sub (hQd x t ht)
  have hlap_add_const : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      lap t (fun y : M ↦ u t y + k) x = lap t (u t) x := by
    intro t ht k x
    rw [show (fun y : M ↦ u t y + k) =
        (fun y : M ↦ (C * Real.exp ((-rate) * t) + k) - Q t y) by
      funext y
      simp [u]
      ring]
    rw [hlap_const_sub t ht (C * Real.exp ((-rate) * t) + k) x]
    rw [show u t =
        (fun y : M ↦ C * Real.exp ((-rate) * t) - Q t y) by
      funext y
      rfl]
    rw [hlap_const_sub t ht (C * Real.exp ((-rate) * t)) x]
  have hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + (-rate) * u t x ≤ u' t x := by
    intro t ht x
    rw [show u t =
        (fun y : M ↦ C * Real.exp ((-rate) * t) - Q t y) by
      funext y
      rfl]
    rw [hlap_const_sub t ht (C * Real.exp ((-rate) * t)) x]
    have hevol := hQevol t ht x
    dsimp only [u']
    change
      -lap t (Q t) x + (-rate) *
          (C * Real.exp ((-rate) * t) - Q t x) ≤
        (-rate) * C * Real.exp ((-rate) * t) - Q' t x
    linarith
  have hmin_lap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x := by
    intro t ht x hmin
    have hmax : IsMaxOn (Q t) Set.univ x := by
      rw [isMaxOn_iff]
      intro y hy
      have h := (isMinOn_iff.mp hmin) y hy
      change u t x ≤ u t y at h
      dsimp only [u] at h
      linarith
    rw [show u t =
        (fun y : M ↦ C * Real.exp ((-rate) * t) - Q t y) by
      funext y
      rfl]
    rw [hlap_const_sub t ht (C * Real.exp ((-rate) * t)) x]
    exact neg_nonneg.mpr (hmax_lap t ht x hmax)
  have h0 : ∀ x : M, 0 ≤ u 0 x := by
    intro x
    dsimp only [u]
    simpa using sub_nonneg.mpr (hQ0 x)
  have hu_nonneg := closed_parabolic_min_principle_var_continuousOn
    (M := M) (lap := lap) (u := u) (u' := u')
      (c := fun _ _ ↦ -rate) (T := T) (M₀ := -rate)
      hT0 (fun _ _ _ ↦ le_rfl) hu_cont hud hlap_add_const hsuper
        hmin_lap h0
  intro t ht x
  have h := hu_nonneg t ht x
  dsimp only [u] at h
  linarith

end Poincare
