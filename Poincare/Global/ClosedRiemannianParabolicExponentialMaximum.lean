import Poincare.Global.ParabolicExponentialMaximum

/-!
# Closed-Riemannian exponential maximum comparison

This specializes the abstract exponential parabolic maximum theorem to the
time-dependent closed Riemannian Laplacian.  Spatial `C²` regularity supplies
both linearity against a spatial constant and the nonpositive Laplacian at a
spatial maximum.  Thus callers provide only the pointwise parabolic evolution
inequality of the geometric scalar they are studying.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M] [IsManifold I ∞ M]
variable [CompactSpace M] [Nonempty M]

/-- A coercive pointwise parabolic inequality for a scalar along a closed
Riemannian metric path gives its exponential pointwise bound on a finite
slab. -/
theorem closedRiemannian_parabolic_exp_decay_continuousOn
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (Q Q' : ℝ → M → ℝ) {T rate C : ℝ}
    (hT0 : 0 ≤ T)
    (hQ_cont : ContinuousOn (Function.uncurry Q)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hQd : ∀ x : M, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ Q s x) (Q' t x) t)
    (hQ₂ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2 (Q t) x)
    (hQevol : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      Q' t x ≤ (gt t).laplacianAt (Q t) x - rate * Q t x)
    (hQ0 : ∀ x : M, Q 0 x ≤ C) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      Q t x ≤ C * Real.exp ((-rate) * t) := by
  apply closed_parabolic_maximum_exp_decay_continuousOn
    (M := M) (lap := fun t f x ↦ (gt t).laplacianAt f x)
      (Q := Q) (Q' := Q') hT0 hQ_cont hQd
  · intro t ht a x
    have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (Q t) y :=
      fun y ↦ hQ₂ t ht y
    have hfun : (fun y : M ↦ a - Q t y) =
        (fun _ : M ↦ a) + (-1 : ℝ) • (Q t) := by
      funext y
      simp [sub_eq_add_neg]
    rw [hfun]
    rw [(gt t).laplacianAt_add'
      (f := fun _ : M ↦ a) (h := (-1 : ℝ) • (Q t)) (x := x)
      (fun _ ↦ contMDiffAt_const)
      (fun y ↦ contMDiffAt_const.smul (hf y))]
    rw [(gt t).laplacianAt_const a x]
    rw [(gt t).laplacianAt_const_smul'
      (c := -1) (f := Q t) (x := x) hf]
    ring
  · exact hQevol
  · intro t ht x hmax
    exact laplacianAt_nonpos_of_isLocalMax
      (g := gt t) (f := Q t) (x := x) (fun y ↦ hQ₂ t ht y)
        (hmax.isLocalMax Filter.univ_mem)
  · exact hQ0

/-- Forward-time form: slab continuity plus a pointwise coercive parabolic
inequality on `Ici 0` produce an exponential bound at every nonnegative
time. -/
theorem closedRiemannian_parabolic_exp_decay_Ici
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (Q Q' : ℝ → M → ℝ) {rate C : ℝ}
    (hQ_cont : ∀ T : ℝ, 0 ≤ T →
      ContinuousOn (Function.uncurry Q)
        (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hQd : ∀ x : M, ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ Q s x) (Q' t x) t)
    (hQ₂ : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2 (Q t) x)
    (hQevol : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      Q' t x ≤ (gt t).laplacianAt (Q t) x - rate * Q t x)
    (hQ0 : ∀ x : M, Q 0 x ≤ C) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
      Q t.1 x ≤ C * Real.exp ((-rate) * t.1) := by
  intro t x
  apply closedRiemannian_parabolic_exp_decay_continuousOn
    gt Q Q' t.2 (hQ_cont t.1 t.2)
  · intro y s hs
    exact hQd y s hs.1
  · intro s hs y
    exact hQ₂ s hs.1 y
  · intro s hs y
    exact hQevol s hs.1 y
  · exact hQ0
  · exact ⟨t.2, le_rfl⟩

end Poincare
