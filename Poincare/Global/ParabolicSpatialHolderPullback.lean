import Poincare.Global.RiemannianContext
import Poincare.Global.ParabolicHolderSpace
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Actual nonlinear spatial pullback on parabolic Hölder carriers

A compactly supported smooth spatial map supplies its own Lipschitz bound.
Spatial substitution preserves the time cylinder and therefore its zero
extension. The resulting carrier operator is linear in the input function,
with a bound fixed before the time interval is chosen. This is an input to
derivative-compatible chart transport toward Hamilton flow existence.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff NNReal

universe v

namespace Poincare.ParabolicSpatialHolderPullback

open ParabolicHolder
local notation "E" => ClosedSmoothModel 3

/-- A nonlinear spatial Lipschitz map controls the true parabolic distance. -/
theorem parabolicDist_comp_le {F : E → E} {L : ℝ≥0}
    (hF : LipschitzWith L F) (p q : ℝ × E) :
    parabolicDist (p.1, F p.2) (q.1, F q.2) ≤
      max 1 (L : ℝ) * parabolicDist p q := by
  have hs : ‖F p.2 - F q.2‖ ≤ max 1 (L : ℝ) * ‖p.2 - q.2‖ :=
    (hF.norm_sub_le p.2 q.2).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have ht : Real.sqrt |p.1 - q.1| ≤
      max 1 (L : ℝ) * Real.sqrt |p.1 - q.1| := by
    simpa using mul_le_mul_of_nonneg_right (le_max_left 1 (L : ℝ))
      (Real.sqrt_nonneg |p.1 - q.1|)
  simpa only [parabolicDist, mul_add] using add_le_add hs ht

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {α T : ℝ}

/-- Substitution carries the actual Hölder seminorm bound to the same cylinder. -/
theorem holderBound_comp (hα : 0 ≤ α) (F : E → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (f : Y («E» := E) α T V) :
    HasHolderBound α (cylinder T) (fun p ↦ f (p.1, F p.2))
      (max 1 ((L : ℝ) ^ α) * holderSeminorm α (cylinder T) f) := by
  intro p hp q hq
  have hp' : (p.1, F p.2) ∈ cylinder T := ⟨hp.1, mem_univ _⟩
  have hq' : (q.1, F q.2) ∈ cylinder T := ⟨hq.1, mem_univ _⟩
  have hd : parabolicDist (p.1, F p.2) (q.1, F q.2) ^ α ≤
      max 1 ((L : ℝ) ^ α) * parabolicDist p q ^ α := by
    have h := Real.rpow_le_rpow (parabolicDist_nonneg _ _)
      (parabolicDist_comp_le hF p q) hα
    simpa only [Real.mul_rpow (by positivity : 0 ≤ max 1 (L : ℝ))
      (parabolicDist_nonneg p q), Real.rpow_max zero_le_one L.coe_nonneg hα,
      Real.one_rpow] using h
  calc
    ‖f (p.1, F p.2) - f (q.1, F q.2)‖ ≤
        holderSeminorm α (cylinder T) f *
          parabolicDist (p.1, F p.2) (q.1, F q.2) ^ α :=
      hasHolderBound_seminorm f _ hp' _ hq'
    _ ≤ holderSeminorm α (cylinder T) f *
        (max 1 ((L : ℝ) ^ α) * parabolicDist p q ^ α) :=
      mul_le_mul_of_nonneg_left hd (holderSeminorm_nonneg f)
    _ = _ := by ring

/-- The genuine carrier obtained by composing the spatial argument. -/
def pullback (hα : 0 ≤ α) (F : E → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (f : Y («E» := E) α T V) : Y («E» := E) α T V :=
  ofFunction (fun p ↦ f (p.1, F p.2))
    (fun p hp ↦ zero_off f (p := (p.1, F p.2))
      (fun h ↦ hp ⟨h.1, mem_univ _⟩))
    ⟨supNorm (cylinder T) f, fun p _ ↦ le_supNorm f (p.1, F p.2)⟩
    ⟨_, holderBound_comp hα F hF f⟩

/-- The carrier sum norm has a bound independent of the time interval. -/
theorem norm_pullback_le (hα : 0 ≤ α) (F : E → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (f : Y («E» := E) α T V) :
    ‖pullback hα F hF f‖ ≤ max 1 ((L : ℝ) ^ α) * ‖f‖ := by
  have hb := norm_le_of_bounds (pullback hα F hF f) (supNorm_nonneg f)
    (mul_nonneg (by positivity) (holderSeminorm_nonneg f))
    (fun p _ ↦ le_supNorm f (p.1, F p.2)) (holderBound_comp hα F hF f)
  have hm : supNorm (cylinder T) f ≤
      max 1 ((L : ℝ) ^ α) * supNorm (cylinder T) f := by
    simpa using mul_le_mul_of_nonneg_right (le_max_left 1 ((L : ℝ) ^ α))
      (supNorm_nonneg f)
  rw [ParabolicHolder.norm_eq f]
  nlinarith only [hb, hm]

/-- Construct actual bounded spatial pullback operators and one bound for every
time interval from the compact smooth map alone. -/
theorem exists_spatial_Y_pullback
    (F : E → E) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (α : ℝ) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ,
      ∃ Q : Y («E» := E) α T V →L[ℝ] Y («E» := E) α T V,
        ‖Q‖ ≤ C ∧ ∀ f p, Q f p = f (p.1, F p.2) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcF hF (by simp)
  let C := max 1 ((L : ℝ) ^ α)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T
  let Qlin : Y («E» := E) α T V →ₗ[ℝ] Y («E» := E) α T V := {
    toFun := pullback hα F hL
    map_add' := by
      intro f g
      apply ParabolicHolder.ext
      intro p _
      rfl
    map_smul' := by
      intro c f
      apply ParabolicHolder.ext
      intro p _
      rfl }
  have hbound : ∀ f, ‖Qlin f‖ ≤ C * ‖f‖ :=
    fun f ↦ norm_pullback_le hα F hL f
  refine ⟨Qlin.mkContinuous C hbound, Qlin.mkContinuous_norm_le hC hbound, ?_⟩
  intro f p
  rfl

end Poincare.ParabolicSpatialHolderPullback
