import Poincare.Global.ExponentialMap

/-!
# Controlled continuous Picard--Lindelof selectors

The repository's endpoint-controlled selector exposes the invariant closed
ball, while Mathlib's selector exposes joint continuity.  Both properties
come from the same family of fixed points.  This module records them
simultaneously, so a variational construction can retain tube control and
continuity without comparing two independently chosen solution families.
-/

noncomputable section

open Function Metric Set
open scoped NNReal Topology

namespace IsPicardLindelof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
variable {x₀ : E} {a r L K : ℝ≥0}

/-- One selected Picard--Lindelof family with initial-value, ODE,
closed-ball, and joint-continuity properties all retained. -/
theorem exists_controlled_continuous_selector
    [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ alpha : E → ℝ → E,
      (∀ x ∈ closedBall x₀ r,
        alpha x t₀ = x ∧
          (∀ t ∈ Icc tmin tmax,
            HasDerivWithinAt (alpha x) (f t (alpha x t))
              (Icc tmin tmax) t) ∧
          ∀ t ∈ Icc tmin tmax, alpha x t ∈ closedBall x₀ a) ∧
      ContinuousOn (Function.uncurry alpha)
        (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  classical
  have hfixed (x : E) (hx : x ∈ closedBall x₀ r) :
      ∃ gamma : ODE.FunSpace t₀ x₀ r L,
        IsFixedPt (ODE.FunSpace.next hf hx) gamma :=
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose gamma hgamma using hfixed
  let alpha : E → ℝ → E :=
    fun x ↦ if hx : x ∈ closedBall x₀ r then (gamma x hx).compProj else 0
  have halpha : ∀ x ∈ closedBall x₀ r,
      alpha x t₀ = x ∧
        (∀ t ∈ Icc tmin tmax,
          HasDerivWithinAt (alpha x) (f t (alpha x t))
            (Icc tmin tmax) t) ∧
        ∀ t ∈ Icc tmin tmax, alpha x t ∈ closedBall x₀ a := by
    intro x hx
    have halphaEq : alpha x = (gamma x hx).compProj := by
      dsimp only [alpha]
      rw [dif_pos hx]
    refine ⟨?_, ?_, ?_⟩
    · rw [halphaEq, ODE.FunSpace.compProj_val, ← hgamma x hx,
        ODE.FunSpace.next_apply₀]
    · intro t ht
      rw [halphaEq, ODE.FunSpace.compProj_apply]
      apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
        ((gamma x hx).continuous_compProj.continuousOn)
        (fun _ _ ↦ (gamma x hx).compProj_mem_closedBall hf.mul_max_le)
        x ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hgamma x hx]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    · intro t ht
      rw [halphaEq]
      exact (gamma x hx).compProj_mem_closedBall hf.mul_max_le
  have htimeLip : ∃ L' : ℝ≥0,
      ∀ t ∈ Icc tmin tmax,
        LipschitzOnWith L' (alpha · t) (closedBall x₀ r) := by
    obtain ⟨L', hdist⟩ :=
      ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have halphaX : alpha x = (gamma x hx).compProj := by
      dsimp only [alpha]
      rw [dif_pos hx]
    have halphaY : alpha y = (gamma y hy).compProj := by
      dsimp only [alpha]
      rw [dif_pos hy]
    rw [halphaX, halphaY, ODE.FunSpace.compProj_apply,
      ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    haveI : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact hdist x y hx hy (gamma x hx) (gamma y hy)
      (hgamma x hx) (hgamma y hy)
  rcases htimeLip with ⟨L', htimeLip⟩
  refine ⟨alpha, halpha, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ htimeLip
  intro x hx
  exact HasDerivWithinAt.continuousOn
    (fun t ht ↦ (halpha x hx).2.1 t ht)

end IsPicardLindelof
