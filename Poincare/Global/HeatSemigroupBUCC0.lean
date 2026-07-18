import Poincare.Global.HeatSemigroupBUCOperator
import Poincare.Global.HeatKernelSemigroup

/-!
# The heat operators form a contraction `C₀` semigroup on `BUC`

This closes the algebraic side of the intrinsic Duhamel theory: in addition to
strong continuity and norm nonexpansion, the restricted heat operators compose
by addition of nonnegative times.
-/

noncomputable section

open Filter Set
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Positive-time semigroup law after restriction to `BUC`. -/
theorem vectorHeatSemigroupBUCLM_comp
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (vectorHeatSemigroupBUCLM (E := E) (F := F) hs).comp
        (vectorHeatSemigroupBUCLM (E := E) (F := F) ht) =
      vectorHeatSemigroupBUCLM (E := E) (F := F) (add_pos hs ht) := by
  ext f x
  have h := congrArg
    (fun A : (E →ᵇ F) →L[ℝ] (E →ᵇ F) ↦ A (f : E →ᵇ F))
    (vectorHeatSemigroupCLM_comp (E := E) (F := F) hs ht)
  exact congrArg (fun g : E →ᵇ F ↦ g x) h

/-- Nonnegative-time semigroup law for the zero-time extension. -/
theorem vectorHeatSemigroupBUCExtended_comp
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (vectorHeatSemigroupBUCExtended (E := E) (F := F) s).comp
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) t) =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (s + t) := by
  rcases hs.eq_or_lt with rfl | hspos
  · simp [vectorHeatSemigroupBUCExtended]
  rcases ht.eq_or_lt with rfl | htpos
  · simp [vectorHeatSemigroupBUCExtended]
  rw [vectorHeatSemigroupBUCExtended, dif_pos hspos,
    vectorHeatSemigroupBUCExtended, dif_pos htpos,
    vectorHeatSemigroupBUCExtended, dif_pos (add_pos hspos htpos)]
  exact vectorHeatSemigroupBUCLM_comp (E := E) (F := F) hspos htpos

/-- Pointwise form of the nonnegative-time semigroup law. -/
theorem vectorHeatSemigroupBUCExtended_add_apply
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : BoundedUniformContinuousFunction (E := E) (F := F)) :
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) t f) =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (s + t) f := by
  have h := congrArg
    (fun A :
      BoundedUniformContinuousFunction (E := E) (F := F) →L[ℝ]
        BoundedUniformContinuousFunction (E := E) (F := F) ↦ A f)
    (vectorHeatSemigroupBUCExtended_comp (E := E) (F := F) hs ht)
  exact h

/-- Consolidated `C₀` contraction-semigroup payload for the intrinsic heat
operators. -/
theorem vectorHeatSemigroupBUCExtended_c0_contracting :
    (vectorHeatSemigroupBUCExtended (E := E) (F := F) 0 =
      ContinuousLinearMap.id ℝ _) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) s).comp
          (vectorHeatSemigroupBUCExtended (E := E) (F := F) t) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (s + t)) ∧
    (∀ f : BoundedUniformContinuousFunction (E := E) (F := F),
      Continuous (fun t : ℝ ↦
        vectorHeatSemigroupBUCExtended (E := E) (F := F) t f)) ∧
    (∀ t : ℝ, ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t‖ ≤ 1) := by
  refine ⟨vectorHeatSemigroupBUCExtended_zero (E := E) (F := F), ?_, ?_, ?_⟩
  · intro s t hs ht
    exact vectorHeatSemigroupBUCExtended_comp (E := E) (F := F) hs ht
  · intro f
    exact continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) f
  · intro t
    by_cases ht : 0 < t
    · simp [vectorHeatSemigroupBUCExtended, ht,
        norm_vectorHeatSemigroupBUCLM_le_one (E := E) (F := F) ht]
    · simp [vectorHeatSemigroupBUCExtended, ht, ContinuousLinearMap.norm_id_le]

end Poincare
