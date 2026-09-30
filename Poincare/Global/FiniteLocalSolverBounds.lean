import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
Finite aggregation of bounds and lifespans for the actual local parametrices.
The empty family still receives a positive interval of length one.
-/

open scoped BigOperators

namespace Poincare.FiniteLocalSolverBounds

/-- Choose common bounds and a positive lifespan before choosing the solver time. -/
theorem exists_common_bounds_and_lifespan
    (n : ℕ) (C D τ : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hD : ∀ i, 0 ≤ D i) (hτ : ∀ i, 0 < τ i) :
    ∃ C₀ D₀ δ : ℝ, 0 ≤ C₀ ∧ 0 ≤ D₀ ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ i, C i ≤ C₀ ∧ D i ≤ D₀ ∧ δ ≤ τ i := by
  have hsumC : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  have hsumD : 0 ≤ ∑ i, D i := Finset.sum_nonneg fun i _ => hD i
  have hinv : ∀ i, 0 ≤ 1 / τ i := fun i => (one_div_pos.mpr (hτ i)).le
  have hsumInv : 0 ≤ ∑ i, 1 / τ i := Finset.sum_nonneg fun i _ => hinv i
  have hden : 0 < 1 + ∑ i, 1 / τ i := by linarith
  refine ⟨∑ i, C i, ∑ i, D i, 1 / (1 + ∑ i, 1 / τ i),
    hsumC, hsumD, one_div_pos.mpr hden, ?_, ?_⟩
  · exact (div_le_one hden).mpr (by linarith)
  · intro i
    refine ⟨Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i),
      Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i), ?_⟩
    apply (one_div_le hden (hτ i)).mpr
    have hi : 1 / τ i ≤ ∑ j, 1 / τ j :=
      Finset.single_le_sum (fun j _ => hinv j) (Finset.mem_univ i)
    linarith

end Poincare.FiniteLocalSolverBounds
