import Poincare.Global.FiniteExtinctionIntegratingFactor

/-!
# Automatic initial scalar-barrier scale

The Hamilton lower barrier is commonly parameterized by a positive constant
`C` satisfying `-3/(2C) ≤ R₀`.  Such a scale exists for every real initial
scalar lower bound, so it need not be retained as an independent geometric
hypothesis.
-/

namespace Poincare

/-- Every real scalar lower bound admits a positive Hamilton barrier scale. -/
theorem exists_positive_hamilton_scalar_barrier_scale (R₀ : ℝ) :
    ∃ C > (0 : ℝ), -(3 / (2 * C)) ≤ R₀ := by
  by_cases hR : 0 ≤ R₀
  · refine ⟨1, zero_lt_one, ?_⟩
    norm_num
    linarith
  · have hRneg : R₀ < 0 := lt_of_not_ge hR
    let C : ℝ := -3 / (2 * R₀)
    have hdenneg : 2 * R₀ < 0 := mul_neg_of_pos_of_neg (by norm_num) hRneg
    have hC : 0 < C := by
      dsimp [C]
      exact div_pos_of_neg_of_neg (by norm_num) hdenneg
    refine ⟨C, hC, ?_⟩
    have hRne : R₀ ≠ 0 := ne_of_lt hRneg
    have hCne : C ≠ 0 := ne_of_gt hC
    have heq : -(3 / (2 * C)) = R₀ := by
      dsimp [C]
      field_simp [hRne]
    exact heq.le

end Poincare
