import Poincare.Global.HamiltonScalarGradientEstimate

noncomputable section
set_option autoImplicit false

namespace Poincare.HamiltonScalarGradientQuotientBound

/-- The algebraic core of Hamilton's quotient-eight estimate.

`hWeighted` is the expansion of
`|2 R ∇Ric - ∇R ⊗ Ric|² ≥ 0`, while `hHessian` is the expansion of
`|R Hess R - ∇R ⊗ ∇R|² ≥ 0`.  Keeping these two geometric inputs
separate makes explicit exactly what remains to be connected to the intrinsic
tensor definitions.  The variable normalized-flow term is retained on both
sides rather than discarded.
-/
theorem quotient_reaction_le_eight_of_square_completions
    {R S H P N A G r Q : ℝ}
    (hR : 0 < R)
    (hWeighted : 2 * R * P ≤ 4 * R ^ 2 * A + S * N)
    (hHessian : 0 ≤ R ^ 2 * H - R * G + S ^ 2) :
    -2 * H / R + 4 * P / R - 2 * S * N / R ^ 2 +
          2 * G / R ^ 2 - 2 * S ^ 2 / R ^ 3 - (4 / 3 : ℝ) * r * Q ≤
      8 * A - (4 / 3 : ℝ) * r * Q := by
  have hWeighted' := mul_le_mul_of_nonneg_left hWeighted (show 0 ≤ 2 * R by positivity)
  have hCore :
      -2 * H / R + 4 * P / R - 2 * S * N / R ^ 2 +
          2 * G / R ^ 2 - 2 * S ^ 2 / R ^ 3 ≤ 8 * A := by
    rw [show -2 * H / R + 4 * P / R - 2 * S * N / R ^ 2 +
          2 * G / R ^ 2 - 2 * S ^ 2 / R ^ 3 =
        (-2 * R ^ 2 * H + 4 * R ^ 2 * P - 2 * R * S * N +
          2 * R * G - 2 * S ^ 2) / R ^ 3 by
      field_simp]
    apply (div_le_iff₀ (pow_pos hR 3)).2
    nlinarith
  linarith

end Poincare.HamiltonScalarGradientQuotientBound
