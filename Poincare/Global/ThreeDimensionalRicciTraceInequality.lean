import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The three-dimensional Ricci trace inequality

For the three eigenvalues of a symmetric Ricci tensor, Cauchy--Schwarz gives

`R² = (λ₁ + λ₂ + λ₃)² ≤ 3 (λ₁² + λ₂² + λ₃²) = 3 |Ric|²`.

This elementary finite-dimensional estimate is the algebraic source of the
coefficient `2/3` in the scalar-curvature minimum inequality under Ricci flow.
-/

noncomputable section

open scoped BigOperators

namespace Poincare

/-- Trace-square is bounded by three times the sum of eigenvalue squares in
dimension three. -/
theorem three_trace_sq_le_three_sum_sq (eig : Fin 3 → ℝ) :
    (∑ i, eig i) ^ 2 ≤ 3 * ∑ i, (eig i) ^ 2 := by
  norm_num [Fin.sum_univ_succ]
  nlinarith [sq_nonneg (eig 0 - eig 1), sq_nonneg (eig 1 - eig 2),
    sq_nonneg (eig 2 - eig 0)]

/-- Equivalent Ricci-flow normalization: twice the squared Ricci norm
dominates `(2/3) R²`. -/
theorem two_thirds_trace_sq_le_two_sum_sq (eig : Fin 3 → ℝ) :
    ((2 : ℝ) / 3) * (∑ i, eig i) ^ 2 ≤ 2 * ∑ i, (eig i) ^ 2 := by
  nlinarith [three_trace_sq_le_three_sum_sq eig]

/-- The diagonal square sum is bounded by the full coordinate Frobenius
square sum. -/
theorem sum_diagonal_sq_le_sum_matrix_sq
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ i, (A i i) ^ 2) ≤ ∑ i, ∑ j, (A i j) ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.single_le_sum
    (fun j hj => sq_nonneg (A i j)) (Finset.mem_univ i)

/-- Coordinate-free-in-use matrix form: the square of the trace is at most
three times the Frobenius coordinate square sum.  Symmetry is not needed for
the inequality itself. -/
theorem three_matrix_trace_sq_le_three_frobenius_sq
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.trace ^ 2 ≤ 3 * ∑ i, ∑ j, (A i j) ^ 2 := by
  have htrace := three_trace_sq_le_three_sum_sq (fun i => A i i)
  have hdiag := sum_diagonal_sq_le_sum_matrix_sq A
  calc
    A.trace ^ 2 = (∑ i, A i i) ^ 2 := rfl
    _ ≤ 3 * ∑ i, (A i i) ^ 2 := htrace
    _ ≤ 3 * ∑ i, ∑ j, (A i j) ^ 2 :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)

/-- Ricci-flow normalization of the matrix trace inequality. -/
theorem two_thirds_matrix_trace_sq_le_two_frobenius_sq
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ((2 : ℝ) / 3) * A.trace ^ 2 ≤
      2 * ∑ i, ∑ j, (A i j) ^ 2 := by
  nlinarith [three_matrix_trace_sq_le_three_frobenius_sq A]

/-- A Hessian with nonnegative diagonal entries in an orthonormal frame has
nonnegative trace, hence nonnegative Laplacian. -/
theorem matrix_trace_nonneg_of_diagonal_nonneg
    (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hdiag : ∀ i, 0 ≤ H i i) :
    0 ≤ H.trace := by
  change 0 ≤ ∑ i, H i i
  exact Finset.sum_nonneg (fun i hi => hdiag i)

/-- At a spatial scalar-curvature minimum, a nonnegative Laplacian term and
the Ricci-flow evolution equation imply the scalar Riccati inequality. -/
theorem scalar_riccati_inequality_of_three_ricci_eigenvalues
    {R dR lap : ℝ} (eig : Fin 3 → ℝ)
    (htrace : R = ∑ i, eig i)
    (hlap : 0 ≤ lap)
    (hevolution : dR = lap + 2 * ∑ i, (eig i) ^ 2) :
    ((2 : ℝ) / 3) * R ^ 2 ≤ dR := by
  rw [htrace, hevolution]
  nlinarith [two_thirds_trace_sq_le_two_sum_sq eig]

/-- Matrix-coordinate form of the scalar Riccati inequality.  An orthonormal
frame supplies `A`; the full square sum is the squared Ricci norm. -/
theorem scalar_riccati_inequality_of_three_ricci_matrix
    {R dR lap : ℝ} (A : Matrix (Fin 3) (Fin 3) ℝ)
    (htrace : R = A.trace)
    (hlap : 0 ≤ lap)
    (hevolution : dR = lap + 2 * ∑ i, ∑ j, (A i j) ^ 2) :
    ((2 : ℝ) / 3) * R ^ 2 ≤ dR := by
  rw [htrace, hevolution]
  nlinarith [two_thirds_matrix_trace_sq_le_two_frobenius_sq A]

/-- Minimum-Hessian form: the Laplacian nonnegativity premise is derived from
nonnegative Hessian diagonal entries in the chosen orthonormal frame. -/
theorem scalar_riccati_inequality_of_three_ricci_matrix_at_minimum
    {R dR lap : ℝ}
    (A H : Matrix (Fin 3) (Fin 3) ℝ)
    (htrace : R = A.trace)
    (hlapTrace : lap = H.trace)
    (hHdiag : ∀ i, 0 ≤ H i i)
    (hevolution : dR = lap + 2 * ∑ i, ∑ j, (A i j) ^ 2) :
    ((2 : ℝ) / 3) * R ^ 2 ≤ dR := by
  apply scalar_riccati_inequality_of_three_ricci_matrix
    (R := R) (dR := dR) (lap := lap) A htrace
  · rw [hlapTrace]
    exact matrix_trace_nonneg_of_diagonal_nonneg H hHdiag
  · exact hevolution

/-- Time-dependent pointwise form, ready to discharge the Riccati premise in
the scalar-barrier theorems. -/
theorem scalar_riccati_inequality_family_of_three_ricci_eigenvalues
    (R dR lap : ℝ → ℝ) (eig : ℝ → Fin 3 → ℝ)
    (htrace : ∀ t, R t = ∑ i, eig t i)
    (hlap : ∀ t, 0 ≤ lap t)
    (hevolution : ∀ t, dR t = lap t + 2 * ∑ i, (eig t i) ^ 2) :
    ∀ t, ((2 : ℝ) / 3) * (R t) ^ 2 ≤ dR t := by
  intro t
  exact scalar_riccati_inequality_of_three_ricci_eigenvalues
    (eig t) (htrace t) (hlap t) (hevolution t)

/-- Segment-indexed version matching a Ricci flow with surgery. -/
theorem scalar_riccati_inequality_segmented_of_three_ricci_eigenvalues
    (R dR lap : ℕ → ℝ → ℝ) (eig : ℕ → ℝ → Fin 3 → ℝ)
    (htrace : ∀ k t, R k t = ∑ i, eig k t i)
    (hlap : ∀ k t, 0 ≤ lap k t)
    (hevolution : ∀ k t,
      dR k t = lap k t + 2 * ∑ i, (eig k t i) ^ 2) :
    ∀ k t, ((2 : ℝ) / 3) * (R k t) ^ 2 ≤ dR k t := by
  intro k t
  exact scalar_riccati_inequality_of_three_ricci_eigenvalues
    (eig k t) (htrace k t) (hlap k t) (hevolution k t)

/-- Segment-indexed matrix-coordinate version matching a Ricci flow with
surgery. -/
theorem scalar_riccati_inequality_segmented_of_three_ricci_matrices
    (R dR lap : ℕ → ℝ → ℝ)
    (A : ℕ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (htrace : ∀ k t, R k t = (A k t).trace)
    (hlap : ∀ k t, 0 ≤ lap k t)
    (hevolution : ∀ k t,
      dR k t = lap k t + 2 * ∑ i, ∑ j, (A k t i j) ^ 2) :
    ∀ k t, ((2 : ℝ) / 3) * (R k t) ^ 2 ≤ dR k t := by
  intro k t
  exact scalar_riccati_inequality_of_three_ricci_matrix
    (A k t) (htrace k t) (hlap k t) (hevolution k t)

/-- Segment-indexed minimum-Hessian form. -/
theorem scalar_riccati_inequality_segmented_of_three_ricci_matrices_at_minimum
    (R dR lap : ℕ → ℝ → ℝ)
    (A H : ℕ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (htrace : ∀ k t, R k t = (A k t).trace)
    (hlapTrace : ∀ k t, lap k t = (H k t).trace)
    (hHdiag : ∀ k t i, 0 ≤ H k t i i)
    (hevolution : ∀ k t,
      dR k t = lap k t + 2 * ∑ i, ∑ j, (A k t i j) ^ 2) :
    ∀ k t, ((2 : ℝ) / 3) * (R k t) ^ 2 ≤ dR k t := by
  intro k t
  exact scalar_riccati_inequality_of_three_ricci_matrix_at_minimum
    (A k t) (H k t) (htrace k t) (hlapTrace k t)
      (hHdiag k t) (hevolution k t)

end Poincare
