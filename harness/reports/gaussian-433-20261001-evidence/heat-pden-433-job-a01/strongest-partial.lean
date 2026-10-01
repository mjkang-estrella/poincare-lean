import Poincare.Global.HeatKernelPDE

/-!
# The finite-dimensional Euclidean heat-kernel PDE

This file closes the positive-time heat equation for the explicit Gaussian
heat kernel on a finite-dimensional real inner-product space.  The final
theorem keeps the target statement from `M2-heat-2`: the only spelling
adaptation is the explicit `(E := E)` arguments already used throughout the
heat-kernel files.
-/

noncomputable section

open scoped InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- First spatial derivative of the negative scaled squared norm. -/
theorem hasFDerivAt_neg_norm_sq_div (t : ℝ) (ht : t ≠ 0) (x : E) :
    HasFDerivAt (fun y : E ↦ -(‖y‖ ^ 2) / (4 * t))
      ((-(1 / (2 * t))) • (innerSL ℝ x)) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(1 / (4 * t)))
  convert! h using 1
  · ext y
    field_simp [ht]
  · ext y
    simp
    field_simp [ht]
    ring


end Poincare
