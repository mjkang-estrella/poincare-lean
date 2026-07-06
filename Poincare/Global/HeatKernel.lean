import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Euclidean heat kernel seed

This file starts the model-space heat-equation layer with the explicit
Gaussian heat kernel on finite-dimensional real inner-product spaces.  The
lemmas here deliberately stay at the first usable calculus facts: positivity
for positive time and smoothness in the spatial variable.
-/

noncomputable section

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The scalar Gaussian heat kernel on a finite-dimensional real inner-product
space.

For `E = EuclideanSpace ℝ (Fin n)` the exponent is `-n / 2`.
-/
def heatKernel [FiniteDimensional ℝ E] (t : ℝ) (x : E) : ℝ :=
  (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (-(‖x‖ ^ 2) / (4 * t))

/-- The Gaussian heat kernel is strictly positive at positive time. -/
theorem heatKernel_pos [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
    0 < heatKernel (E := E) t x := by
  have hbase : 0 < 4 * Real.pi * t := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (Real.exp_pos _)

/-- The Gaussian heat kernel is nonnegative at positive time. -/
theorem heatKernel_nonneg [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
    0 ≤ heatKernel (E := E) t x :=
  (heatKernel_pos (E := E) ht x).le

/--
For fixed time, the heat kernel is smooth in the spatial variable.

The statement is global in `t`: even at nonpositive times the displayed formula
is still a constant multiple of an exponential of the smooth squared norm.
-/
theorem contDiff_heatKernel_spatial [FiniteDimensional ℝ E] (t : ℝ) :
    ContDiff ℝ ⊤ fun x : E ↦ heatKernel (E := E) t x := by
  unfold heatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp)

/-- Pointwise version of spatial smoothness. -/
theorem contDiffAt_heatKernel_spatial [FiniteDimensional ℝ E] (t : ℝ) (x : E) :
    ContDiffAt ℝ ⊤ (fun y : E ↦ heatKernel (E := E) t y) x :=
  (contDiff_heatKernel_spatial (E := E) t).contDiffAt

end Poincare
