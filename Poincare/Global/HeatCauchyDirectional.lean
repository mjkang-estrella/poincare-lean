import Poincare.Global.HeatCauchyTheorem

/-!
# Directional heat-kernel Cauchy work surface

This module records the verified directional kernel calculation needed by the
coordinate route to the heat Cauchy theorem.  The scalar calculation below is
the non-vacuous local payload isolated by `M2-heat-11`: along a fixed affine
line, the second derivative of the heat kernel is the diagonal second
Frechet derivative of the Gaussian kernel.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Diagonal second spatial Fréchet derivative of the normalized heat kernel. -/
theorem iteratedFDeriv_two_heatKernel_apply {t : ℝ} (ht : t ≠ 0) (u v : E) :
    iteratedFDeriv ℝ 2 (fun z : E => heatKernel (E := E) t z) u ![v, v] =
      heatKernel (E := E) t u *
        (⟪u, v⟫_ℝ ^ 2 / (4 * t ^ 2) - ‖v‖ ^ 2 / (2 * t)) := by
  let A : ℝ := (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  let G : E → ℝ := fun z => Real.exp (-(‖z‖ ^ 2) / (4 * t))
  have hG : ContDiffAt ℝ 2 G u := by
    dsimp [G]
    exact (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp).contDiffAt
  have hheat : (fun z : E => heatKernel (E := E) t z) = A • G := by
    funext z
    simp [A, G, heatKernel, smul_eq_mul]
  rw [hheat]
  rw [iteratedFDeriv_const_smul_apply hG]
  change A * (iteratedFDeriv ℝ 2 G u ![v, v]) =
    heatKernel (E := E) t u *
      (⟪u, v⟫_ℝ ^ 2 / (4 * t ^ 2) - ‖v‖ ^ 2 / (2 * t))
  have hG_two :
      iteratedFDeriv ℝ 2 G u ![v, v] =
        Real.exp (-(‖u‖ ^ 2) / (4 * t)) *
          (⟪u, v⟫_ℝ ^ 2 / (4 * t ^ 2) - ‖v‖ ^ 2 / (2 * t)) := by
    simpa [G] using iteratedFDeriv_two_exp_neg_norm_sq_div_apply (E := E) t ht u v
  rw [hG_two]
  simp [A, heatKernel]
  ring

/--
Second derivative of the heat kernel along an affine line in a fixed spatial
direction.
-/
theorem iteratedDeriv_two_heatKernel_spatial_line {t : ℝ} (ht : t ≠ 0)
    (x y v : E) :
    iteratedDeriv 2 (fun r : ℝ => heatKernel (E := E) t (x + r • v - y)) 0 =
      heatKernel (E := E) t (x - y) *
        (⟪x - y, v⟫_ℝ ^ 2 / (4 * t ^ 2) - ‖v‖ ^ 2 / (2 * t)) := by
  have hline :
      (fun r : ℝ => heatKernel (E := E) t (x + r • v - y)) =
        fun r : ℝ => heatKernel (E := E) t ((x - y) + r • v) := by
    funext r
    congr 1
    abel
  rw [hline]
  have hcd : ContDiff ℝ 2 (fun z : E => heatKernel (E := E) t z) :=
    (contDiff_heatKernel_spatial (E := E) t).of_le le_top
  rw [iteratedDeriv_two_affine_line_eq_iteratedFDeriv
    (E := E) (fun z : E => heatKernel (E := E) t z) hcd (x - y) v]
  exact iteratedFDeriv_two_heatKernel_apply (E := E) ht (x - y) v

end Poincare
