import Poincare.Global.DuhamelContraction

/-!
# Local bounds for quadratic parabolic nonlinearities

Ricci--DeTurck coordinate remainders are assembled from bounded bilinear
contractions.  This file records the Banach-space estimate needed to feed such
terms to a local Duhamel contraction: `x ↦ B x x` is bounded by `‖B‖ R²` and
is `2 ‖B‖ R`-Lipschitz on the radius-`R` ball.
-/

noncomputable section

open Set Function
open scoped NNReal

namespace Poincare

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A bounded curried bilinear map evaluated diagonally. -/
def quadraticOfCLM (B : X →L[ℝ] X →L[ℝ] X) (x : X) : X := B x x

/-- The diagonal quadratic term has the expected quadratic norm bound. -/
theorem norm_quadraticOfCLM_le
    (B : X →L[ℝ] X →L[ℝ] X) (x : X) :
    ‖quadraticOfCLM B x‖ ≤ ‖B‖ * ‖x‖ ^ 2 := by
  calc
    ‖quadraticOfCLM B x‖ = ‖B x x‖ := rfl
    _ ≤ ‖B x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖B‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm B x) (norm_nonneg x)
    _ = ‖B‖ * ‖x‖ ^ 2 := by ring

/-- Polarized difference identity for the diagonal quadratic map. -/
theorem quadraticOfCLM_sub
    (B : X →L[ℝ] X →L[ℝ] X) (x y : X) :
    quadraticOfCLM B x - quadraticOfCLM B y =
      B (x - y) x + B y (x - y) := by
  simp [quadraticOfCLM, map_sub]

/-- Pointwise local Lipschitz estimate for a quadratic term. -/
theorem norm_quadraticOfCLM_sub_le
    (B : X →L[ℝ] X →L[ℝ] X) {R : ℝ}
    {x y : X} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖quadraticOfCLM B x - quadraticOfCLM B y‖ ≤
      (2 * ‖B‖ * R) * ‖x - y‖ := by
  rw [quadraticOfCLM_sub]
  calc
    ‖B (x - y) x + B y (x - y)‖
        ≤ ‖B (x - y) x‖ + ‖B y (x - y)‖ := norm_add_le _ _
    _ ≤ (‖B‖ * ‖x - y‖) * ‖x‖ + (‖B‖ * ‖y‖) * ‖x - y‖ := by
      apply add_le_add
      · exact (ContinuousLinearMap.le_opNorm (B (x - y)) x).trans
          (mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.le_opNorm B (x - y)) (norm_nonneg x))
      · exact (ContinuousLinearMap.le_opNorm (B y) (x - y)).trans
          (mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.le_opNorm B y) (norm_nonneg (x - y)))
    _ ≤ (‖B‖ * ‖x - y‖) * R + (‖B‖ * R) * ‖x - y‖ := by
      gcongr
    _ = (2 * ‖B‖ * R) * ‖x - y‖ := by ring

/-- The diagonal quadratic map is Lipschitz on a centered closed ball. -/
theorem lipschitzOnWith_quadraticOfCLM_closedBall
    (B : X →L[ℝ] X →L[ℝ] X) (R : ℝ≥0) :
    LipschitzOnWith ⟨2 * ‖B‖ * (R : ℝ), by positivity⟩
      (quadraticOfCLM B) (Metric.closedBall (0 : X) (R : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_quadraticOfCLM_sub_le B
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hy)

/-- Uniform quadratic bound on a centered closed ball. -/
theorem norm_quadraticOfCLM_le_on_closedBall
    (B : X →L[ℝ] X →L[ℝ] X) (R : ℝ≥0)
    {x : X} (hx : x ∈ Metric.closedBall (0 : X) (R : ℝ)) :
    ‖quadraticOfCLM B x‖ ≤ ‖B‖ * (R : ℝ) ^ 2 := by
  have hxR : ‖x‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  exact (norm_quadraticOfCLM_le B x).trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg x) R.property).2 hxR) (norm_nonneg B))

/-- A point in a ball centered at `c` has norm at most `‖c‖ + R`. -/
theorem norm_le_center_add_nnreal_radius
    (c : X) (R : ℝ≥0) {x : X}
    (hx : x ∈ Metric.closedBall c (R : ℝ)) :
    ‖x‖ ≤ ‖c‖ + (R : ℝ) := by
  calc
    ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (R : ℝ) + ‖c‖ := by
      gcongr
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    _ = ‖c‖ + (R : ℝ) := add_comm _ _

/-- Local Lipschitz estimate on a closed ball with arbitrary center. -/
theorem lipschitzOnWith_quadraticOfCLM_closedBall_center
    (B : X →L[ℝ] X →L[ℝ] X) (c : X) (R : ℝ≥0) :
    LipschitzOnWith ⟨2 * ‖B‖ * (‖c‖ + (R : ℝ)), by positivity⟩
      (quadraticOfCLM B) (Metric.closedBall c (R : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_quadraticOfCLM_sub_le B
    (norm_le_center_add_nnreal_radius c R hx)
    (norm_le_center_add_nnreal_radius c R hy)

/-- Uniform quadratic bound on an arbitrary centered closed ball. -/
theorem norm_quadraticOfCLM_le_on_closedBall_center
    (B : X →L[ℝ] X →L[ℝ] X) (c : X) (R : ℝ≥0)
    {x : X} (hx : x ∈ Metric.closedBall c (R : ℝ)) :
    ‖quadraticOfCLM B x‖ ≤ ‖B‖ * (‖c‖ + (R : ℝ)) ^ 2 := by
  have hxR := norm_le_center_add_nnreal_radius c R hx
  exact (norm_quadraticOfCLM_le B x).trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg x) (by positivity)).2 hxR) (norm_nonneg B))

end Poincare
