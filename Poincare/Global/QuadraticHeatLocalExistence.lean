import Poincare.Global.QuadraticHeatDuhamel

/-!
# An automatic lifespan for the intrinsic quadratic heat-Volterra equation

The ball-contraction theorem in `QuadraticHeatDuhamel` has two explicit
small-time hypotheses.  Here a positive lifespan is chosen from the local
quadratic bound and local Lipschitz constant, so local existence no longer
requires the caller to solve those inequalities.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- A concrete strictly positive lifespan for the unit path ball. -/
def quadraticBUCLifespan (β : ℝ≥0) (u₀ : BUC) : ℝ≥0 :=
  1 / (2 * (quadraticBUCBallBound β u₀ 1 +
    quadraticBUCBallLipschitzConstant β u₀ 1 + 1))

theorem quadraticBUCLifespan_pos (β : ℝ≥0) (u₀ : BUC) :
    0 < quadraticBUCLifespan β u₀ := by
  simp only [quadraticBUCLifespan]
  positivity

/-- The chosen lifespan maps the unit path ball to itself. -/
theorem quadraticBUCLifespan_mul_bound_le_one (β : ℝ≥0) (u₀ : BUC) :
    (quadraticBUCLifespan β u₀ : ℝ) *
        (quadraticBUCBallBound β u₀ 1 : ℝ) ≤ 1 := by
  let A := (quadraticBUCBallBound β u₀ 1 : ℝ)
  let L := (quadraticBUCBallLipschitzConstant β u₀ 1 : ℝ)
  have hA : 0 ≤ A := quadraticBUCBallBound β u₀ 1 |>.property
  have hL : 0 ≤ L := quadraticBUCBallLipschitzConstant β u₀ 1 |>.property
  have hD : 0 < 2 * (A + L + 1) := by positivity
  change (1 / (2 * (A + L + 1))) * A ≤ 1
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hD]
  nlinarith

/-- The chosen lifespan makes the local quadratic Lipschitz factor strictly
contractive. -/
theorem quadraticBUCLifespan_mul_lipschitz_lt_one (β : ℝ≥0) (u₀ : BUC) :
    quadraticBUCLifespan β u₀ *
        quadraticBUCBallLipschitzConstant β u₀ 1 < 1 := by
  rw [← NNReal.coe_lt_coe]
  let A := (quadraticBUCBallBound β u₀ 1 : ℝ)
  let L := (quadraticBUCBallLipschitzConstant β u₀ 1 : ℝ)
  have hA : 0 ≤ A := quadraticBUCBallBound β u₀ 1 |>.property
  have hL : 0 ≤ L := quadraticBUCBallLipschitzConstant β u₀ 1 |>.property
  have hD : 0 < 2 * (A + L + 1) := by positivity
  change (1 / (2 * (A + L + 1))) * L < 1
  rw [one_div, inv_mul_eq_div, div_lt_iff₀ hD]
  nlinarith

/-- Every bounded bilinear intrinsic heat-propagated Volterra nonlinearity has
a unique fixed point on an explicit positive time interval. -/
theorem exists_positive_time_heatDuhamelBUCIntrinsic_quadratic_fixedPoint
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) (u₀ : BUC) :
    ∃ T : ℝ≥0, 0 < T ∧
      ∃ u ∈ Metric.closedBall (constantDuhamelPathGeneric T u₀) (1 : ℝ),
        heatDuhamelBUCIntrinsicPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) u = u ∧
        ∀ v ∈ Metric.closedBall (constantDuhamelPathGeneric T u₀) (1 : ℝ),
          heatDuhamelBUCIntrinsicPicard T u₀ (quadraticOfCLM B)
              (continuous_quadraticOfCLM B) v = v → v = u := by
  let T := quadraticBUCLifespan β u₀
  refine ⟨T, quadraticBUCLifespan_pos β u₀, ?_⟩
  exact exists_heatDuhamelBUCIntrinsic_quadratic_fixedPoint_mem_closedBall
    T B β hB u₀ 1
    (quadraticBUCLifespan_mul_bound_le_one β u₀)
    (quadraticBUCLifespan_mul_lipschitz_lt_one β u₀)

end Poincare
