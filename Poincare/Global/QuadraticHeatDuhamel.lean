import Poincare.Global.DuhamelLocalContraction
import Poincare.Global.QuadraticNonlinearity
import Poincare.Global.HeatDuhamelBUCIntrinsic

/-!
# Local intrinsic heat-propagated Volterra solutions for quadratic nonlinearities

This instantiates the constant-linear-term intrinsic `BUC` Picard theory with
`N(u) = B(u,u)`.  Unlike the global Lipschitz theorem, the resulting fixed
point uses only the natural quadratic bounds on a prescribed ball around the
initial datum.  It is not claimed to solve the semilinear heat equation,
whose mild formula instead begins with `H_t u₀`.
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

/-- Local Lipschitz constant for `u ↦ B u u` on the radius-`R` ball at `u₀`. -/
def quadraticBUCBallLipschitzConstant
    (β : ℝ≥0) (u₀ : BUC) (R : ℝ≥0) : ℝ≥0 :=
  ⟨2 * (β : ℝ) * (‖u₀‖ + (R : ℝ)), by positivity⟩

/-- Uniform bound for `u ↦ B u u` on the same ball. -/
def quadraticBUCBallBound
    (β : ℝ≥0) (u₀ : BUC) (R : ℝ≥0) : ℝ≥0 :=
  ⟨(β : ℝ) * (‖u₀‖ + (R : ℝ)) ^ 2, by positivity⟩

/-- A diagonal bounded bilinear map is continuous. -/
theorem continuous_quadraticOfCLM
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) :
    Continuous (quadraticOfCLM B) := by
  exact B.continuous.clm_apply continuous_id

/-- A supplied bilinear operator bound gives the corresponding quadratic
bound without requiring an operator norm on the iterated `BUC` map space. -/
theorem norm_quadraticOfCLM_le_of_bound
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) (x : BUC) :
    ‖quadraticOfCLM B x‖ ≤ (β : ℝ) * ‖x‖ ^ 2 := by
  calc
    ‖quadraticOfCLM B x‖ = ‖B x x‖ := rfl
    _ ≤ ‖B x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((β : ℝ) * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (hB x) (norm_nonneg x)
    _ = (β : ℝ) * ‖x‖ ^ 2 := by ring

/-- Local Lipschitz estimate on a `BUC` ball from an explicit bilinear bound. -/
theorem lipschitzOnWith_quadraticOfCLM_closedBall_center_of_bound
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (R : ℝ≥0) :
    LipschitzOnWith (quadraticBUCBallLipschitzConstant β u₀ R)
      (quadraticOfCLM B) (Metric.closedBall u₀ (R : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm, quadraticOfCLM_sub]
  have hxR := norm_le_center_add_nnreal_radius u₀ R hx
  have hyR := norm_le_center_add_nnreal_radius u₀ R hy
  calc
    ‖B (x - y) x + B y (x - y)‖
        ≤ ‖B (x - y) x‖ + ‖B y (x - y)‖ := norm_add_le _ _
    _ ≤ (((β : ℝ) * ‖x - y‖) * ‖x‖) +
        (((β : ℝ) * ‖y‖) * ‖x - y‖) := by
      apply add_le_add
      · exact (ContinuousLinearMap.le_opNorm (B (x - y)) x).trans
          (mul_le_mul_of_nonneg_right (hB (x - y)) (norm_nonneg x))
      · exact (ContinuousLinearMap.le_opNorm (B y) (x - y)).trans
          (mul_le_mul_of_nonneg_right (hB y) (norm_nonneg (x - y)))
    _ ≤ (((β : ℝ) * ‖x - y‖) * (‖u₀‖ + (R : ℝ))) +
        (((β : ℝ) * (‖u₀‖ + (R : ℝ))) * ‖x - y‖) := by
      gcongr
    _ = (quadraticBUCBallLipschitzConstant β u₀ R : ℝ) * ‖x - y‖ := by
      change
        ((β : ℝ) * ‖x - y‖) * (‖u₀‖ + (R : ℝ)) +
            ((β : ℝ) * (‖u₀‖ + (R : ℝ))) * ‖x - y‖ =
          (2 * (β : ℝ) * (‖u₀‖ + (R : ℝ))) * ‖x - y‖
      ring

/-- On a path ball, the intrinsic quadratic Picard map stays within `T` times
the local quadratic bound of the initial constant path. -/
theorem dist_heatDuhamelBUCIntrinsicPicard_quadratic_le
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) (u₀ : BUC) (R : ℝ≥0)
    (u : DuhamelPath T BUC)
    (hu : u ∈ Metric.closedBall (constantDuhamelPathGeneric T u₀) (R : ℝ)) :
    dist
      (heatDuhamelBUCIntrinsicPicard T u₀ (quadraticOfCLM B)
        (continuous_quadraticOfCLM B) u)
      (constantDuhamelPathGeneric T u₀) ≤
        (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) := by
  apply (ContinuousMap.dist_le
    (mul_nonneg T.property (quadraticBUCBallBound β u₀ R).property)).mpr
  intro t
  rw [dist_eq_norm]
  change ‖u₀ + (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (quadraticOfCLM B
          (u (Set.projIcc 0 (T : ℝ) T.property s)))) - u₀‖ ≤ _
  rw [add_sub_cancel_left]
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (quadraticOfCLM B
          (u (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤
        (quadraticBUCBallBound β u₀ R : ℝ) := by
    intro s _hs
    let p : Set.Icc (0 : ℝ) (T : ℝ) :=
      Set.projIcc 0 (T : ℝ) T.property s
    have hup : u p ∈ Metric.closedBall u₀ (R : ℝ) :=
      eval_mem_closedBall_of_path_mem_closedBall T u₀ hu p
    have huNorm := norm_le_center_add_nnreal_radius u₀ R hup
    have hquad := (norm_quadraticOfCLM_le_of_bound B β hB (u p)).trans
      (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg (u p)) (by positivity)).2 huNorm) β.property)
    calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (quadraticOfCLM B (u p))‖
          ≤ ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)‖ *
              ‖quadraticOfCLM B (u p)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (quadraticBUCBallBound β u₀ R : ℝ) :=
        mul_le_mul
          (norm_vectorHeatSemigroupBUCExtended_le_one
            (E := E) (F := F) ((t : ℝ) - s))
          hquad (norm_nonneg _) zero_le_one
      _ = (quadraticBUCBallBound β u₀ R : ℝ) := one_mul _
  calc
    ‖∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (quadraticOfCLM B
            (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
        ≤ (quadraticBUCBallBound β u₀ R : ℝ) * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (quadraticBUCBallBound β u₀ R : ℝ) * (t : ℝ) := by
      rw [sub_zero, abs_of_nonneg t.property.1]
    _ ≤ (quadraticBUCBallBound β u₀ R : ℝ) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left t.property.2 (quadraticBUCBallBound β u₀ R).property
    _ = (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) := mul_comm _ _

/-- The quadratic intrinsic Picard map preserves the chosen path ball under
the explicit `T B_R ≤ R` condition. -/
theorem heatDuhamelBUCIntrinsicPicard_quadratic_mapsTo_closedBall
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) (u₀ : BUC) (R : ℝ≥0)
    (hmap : (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) ≤ (R : ℝ)) :
    MapsTo
      (heatDuhamelBUCIntrinsicPicard T u₀ (quadraticOfCLM B)
        (continuous_quadraticOfCLM B))
      (Metric.closedBall (constantDuhamelPathGeneric T u₀) (R : ℝ))
      (Metric.closedBall (constantDuhamelPathGeneric T u₀) (R : ℝ)) := by
  intro u hu
  exact (dist_heatDuhamelBUCIntrinsicPicard_quadratic_le
    T B β hB u₀ R u hu).trans hmap

/-- Explicit local fixed point for the quadratic heat-propagated Volterra map. -/
theorem exists_heatDuhamelBUCIntrinsic_quadratic_fixedPoint_mem_closedBall
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) (u₀ : BUC) (R : ℝ≥0)
    (hmap : (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) ≤ (R : ℝ))
    (hsmall : T * quadraticBUCBallLipschitzConstant β u₀ R < 1) :
    ∃ u ∈ Metric.closedBall (constantDuhamelPathGeneric T u₀) (R : ℝ),
      heatDuhamelBUCIntrinsicPicard T u₀ (quadraticOfCLM B)
          (continuous_quadraticOfCLM B) u = u ∧
      ∀ v ∈ Metric.closedBall (constantDuhamelPathGeneric T u₀) (R : ℝ),
        heatDuhamelBUCIntrinsicPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) v = v → v = u := by
  let L := quadraticBUCBallLipschitzConstant β u₀ R
  let Φ := heatDuhamelBUCIntrinsicPicard T u₀ (quadraticOfCLM B)
    (continuous_quadraticOfCLM B)
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply exists_fixedPoint_mem_closedBall_of_pointwise_contraction
    (X := BUC)
    (q := T * L) Φ
    (constantDuhamelPathGeneric T u₀) R.property
  · exact heatDuhamelBUCIntrinsicPicard_quadratic_mapsTo_closedBall
      T B β hB u₀ R hmap
  · intro u v hu hv t
    change ‖Φ u t - Φ v t‖ ≤ ((T * L : ℝ≥0) : ℝ) * ‖u - v‖
    rw [heatDuhamelBUCIntrinsicPicard_sub_eq_projectedDuhamelDifference
      (E := E) (F := F) T u₀ (quadraticOfCLM B)
      (continuous_quadraticOfCLM B) u v t]
    have hlocal :=
      lipschitzOnWith_quadraticOfCLM_closedBall_center_of_bound B β hB u₀ R
    have hbound :=
      norm_projectedDuhamelDifference_le_of_lipschitzOn_closedBall
        T 1 L (vectorHeatSemigroupBUCExtended (E := E) (F := F))
        (quadraticOfCLM B) u₀
        (fun r _hr ↦ norm_vectorHeatSemigroupBUCExtended_le_one
          (E := E) (F := F) r)
        hlocal u v hu hv t
    simpa [L] using hbound
  · simpa [L] using hsmall

end Poincare
