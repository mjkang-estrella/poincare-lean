import Poincare.Global.SemilinearHeatBUC
import Poincare.Global.QuadraticHeatLocalExistence

/-!
# Correct local quadratic semilinear heat equation on `BUC`

This transfers the explicit quadratic ball estimates to the corrected mild
formula based at the homogeneous orbit `H_t u₀`.
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

/-- The homogeneous heat path is uniformly bounded by its initial datum. -/
theorem norm_heatLinearBUCPath_le (T : ℝ≥0) (u₀ : BUC) :
    ‖heatLinearBUCPath T u₀‖ ≤ ‖u₀‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  calc
    ‖heatLinearBUCPath T u₀ t‖
        ≤ ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ)‖ * ‖u₀‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖u₀‖ := mul_le_mul_of_nonneg_right
      (norm_vectorHeatSemigroupBUCExtended_le_one (E := E) (F := F) (t : ℝ))
      (norm_nonneg _)
    _ = ‖u₀‖ := one_mul _

/-- A path within `R` of the homogeneous orbit lies in the zero-centered path
ball of radius `‖u₀‖ + R`. -/
theorem mem_zero_ball_of_mem_heatLinearBUCPath_ball
    (T : ℝ≥0) (u₀ : BUC) (R : ℝ≥0) {u : DuhamelPath T BUC}
    (hu : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) :
    u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
      (‖u₀‖ + (R : ℝ)) := by
  rw [Metric.mem_closedBall] at hu ⊢
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  have horbit : dist (heatLinearBUCPath T u₀ t) (0 : BUC) ≤ ‖u₀‖ := by
    have hb : ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀‖ ≤ ‖u₀‖ := by
      calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀‖
          ≤ ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ)‖ * ‖u₀‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖u₀‖ := mul_le_mul_of_nonneg_right
        (norm_vectorHeatSemigroupBUCExtended_le_one (E := E) (F := F) (t : ℝ))
        (norm_nonneg _)
      _ = ‖u₀‖ := one_mul _
    rw [Subtype.dist_eq, dist_eq_norm]
    simpa [heatLinearBUCPath] using hb
  calc
    dist (u t) (constantDuhamelPathGeneric T (0 : BUC) t)
        = dist (u t) (0 : BUC) := rfl
    _ ≤ dist (u t) (heatLinearBUCPath T u₀ t) +
          dist (heatLinearBUCPath T u₀ t) 0 := dist_triangle _ _ _
    _ ≤ dist u (heatLinearBUCPath T u₀) + ‖u₀‖ :=
      add_le_add (ContinuousMap.dist_apply_le_dist t) horbit
    _ ≤ (R : ℝ) + ‖u₀‖ := add_le_add hu le_rfl
    _ = ‖u₀‖ + (R : ℝ) := add_comm _ _

/-- Corrected quadratic Picard iterates stay within `T B_R` of the homogeneous
heat orbit. -/
theorem dist_semilinearHeatBUCPicard_quadratic_heatLinearPath_le
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (R : ℝ≥0) (u : DuhamelPath T BUC)
    (hu : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) :
    dist
      (semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
        (continuous_quadraticOfCLM B) u)
      (heatLinearBUCPath T u₀) ≤
        (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) := by
  apply (ContinuousMap.dist_le
    (mul_nonneg T.property (quadraticBUCBallBound β u₀ R).property)).mpr
  intro t
  rw [semilinearHeatBUCPicard_apply, heatLinearBUCPath_apply, dist_eq_norm,
    add_sub_cancel_left]
  have hu0 := mem_zero_ball_of_mem_heatLinearBUCPath_ball
    (E := E) (F := F) T u₀ R hu
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (quadraticOfCLM B
          (u (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤
        (quadraticBUCBallBound β u₀ R : ℝ) := by
    intro s _hs
    let p : Set.Icc (0 : ℝ) (T : ℝ) :=
      Set.projIcc 0 (T : ℝ) T.property s
    have hup : u p ∈ Metric.closedBall (0 : BUC) (‖u₀‖ + (R : ℝ)) :=
      eval_mem_closedBall_of_path_mem_closedBall T (0 : BUC) hu0 p
    have huNorm : ‖u p‖ ≤ ‖u₀‖ + (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hup
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
      mul_le_mul_of_nonneg_left t.property.2
        (quadraticBUCBallBound β u₀ R).property
    _ = (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) := mul_comm _ _

/-- Ball preservation for the corrected quadratic semilinear heat map. -/
theorem semilinearHeatBUCPicard_quadratic_mapsTo_closedBall
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (R : ℝ≥0)
    (hmap : (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) ≤ (R : ℝ)) :
    MapsTo
      (semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
        (continuous_quadraticOfCLM B))
      (Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ))
      (Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) := by
  intro u hu
  exact (dist_semilinearHeatBUCPicard_quadratic_heatLinearPath_le
    T B β hB u₀ R u hu).trans hmap

/-- Corrected local fixed point for a quadratic semilinear heat equation. -/
theorem exists_semilinearHeatBUC_quadratic_fixedPoint_mem_closedBall
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (R : ℝ≥0)
    (hmap : (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) ≤ (R : ℝ))
    (hsmall : T * quadraticBUCBallLipschitzConstant β u₀ R < 1) :
    ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ),
      semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
          (continuous_quadraticOfCLM B) u = u ∧
      ∀ v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ),
        semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) v = v → v = u := by
  let L := quadraticBUCBallLipschitzConstant β u₀ R
  let Φ := semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
    (continuous_quadraticOfCLM B)
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply exists_fixedPoint_mem_closedBall_of_pointwise_contraction
    (X := BUC) (q := T * L) Φ (heatLinearBUCPath T u₀) R.property
  · exact semilinearHeatBUCPicard_quadratic_mapsTo_closedBall
      T B β hB u₀ R hmap
  · intro u v hu hv t
    change ‖Φ u t - Φ v t‖ ≤ ((T * L : ℝ≥0) : ℝ) * ‖u - v‖
    rw [semilinearHeatBUCPicard_sub_eq_projectedDuhamelDifference
      (E := E) (F := F) T u₀ (quadraticOfCLM B)
      (continuous_quadraticOfCLM B) u v t]
    have hu0 := mem_zero_ball_of_mem_heatLinearBUCPath_ball
      (E := E) (F := F) T u₀ R hu
    have hv0 := mem_zero_ball_of_mem_heatLinearBUCPath_ball
      (E := E) (F := F) T u₀ R hv
    let Q : ℝ≥0 := ⟨‖u₀‖ + (R : ℝ), by positivity⟩
    have hlocal :=
      lipschitzOnWith_quadraticOfCLM_closedBall_center_of_bound
        B β hB (0 : BUC) Q
    have hbound :=
      norm_projectedDuhamelDifference_le_of_lipschitzOn_closedBall
        T 1 L (vectorHeatSemigroupBUCExtended (E := E) (F := F))
        (quadraticOfCLM B) (0 : BUC)
        (fun r _hr ↦ norm_vectorHeatSemigroupBUCExtended_le_one
          (E := E) (F := F) r)
        (by simpa [L, Q, quadraticBUCBallLipschitzConstant] using hlocal)
        u v hu0 hv0 t
    simpa [L] using hbound
  · simpa [L] using hsmall

/-- Explicit positive lifespan for the corrected quadratic semilinear heat
equation on the unit orbit ball. -/
theorem exists_positive_time_semilinearHeatBUC_quadratic_fixedPoint
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) (u₀ : BUC) :
    ∃ T : ℝ≥0, 0 < T ∧
      ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
        semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) u = u ∧
        ∀ v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
          semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
              (continuous_quadraticOfCLM B) v = v → v = u := by
  let T := quadraticBUCLifespan β u₀
  refine ⟨T, quadraticBUCLifespan_pos β u₀, ?_⟩
  exact exists_semilinearHeatBUC_quadratic_fixedPoint_mem_closedBall
    T B β hB u₀ 1
    (quadraticBUCLifespan_mul_bound_le_one β u₀)
    (quadraticBUCLifespan_mul_lipschitz_lt_one β u₀)

end Poincare
