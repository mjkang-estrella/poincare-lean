import Poincare.Global.SemilinearHeatBUCRestart
import Poincare.Global.QuadraticSemilinearHeatBUCUniform

/-!
# Local continuation for quadratic semilinear heat paths on `BUC`

Every quadratic mild solution defined on a closed interval has a positive-time
tail starting from its endpoint.  If the endpoint norm is bounded by `K`, the
tail length is the uniform lifespan depending only on `(β,K)`.  Consequently,
failure of that quantitative continuation forces the endpoint norm to exceed
`K`.

This is the honest closed-interval continuation alternative.  A traditional
maximal-lifespan blow-up theorem concerns a solution on a half-open interval
`[0,Tmax)` and additionally requires compatible restriction/gluing machinery;
that larger object is not assumed here.
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

/-- The right endpoint as an element of the Duhamel time interval. -/
def duhamelEndTime (T : ℝ≥0) : Set.Icc (0 : ℝ) (T : ℝ) :=
  ⟨(T : ℝ), ⟨T.property, le_rfl⟩⟩

@[simp]
theorem coe_duhamelEndTime (T : ℝ≥0) :
    ((duhamelEndTime T : Set.Icc (0 : ℝ) (T : ℝ)) : ℝ) = (T : ℝ) :=
  rfl

/-- A quadratic mild path is a fixed point of the corrected heat Picard map. -/
def IsQuadraticSemilinearHeatBUCMildPath
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC)
    (u₀ : BUC) (u : DuhamelPath T BUC) : Prop :=
  semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
    (continuous_quadraticOfCLM B) u = u

/-- A local continuation tail of prescribed length, based at the endpoint of
an existing path. -/
def HasQuadraticSemilinearHeatBUCLocalContinuation
    (T δ : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC)
    (u : DuhamelPath T BUC) : Prop :=
  ∃ v : DuhamelPath δ BUC,
    v (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ)) =
        u (duhamelEndTime T) ∧
      semilinearHeatBUCPicard δ (u (duhamelEndTime T))
        (quadraticOfCLM B) (continuous_quadraticOfCLM B) v = v

/-- The restart of an existing quadratic mild path at any intermediate time is
again a quadratic mild path based at the value at that time. -/
theorem quadraticSemilinearHeatBUCMildPath_restart
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsQuadraticSemilinearHeatBUCMildPath T B u₀ u)
    (a : Set.Icc (0 : ℝ) (T : ℝ)) :
    IsQuadraticSemilinearHeatBUCMildPath
      (remainingDuhamelTime T a) B (u a) (restartDuhamelPath T u a) := by
  exact semilinearHeatBUCFixedPoint_restart_isFixedPt
    (E := E) (F := F) T u₀ (quadraticOfCLM B)
    (continuous_quadraticOfCLM B) u hu a

/-- Quantitative endpoint continuation: if `‖u(T)‖ ≤ K`, a locally unique
quadratic tail exists on the common positive interval `T(β,K)` and stays in
the unit ball about the endpoint's homogeneous heat orbit. -/
theorem exists_quadraticSemilinearHeatBUCLocalContinuation_of_end_norm_le
    (T K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (_hu : IsQuadraticSemilinearHeatBUCMildPath T B u₀ u)
    (hend : ‖u (duhamelEndTime T)‖ ≤ (K : ℝ)) :
    let δ := quadraticBUCUniformLifespan β K
    0 < δ ∧
      ∃ v ∈ Metric.closedBall
          (heatLinearBUCPath δ (u (duhamelEndTime T))) (1 : ℝ),
        v (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ)) =
            u (duhamelEndTime T) ∧
          semilinearHeatBUCPicard δ (u (duhamelEndTime T))
              (quadraticOfCLM B) (continuous_quadraticOfCLM B) v = v ∧
          ∀ w ∈ Metric.closedBall
              (heatLinearBUCPath δ (u (duhamelEndTime T))) (1 : ℝ),
            semilinearHeatBUCPicard δ (u (duhamelEndTime T))
                (quadraticOfCLM B) (continuous_quadraticOfCLM B) w = w →
              w = v := by
  dsimp only
  refine ⟨quadraticBUCUniformLifespan_pos β K, ?_⟩
  rcases exists_semilinearHeatBUC_quadratic_fixedPoint_uniform
      (E := E) (F := F) (quadraticBUCUniformLifespan β K) K 1 B β hB
      (u (duhamelEndTime T)) hend
      (quadraticBUCUniformLifespan_mul_bound_le_one β K)
      (quadraticBUCUniformLifespan_mul_lipschitz_lt_one β K) with
    ⟨v, hvBall, hv, huniq⟩
  refine ⟨v, hvBall, ?_, hv, huniq⟩
  have hv0 := congrArg
    (fun w : DuhamelPath (quadraticBUCUniformLifespan β K) BUC ↦
      w (⟨0, ⟨le_rfl, (quadraticBUCUniformLifespan β K).property⟩⟩ :
        Set.Icc (0 : ℝ) (quadraticBUCUniformLifespan β K : ℝ))) hv
  simpa using hv0.symm

/-- The quantitative tail above witnesses the prescribed-length continuation
predicate. -/
theorem has_quadraticSemilinearHeatBUCLocalContinuation_of_end_norm_le
    (T K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsQuadraticSemilinearHeatBUCMildPath T B u₀ u)
    (hend : ‖u (duhamelEndTime T)‖ ≤ (K : ℝ)) :
    HasQuadraticSemilinearHeatBUCLocalContinuation
      T (quadraticBUCUniformLifespan β K) B u := by
  rcases (exists_quadraticSemilinearHeatBUCLocalContinuation_of_end_norm_le
      (E := E) (F := F) T K B β hB u₀ u hu hend).2 with
    ⟨v, _hvBall, hv0, hv, _huniq⟩
  exact ⟨v, hv0, hv⟩

/-- Endpoint continuation alternative: failure of the uniform continuation
of length `T(β,K)` forces the endpoint norm to be larger than `K`. -/
theorem end_norm_gt_of_not_has_quadraticSemilinearHeatBUCLocalContinuation
    (T K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsQuadraticSemilinearHeatBUCMildPath T B u₀ u)
    (hno : ¬ HasQuadraticSemilinearHeatBUCLocalContinuation
      T (quadraticBUCUniformLifespan β K) B u) :
    (K : ℝ) < ‖u (duhamelEndTime T)‖ := by
  apply lt_of_not_ge
  intro hend
  exact hno
    (has_quadraticSemilinearHeatBUCLocalContinuation_of_end_norm_le
      (E := E) (F := F) T K B β hB u₀ u hu hend)

/-- A closed-interval quadratic mild path always has some positive local
continuation tail at its endpoint. -/
theorem exists_positive_quadraticSemilinearHeatBUCLocalContinuation
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsQuadraticSemilinearHeatBUCMildPath T B u₀ u) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      HasQuadraticSemilinearHeatBUCLocalContinuation T δ B u := by
  let K : ℝ≥0 := ⟨‖u (duhamelEndTime T)‖, norm_nonneg _⟩
  let δ := quadraticBUCUniformLifespan β K
  refine ⟨δ, quadraticBUCUniformLifespan_pos β K, ?_⟩
  apply has_quadraticSemilinearHeatBUCLocalContinuation_of_end_norm_le
    (E := E) (F := F) T K B β hB u₀ u hu
  exact le_rfl

/-- Thus no solution represented on a closed finite interval can be maximal
in the endpoint sense of admitting no positive continuation tail. -/
theorem not_forall_no_quadraticSemilinearHeatBUCLocalContinuation
    (T : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsQuadraticSemilinearHeatBUCMildPath T B u₀ u) :
    ¬ ∀ δ : ℝ≥0, 0 < δ →
      ¬ HasQuadraticSemilinearHeatBUCLocalContinuation T δ B u := by
  rintro hmax
  rcases exists_positive_quadraticSemilinearHeatBUCLocalContinuation
    (E := E) (F := F) T B β hB u₀ u hu with ⟨δ, hδ, hcont⟩
  exact hmax δ hδ hcont

end Poincare
