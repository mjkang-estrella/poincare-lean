import Poincare.Global.SemilinearHeatBUCRestrictionGluing
import Poincare.Global.SemilinearHeatBUCLocalUniform

/-!
# Local continuation for locally Lipschitz semilinear heat paths

The bounded-ball moduli give an explicit continuation interval at the endpoint
of every closed mild path.  This is the closed-interval counterpart of the
maximal compatible-family blow-up theorem.
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

/-- A mild path for an arbitrary continuous `BUC` nonlinearity. -/
def IsSemilinearHeatBUCMildPath
    (T : ℝ≥0) (N : BUC → BUC) (hN : Continuous N)
    (u₀ : BUC) (u : DuhamelPath T BUC) : Prop :=
  semilinearHeatBUCPicard T u₀ N hN u = u

/-- A prescribed-length local continuation tail based at the endpoint of an
existing path. -/
def HasSemilinearHeatBUCLocalContinuation
    (T δ : ℝ≥0) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC) : Prop :=
  ∃ v : DuhamelPath δ BUC,
    v (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ)) =
        u (compactDuhamelEndTime T) ∧
      semilinearHeatBUCPicard δ (u (compactDuhamelEndTime T)) N hN v = v

/-- Restarting a mild path at an intermediate time produces a mild path
based at the attained value. -/
theorem semilinearHeatBUCMildPath_restart
    (T : ℝ≥0) (N : BUC → BUC) (hN : Continuous N)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsSemilinearHeatBUCMildPath T N hN u₀ u)
    (a : Set.Icc (0 : ℝ) (T : ℝ)) :
    IsSemilinearHeatBUCMildPath (remainingDuhamelTime T a) N hN
      (u a) (restartDuhamelPath T u a) := by
  exact semilinearHeatBUCFixedPoint_restart_isFixedPt
    (E := E) (F := F) T u₀ N hN u hu a

/-- Quantitative endpoint continuation under an endpoint norm bound. -/
theorem exists_semilinearHeatBUCLocalContinuation_of_end_norm_le
    (T K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (_hu : IsSemilinearHeatBUCMildPath T N data.continuous u₀ u)
    (hend : ‖u (compactDuhamelEndTime T)‖ ≤ (K : ℝ)) :
    let δ := semilinearHeatBUCUniformLifespan data K
    0 < δ ∧
      ∃ v ∈ Metric.closedBall
          (heatLinearBUCPath δ (u (compactDuhamelEndTime T))) (1 : ℝ),
        v (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ)) =
            u (compactDuhamelEndTime T) ∧
          semilinearHeatBUCPicard δ (u (compactDuhamelEndTime T)) N
              data.continuous v = v ∧
          ∀ w ∈ Metric.closedBall
              (heatLinearBUCPath δ (u (compactDuhamelEndTime T))) (1 : ℝ),
            semilinearHeatBUCPicard δ (u (compactDuhamelEndTime T)) N
                data.continuous w = w → w = v := by
  dsimp only
  refine ⟨semilinearHeatBUCUniformLifespan_pos data K, ?_⟩
  rcases exists_semilinearHeatBUC_fixedPoint_uniform_local
      (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K) K 1
      N data (u (compactDuhamelEndTime T)) hend
      (semilinearHeatBUCUniformLifespan_mul_bound_le_one data K)
      (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one data K) with
    ⟨v, hvBall, hv, huniq⟩
  refine ⟨v, hvBall, ?_, hv, huniq⟩
  have hv0 := congrArg
    (fun w : DuhamelPath (semilinearHeatBUCUniformLifespan data K) BUC ↦
      w (⟨0, ⟨le_rfl, (semilinearHeatBUCUniformLifespan data K).property⟩⟩ :
        Set.Icc (0 : ℝ) (semilinearHeatBUCUniformLifespan data K : ℝ))) hv
  simpa using hv0.symm

/-- The endpoint estimate supplies the prescribed continuation predicate. -/
theorem has_semilinearHeatBUCLocalContinuation_of_end_norm_le
    (T K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsSemilinearHeatBUCMildPath T N data.continuous u₀ u)
    (hend : ‖u (compactDuhamelEndTime T)‖ ≤ (K : ℝ)) :
    HasSemilinearHeatBUCLocalContinuation T
      (semilinearHeatBUCUniformLifespan data K) N data.continuous u := by
  rcases (exists_semilinearHeatBUCLocalContinuation_of_end_norm_le
      (E := E) (F := F) T K N data u₀ u hu hend).2 with
    ⟨v, _hvBall, hv0, hv, _huniq⟩
  exact ⟨v, hv0, hv⟩

/-- Failure of the uniform continuation length forces the endpoint norm above
the proposed bound. -/
theorem end_norm_gt_of_not_has_semilinearHeatBUCLocalContinuation
    (T K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsSemilinearHeatBUCMildPath T N data.continuous u₀ u)
    (hno : ¬ HasSemilinearHeatBUCLocalContinuation T
      (semilinearHeatBUCUniformLifespan data K) N data.continuous u) :
    (K : ℝ) < ‖u (compactDuhamelEndTime T)‖ := by
  apply lt_of_not_ge
  intro hend
  exact hno (has_semilinearHeatBUCLocalContinuation_of_end_norm_le
    (E := E) (F := F) T K N data u₀ u hu hend)

/-- Every closed mild path has a positive local continuation. -/
theorem exists_positive_semilinearHeatBUCLocalContinuation
    (T : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsSemilinearHeatBUCMildPath T N data.continuous u₀ u) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      HasSemilinearHeatBUCLocalContinuation T δ N data.continuous u := by
  let K : ℝ≥0 := ⟨‖u (compactDuhamelEndTime T)‖, norm_nonneg _⟩
  let δ := semilinearHeatBUCUniformLifespan data K
  refine ⟨δ, semilinearHeatBUCUniformLifespan_pos data K, ?_⟩
  apply has_semilinearHeatBUCLocalContinuation_of_end_norm_le
    (E := E) (F := F) T K N data u₀ u hu
  exact le_rfl

/-- Hence a solution represented on a closed finite interval cannot be
endpoint-maximal. -/
theorem not_forall_no_semilinearHeatBUCLocalContinuation
    (T : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsSemilinearHeatBUCMildPath T N data.continuous u₀ u) :
    ¬ ∀ δ : ℝ≥0, 0 < δ →
      ¬ HasSemilinearHeatBUCLocalContinuation T δ N data.continuous u := by
  rintro hmax
  rcases exists_positive_semilinearHeatBUCLocalContinuation
    (E := E) (F := F) T N data u₀ u hu with ⟨δ, hδ, hcont⟩
  exact hmax δ hδ hcont

end Poincare
