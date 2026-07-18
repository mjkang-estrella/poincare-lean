import Poincare.Global.HeatDuhamelBUCIntrinsic
import Poincare.Global.HeatSemigroupBUCC0

/-!
# Correct semilinear heat mild solutions on `BUC`

For `u' = A u + N(u)`, the mild formula is

`u(t) = H_t u₀ + ∫₀ᵗ H_(t-s) N(u(s)) ds`.

The earlier constant-basepoint Volterra map is useful as an abstract integral
equation, but it omits the linear orbit `H_t u₀`.  This module supplies the
actual semilinear heat Picard map intrinsically on the complete `BUC` space.
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

/-- The homogeneous heat orbit through the initial datum. -/
def heatLinearBUCPath (T : ℝ≥0) (u₀ : BUC) : DuhamelPath T BUC where
  toFun t := vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀
  continuous_toFun :=
    (continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) u₀).comp
      continuous_subtype_val

@[simp]
theorem heatLinearBUCPath_apply (T : ℝ≥0) (u₀ : BUC)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatLinearBUCPath T u₀ t =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ :=
  rfl

@[simp]
theorem heatLinearBUCPath_zero (T : ℝ≥0) (u₀ : BUC) :
    heatLinearBUCPath T u₀
      (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) = u₀ := by
  simp [heatLinearBUCPath, vectorHeatSemigroupBUCExtended]

/-- Correct semilinear heat Picard map: homogeneous heat orbit plus Duhamel
forcing. -/
def semilinearHeatBUCPicard
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC) : DuhamelPath T BUC :=
  heatDuhamelBUCIntrinsicPicard T u₀ N hN u +
    heatLinearBUCPath T u₀ - constantDuhamelBUCIntrinsicPath T u₀

@[simp]
theorem semilinearHeatBUCPicard_apply
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    semilinearHeatBUCPicard T u₀ N hN u t =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
  change
    (u₀ + (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s))))) +
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ - u₀ = _
  abel

/-- Differences of corrected semilinear iterates still have the same projected
Duhamel form, since the homogeneous heat orbit is independent of the iterate. -/
theorem semilinearHeatBUCPicard_sub_eq_projectedDuhamelDifference
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u v : DuhamelPath T BUC) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    semilinearHeatBUCPicard T u₀ N hN u t -
        semilinearHeatBUCPicard T u₀ N hN v t =
      projectedDuhamelDifference T
        (vectorHeatSemigroupBUCExtended (E := E) (F := F)) N u v t := by
  change
    (heatDuhamelBUCIntrinsicPicard T u₀ N hN u t +
        heatLinearBUCPath T u₀ t - u₀) -
      (heatDuhamelBUCIntrinsicPicard T u₀ N hN v t +
        heatLinearBUCPath T u₀ t - u₀) = _
  rw [show
      (heatDuhamelBUCIntrinsicPicard T u₀ N hN u t +
          heatLinearBUCPath T u₀ t - u₀) -
        (heatDuhamelBUCIntrinsicPicard T u₀ N hN v t +
          heatLinearBUCPath T u₀ t - u₀) =
        heatDuhamelBUCIntrinsicPicard T u₀ N hN u t -
          heatDuhamelBUCIntrinsicPicard T u₀ N hN v t by abel]
  exact heatDuhamelBUCIntrinsicPicard_sub_eq_projectedDuhamelDifference
    (E := E) (F := F) T u₀ N hN u v t

/-- Corrected semilinear heat Picard contraction. -/
theorem semilinearHeatBUCPicard_contractingWith
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ContractingWith (T * L)
      (semilinearHeatBUCPicard T u₀ N hN.continuous) := by
  have h := contractingWith_of_projectedDuhamelDifference
    (X := BUC) T 1 L
    (vectorHeatSemigroupBUCExtended (E := E) (F := F)) N
    (fun r _hr ↦ norm_vectorHeatSemigroupBUCExtended_le_one
      (E := E) (F := F) r)
    hN (semilinearHeatBUCPicard T u₀ N hN.continuous)
    (semilinearHeatBUCPicard_sub_eq_projectedDuhamelDifference
      T u₀ N hN.continuous)
    (by simpa using hsmall)
  simpa using h

/-- Unique fixed point of the corrected semilinear heat Picard map. -/
theorem exists_unique_semilinearHeatBUCPicard_fixedPoint
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ∃! u : DuhamelPath T BUC,
      semilinearHeatBUCPicard T u₀ N hN.continuous u = u := by
  have hc := semilinearHeatBUCPicard_contractingWith
    (E := E) (F := F) T L u₀ N hN hsmall
  let u := hc.fixedPoint (semilinearHeatBUCPicard T u₀ N hN.continuous)
  refine ⟨u, hc.fixedPoint_isFixedPt, ?_⟩
  intro v hv
  exact hc.fixedPoint_unique' hv hc.fixedPoint_isFixedPt

/-- Unique corrected semilinear heat mild solution. -/
theorem exists_unique_semilinearHeatBUC_mildSolution
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ∃! u : DuhamelPath T BUC,
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) = u₀ ∧
      ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
        u t = vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
          ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
            vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
              (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
  rcases exists_unique_semilinearHeatBUCPicard_fixedPoint
    (E := E) (F := F) T L u₀ N hN hsmall with ⟨u, hu, huniq⟩
  have hmild : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      u t = vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
    intro t
    have ht := congrArg (fun w : DuhamelPath T BUC ↦ w t) hu
    simpa using ht.symm
  refine ⟨u, ⟨?_, hmild⟩, ?_⟩
  · simpa using hmild
      (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))
  · intro v hv
    apply huniq v
    apply ContinuousMap.ext
    intro t
    simpa using (hv.2 t).symm

/-- Canonical corrected semilinear heat mild solution. -/
noncomputable def semilinearHeatBUCSolution
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    DuhamelPath T BUC :=
  Classical.choose
    (exists_unique_semilinearHeatBUCPicard_fixedPoint
      (E := E) (F := F) T L u₀ N hN hsmall)

/-- The canonical corrected solution is a fixed point. -/
theorem semilinearHeatBUCSolution_isFixedPt
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    semilinearHeatBUCPicard T u₀ N hN.continuous
        (semilinearHeatBUCSolution T L u₀ N hN hsmall) =
      semilinearHeatBUCSolution T L u₀ N hN hsmall :=
  (Classical.choose_spec
    (exists_unique_semilinearHeatBUCPicard_fixedPoint
      (E := E) (F := F) T L u₀ N hN hsmall)).1

/-- Exact corrected mild formula for the canonical solution. -/
theorem semilinearHeatBUCSolution_mild
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    semilinearHeatBUCSolution T L u₀ N hN hsmall t =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (N (semilinearHeatBUCSolution T L u₀ N hN hsmall
              (Set.projIcc 0 (T : ℝ) T.property s))) := by
  have h := congrArg (fun w : DuhamelPath T BUC ↦ w t)
    (semilinearHeatBUCSolution_isFixedPt
      (E := E) (F := F) T L u₀ N hN hsmall)
  simpa using h.symm

@[simp]
theorem semilinearHeatBUCSolution_zero
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    semilinearHeatBUCSolution T L u₀ N hN hsmall
      (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) = u₀ := by
  simpa using semilinearHeatBUCSolution_mild
    (E := E) (F := F) T L u₀ N hN hsmall
      (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))

/-- Every extended heat operator is nonexpanding in the intrinsic `BUC`
metric. -/
theorem dist_vectorHeatSemigroupBUCExtended_apply_le
    (t : ℝ) (f g : BUC) :
    dist (vectorHeatSemigroupBUCExtended (E := E) (F := F) t f)
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) t g) ≤ dist f g := by
  by_cases ht : 0 < t
  · rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simp only [vectorHeatSemigroupBUCExtended, dif_pos ht]
    change ‖vectorHeatSemigroupBUCLM (E := E) (F := F) ht f -
        vectorHeatSemigroupBUCLM (E := E) (F := F) ht g‖ ≤ ‖f - g‖
    rw [← (vectorHeatSemigroupBUCLM (E := E) (F := F) ht).map_sub]
    calc
      ‖vectorHeatSemigroupBUCLM (E := E) (F := F) ht (f - g)‖
          ≤ ‖vectorHeatSemigroupBUCLM (E := E) (F := F) ht‖ * ‖f - g‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f - g‖ := mul_le_mul_of_nonneg_right
        (norm_vectorHeatSemigroupBUCLM_le_one (E := E) (F := F) ht)
        (norm_nonneg _)
      _ = ‖f - g‖ := one_mul _
  · simp [vectorHeatSemigroupBUCExtended, ht]

/-- Quantitative dependence of corrected semilinear heat fixed points on the
initial datum. -/
theorem dist_semilinearHeatBUC_fixedPoints_le
    (T L : ℝ≥0) (u₀ v₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1)
    (u v : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN.continuous u = u)
    (hv : semilinearHeatBUCPicard T v₀ N hN.continuous v = v) :
    dist u v ≤ (1 - (((T * L : ℝ≥0) : ℝ)))⁻¹ * dist u₀ v₀ := by
  let Φu := semilinearHeatBUCPicard T u₀ N hN.continuous
  let Φv := semilinearHeatBUCPicard T v₀ N hN.continuous
  have hc := semilinearHeatBUCPicard_contractingWith
    (E := E) (F := F) T L u₀ N hN hsmall
  have hlip : LipschitzWith (T * L) Φu := by simpa [Φu] using hc.2
  have hshift : dist (Φu v) (Φv v) ≤ dist u₀ v₀ := by
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro t
    simp only [Φu, Φv, semilinearHeatBUCPicard_apply]
    rw [dist_add_right]
    exact dist_vectorHeatSemigroupBUCExtended_apply_le
      (E := E) (F := F) (t : ℝ) u₀ v₀
  have htotal : dist u v ≤
      (((T * L : ℝ≥0) : ℝ)) * dist u v + dist u₀ v₀ := by
    calc
      dist u v = dist (Φu u) (Φv v) := by
        simp only [Φu, Φv]
        rw [hu, hv]
      _ ≤ dist (Φu u) (Φu v) + dist (Φu v) (Φv v) := dist_triangle _ _ _
      _ ≤ (((T * L : ℝ≥0) : ℝ)) * dist u v + dist u₀ v₀ :=
        add_le_add (hlip.dist_le_mul u v) hshift
  have hq : (((T * L : ℝ≥0) : ℝ)) < 1 := by exact_mod_cast hsmall
  have hden : 0 < 1 - (((T * L : ℝ≥0) : ℝ)) := sub_pos.mpr hq
  rw [le_inv_mul_iff₀ hden]
  nlinarith

/-- The corrected canonical solution operator is Lipschitz in its initial
datum with constant `(1 - T L)⁻¹`. -/
theorem lipschitzWith_semilinearHeatBUCSolution
    (T L : ℝ≥0) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    LipschitzWith (heatDuhamelBUCIntrinsicStabilityConstant T L hsmall)
      (fun u₀ : BUC ↦ semilinearHeatBUCSolution T L u₀ N hN hsmall) := by
  apply LipschitzWith.of_dist_le_mul
  intro u₀ v₀
  have h := dist_semilinearHeatBUC_fixedPoints_le
    (E := E) (F := F) T L u₀ v₀ N hN hsmall
    (semilinearHeatBUCSolution T L u₀ N hN hsmall)
    (semilinearHeatBUCSolution T L v₀ N hN hsmall)
    (semilinearHeatBUCSolution_isFixedPt
      (E := E) (F := F) T L u₀ N hN hsmall)
    (semilinearHeatBUCSolution_isFixedPt
      (E := E) (F := F) T L v₀ N hN hsmall)
  simpa [heatDuhamelBUCIntrinsicStabilityConstant] using h

end Poincare
