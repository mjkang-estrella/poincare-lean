import Poincare.Global.SemilinearHeatBUCRestart
import Poincare.Global.SemilinearHeatBUCFixedPointRegularity
import Poincare.Global.DeTurckBUCMetricReconstruction

/-!
# Right-sided interior regularity for semilinear heat fixed points

A fixed point on `[0,T]` restarts at every intermediate time `a`.  Applying
the already-proved zero-time derivative theorem to that restarted fixed point
identifies the exact derivative of the original mild path from the right:

`d⁺u/dt (a) = Au(a) + N(u(a))`.

The only analytic premise added at time `a` is one strong heat-generator graph
witness for the current state `u(a)`.  The conclusions in this file are
right-sided (`Ici a`, equivalently the germ of `[a,T]` at `a`).  No two-sided
interior differentiability is claimed.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction
  BigOperators

namespace Poincare

section FixedPointInteriorRegularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- On the right interval `[a,T]`, translating by `a` and projecting to the
remaining interval recovers the original projected path. -/
theorem restartDuhamelPath_proj_sub_eq
    (T : ℝ≥0) (u : DuhamelPath T BUC)
    (a : Set.Icc (0 : ℝ) (T : ℝ))
    (t : ℝ) (ht : t ∈ Set.Icc (a : ℝ) (T : ℝ)) :
    restartDuhamelPath T u a
        (Set.projIcc 0 (remainingDuhamelTime T a : ℝ)
          (remainingDuhamelTime T a).property (t - (a : ℝ))) =
      u (Set.projIcc 0 (T : ℝ) T.property t) := by
  have ht0 : 0 ≤ t := a.property.1.trans ht.1
  have hta0 : 0 ≤ t - (a : ℝ) := sub_nonneg.mpr ht.1
  have htaRemain : t - (a : ℝ) ≤ (remainingDuhamelTime T a : ℝ) := by
    simpa only [coe_remainingDuhamelTime] using
      sub_le_sub_right ht.2 (a : ℝ)
  have hprojRemain :
      Set.projIcc 0 (remainingDuhamelTime T a : ℝ)
          (remainingDuhamelTime T a).property (t - (a : ℝ)) =
        (⟨t - (a : ℝ), ⟨hta0, htaRemain⟩⟩ :
          Set.Icc (0 : ℝ) (remainingDuhamelTime T a : ℝ)) := by
    apply Subtype.ext
    simp only [Set.coe_projIcc, coe_remainingDuhamelTime] at htaRemain ⊢
    rw [min_eq_right htaRemain, max_eq_right hta0]
  have hprojT :
      Set.projIcc 0 (T : ℝ) T.property t =
        (⟨t, ⟨ht0, ht.2⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) := by
    apply Subtype.ext
    simp [Set.coe_projIcc, max_eq_right ht0, min_eq_right ht.2]
  rw [hprojRemain, hprojT, restartDuhamelPath_apply]
  congr 1
  apply Subtype.ext
  simp only [restartDuhamelTimeMap_coe]
  ring

/-- Exact derivative on the remaining compact right interval.  This form does
not need `a < T`; at `a = T` its derivative statement is relative to a
singleton and is therefore only a degenerate endpoint statement. -/
theorem semilinearHeatBUCFixedPoint_hasDerivWithinAt_rightInterval
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (a : Set.Icc (0 : ℝ) (T : ℝ))
    (Au : BUC)
    (hua : IsInBUCHeatGeneratorDomain (E := E) (F := F) (u a) Au) :
    HasDerivWithinAt
      (fun t : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property t))
      (Au + N (u a)) (Set.Icc (a : ℝ) (T : ℝ)) (a : ℝ) := by
  let R := remainingDuhamelTime T a
  let ur := restartDuhamelPath T u a
  have hfixed :
      semilinearHeatBUCPicard R (u a) N hN ur = ur := by
    simpa only [R, ur] using
      semilinearHeatBUCFixedPoint_restart_isFixedPt
        (E := E) (F := F) T u₀ N hN u hu a
  have hzero : HasDerivWithinAt
      (fun τ : ℝ ↦ ur (Set.projIcc 0 (R : ℝ) R.property τ))
      (Au + N (u a)) (Set.Icc 0 (R : ℝ)) 0 :=
    semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
      (E := E) (F := F) R (u a) Au N hN ur hfixed hua
  have hshift : HasDerivWithinAt
      (fun t : ℝ ↦ t - (a : ℝ)) 1
      (Set.Icc (a : ℝ) (T : ℝ)) (a : ℝ) :=
    ((hasDerivAt_id (a : ℝ)).sub_const (a : ℝ)).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun t : ℝ ↦ t - (a : ℝ))
      (Set.Icc (a : ℝ) (T : ℝ)) (Set.Icc 0 (R : ℝ)) := by
    intro t ht
    constructor
    · exact sub_nonneg.mpr ht.1
    · simpa only [R, coe_remainingDuhamelTime] using
        sub_le_sub_right ht.2 (a : ℝ)
  have htranslated : HasDerivWithinAt
      (fun t : ℝ ↦ ur
        (Set.projIcc 0 (R : ℝ) R.property (t - (a : ℝ))))
      (Au + N (u a)) (Set.Icc (a : ℝ) (T : ℝ)) (a : ℝ) := by
    simpa only [Function.comp_def, one_smul] using
      hzero.scomp_of_eq (a : ℝ) hshift hmaps (by ring)
  apply htranslated.congr
  · intro t ht
    exact (restartDuhamelPath_proj_sub_eq
      (E := E) (F := F) T u a t ht).symm
  · exact (restartDuhamelPath_proj_sub_eq
      (E := E) (F := F) T u a (a : ℝ) ⟨le_rfl, a.property.2⟩).symm

/-- Genuine right derivative at an intermediate time `a < T`.  The upper
endpoint of `[a,T]` is invisible to the germ at `a`, so the compact-interval
result is exactly a derivative within `Ici a`. -/
theorem semilinearHeatBUCFixedPoint_hasDerivWithinAt_interior_right
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (a : Set.Icc (0 : ℝ) (T : ℝ)) (ha : (a : ℝ) < (T : ℝ))
    (Au : BUC)
    (hua : IsInBUCHeatGeneratorDomain (E := E) (F := F) (u a) Au) :
    HasDerivWithinAt
      (fun t : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property t))
      (Au + N (u a)) (Set.Ici (a : ℝ)) (a : ℝ) := by
  have hright :=
    semilinearHeatBUCFixedPoint_hasDerivWithinAt_rightInterval
      (E := E) (F := F) T u₀ N hN u hu a Au hua
  simpa only [HasDerivWithinAt, nhdsWithin_Icc_eq_nhdsGE ha] using hright

end FixedPointInteriorRegularity

section AffineInteriorRegularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- The canonical affine fixed point has the exact right derivative at every
intermediate time where its current state has one heat-generator witness. -/
theorem uniformSolution_hasDerivWithinAt_interior_right
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (a : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ))
    (ha : (a : ℝ) < (D.uniformLifespan K : ℝ))
    (Au : BUC)
    (hua : IsInBUCHeatGeneratorDomain
      (E := E) (F := F) (D.uniformSolution K u₀ a) Au) :
    HasDerivWithinAt
      (fun t : ℝ ↦ D.uniformSolution K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property t))
      (Au + D.nonlinearity (D.uniformSolution K u₀ a))
      (Set.Ici (a : ℝ)) (a : ℝ) := by
  exact semilinearHeatBUCFixedPoint_hasDerivWithinAt_interior_right
    (E := E) (F := F) (D.uniformLifespan K) (u₀ : BUC)
      D.nonlinearity D.localData.continuous (D.uniformSolution K u₀)
      (D.uniformSolution_isFixedPt K u₀) a ha Au hua

end AffineRecenteredDeTurckShapedBUCRemainderData

end AffineInteriorRegularity

section ReconstructedMetricInteriorRegularity

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

local notation "T₂" => CoordinateTwoTensor E
local notation "BUCT₂" => CoordinateBUCTensor E

/-- The affine reconstructed coordinate metric has the same right derivative
as its perturbation, since the reconstructed background is time-independent. -/
theorem reconstructedMetricCoefficient_hasDerivWithinAt_interior_right
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    (a : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ))
    (ha : (a : ℝ) < (D.uniformLifespan K : ℝ))
    (Au : BUCT₂)
    (hua : IsInBUCHeatGeneratorDomain
      (E := E) (F := T₂) (D.uniformSolution K u₀ a) Au) :
    HasDerivWithinAt
      (fun t : ℝ ↦ D.reconstructedMetricCoefficient K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property t))
      (Au + D.nonlinearity (D.uniformSolution K u₀ a))
      (Set.Ici (a : ℝ)) (a : ℝ) := by
  have hbackground : HasDerivWithinAt
      (fun _t : ℝ ↦ D.recentered.background) 0
      (Set.Ici (a : ℝ)) (a : ℝ) :=
    hasDerivWithinAt_const (x := (a : ℝ))
      (s := Set.Ici (a : ℝ)) (c := D.recentered.background)
  have hsolution := D.uniformSolution_hasDerivWithinAt_interior_right
    K u₀ a ha Au hua
  simpa only [reconstructedMetricCoefficient, zero_add] using
    hbackground.add hsolution

/-- For the natural shifted-background package, the interior right derivative
is the original DeTurck-shaped nonlinearity evaluated on the current full
coefficient. -/
theorem ofShiftedBackground_reconstructedMetricCoefficient_hasDerivWithinAt_interior_right
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    (a : Set.Icc (0 : ℝ) ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (ha : (a : ℝ) < ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (Au : BUCT₂)
    (hua : IsInBUCHeatGeneratorDomain
      (E := E) (F := T₂)
      ((ofShiftedBackground D).uniformSolution K u₀ a) Au) :
    HasDerivWithinAt
      (fun t : ℝ ↦ (ofShiftedBackground D).reconstructedMetricCoefficient K u₀
        (Set.projIcc 0 ((ofShiftedBackground D).uniformLifespan K : ℝ)
          ((ofShiftedBackground D).uniformLifespan K).property t))
      (Au + D.base.nonlinearity
        ((ofShiftedBackground D).uniformSolution K u₀ a + D.background))
      (Set.Ici (a : ℝ)) (a : ℝ) := by
  simpa only [ofShiftedBackground_nonlinearity] using
    (ofShiftedBackground D).reconstructedMetricCoefficient_hasDerivWithinAt_interior_right
      K u₀ a ha Au hua

end AffineRecenteredDeTurckShapedBUCRemainderData

end ReconstructedMetricInteriorRegularity

end Poincare
