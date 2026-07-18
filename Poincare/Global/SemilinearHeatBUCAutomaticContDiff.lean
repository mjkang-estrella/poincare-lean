import Poincare.Global.SemilinearHeatBUCLocalAutomaticClassical

/-!
# Automatic positive-time C1 regularity for semilinear BUC paths

The automatic classicality layer already supplies an ordinary derivative at
every positive interior time.  The Hölder-Duhamel construction also makes the
selected generator path continuous on compact windows separated from zero.
This file combines those facts into genuine `ContDiffOn ℝ 1` statements.

No regularity at the initial endpoint is asserted.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction ContDiff

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- Uniform endpoint Hölder forcing upgrades the interior derivative theorem
to a continuously differentiable path on the open positive-time window. -/
theorem semilinearHeatBUCFixedPoint_contDiffOn_one_interior_of_uniformHolder_forcing
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    {a b K α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbT : b ≤ (T : ℝ)) (hK : 0 ≤ K) (hα : 0 < α)
    (hholder : ∀ t ∈ Set.Icc a b,
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖semilinearHeatBUCProjectedForcing T N u s -
            semilinearHeatBUCProjectedForcing T N u t‖ ≤
          K * |t - s| ^ α) :
    ContDiffOn ℝ 1
      (fun r : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property r))
      (Set.Ioo a b) := by
  let path : ℝ → BUC := fun r ↦
    u (Set.projIcc 0 (T : ℝ) T.property r)
  let G : ℝ → BUC := semilinearHeatBUCProjectedForcing T N u
  let A : ℝ → BUC :=
    semilinearHeatBUCInteriorGeneratorValue
      (E := E) (F := F) T u₀ N u
  let velocity : ℝ → BUC := fun r ↦ A r + G r
  have hA : ContinuousOn A (Set.Icc a b) := by
    exact continuousOn_semilinearHeatBUCInteriorGeneratorValue_of_uniformHolder
      (E := E) (F := F) T u₀ N hN u ha hab hK hα hholder
  have hG : Continuous G := by
    exact continuous_semilinearHeatBUCProjectedForcing T N hN u
  have hvelocityIcc : ContinuousOn velocity (Set.Icc a b) :=
    hA.add hG.continuousOn
  have hvelocity : ContinuousOn velocity (Set.Ioo a b) :=
    hvelocityIcc.mono fun _ ht ↦ ⟨ht.1.le, ht.2.le⟩
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt path (velocity t) t := by
    simpa only [path, velocity, A, G] using
      semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_uniformHolder_forcing
        (E := E) (F := F) T u₀ N hN u hu
        ha hab hbT hK hα hholder
  rw [show (fun r : ℝ ↦
      u (Set.projIcc 0 (T : ℝ) T.property r)) = path from rfl]
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  constructor
  · intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  · apply hvelocity.congr
    intro t ht
    exact (hderiv t ht).hasDerivWithinAt.derivWithin
      (isOpen_Ioo.uniqueDiffWithinAt ht)

/-- Range-local Lipschitz control makes a semilinear fixed point automatically
`C1` on every compactly separated positive-time interior window. -/
theorem semilinearHeatBUCFixedPoint_contDiffOn_one_interior_of_lipschitzOn_range
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (L : ℝ≥0) (hNLipschitz : LipschitzOnWith L N (Set.range u))
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (T : ℝ)) (hα0 : 0 < α) (hα1 : α < 1) :
    ContDiffOn ℝ 1
      (fun r : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property r))
      (Set.Ioo a b) := by
  obtain ⟨K, hK, hholder⟩ :=
    exists_endpointHolderConstant_semilinearHeatBUCProjectedForcing
      (E := E) (F := F) T u₀ N hN u hu L hNLipschitz
      hc hca hab hbT hα0 hα1
  exact
    semilinearHeatBUCFixedPoint_contDiffOn_one_interior_of_uniformHolder_forcing
      (E := E) (F := F) T u₀ N hN u hu
      (hc.trans hca) hab hbT hK hα0 hholder

/-- The bounded-ball local solution is automatically `C1` on every strict
positive-time window. -/
theorem semilinearHeatBUCUniformLocalSolution_contDiffOn_one_interior
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (semilinearHeatBUCUniformLifespan data K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ContDiffOn ℝ 1
      (fun r : ℝ ↦ semilinearHeatBUCUniformLocalSolution K N data u₀
        (Set.projIcc 0 (semilinearHeatBUCUniformLifespan data K : ℝ)
          (semilinearHeatBUCUniformLifespan data K).property r))
      (Set.Ioo a b) := by
  let u : DuhamelPath (semilinearHeatBUCUniformLifespan data K) BUC :=
    semilinearHeatBUCUniformLocalSolution K N data u₀
  have hRange : Set.range u ⊆
      Metric.closedBall (0 : BUC) ((K + 1 : ℝ≥0) : ℝ) := by
    rintro x ⟨t, rfl⟩
    have hnorm := norm_semilinearHeatBUCUniformLocalSolution_le
      (E := E) (F := F) K N data u₀ t
    simpa only [u, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm
  have hNLipschitz : LipschitzOnWith (data.lipschitz (K + 1)) N
      (Set.range u) :=
    (data.lipschitzOn_closedBall (K + 1)).mono hRange
  simpa only [u] using
    semilinearHeatBUCFixedPoint_contDiffOn_one_interior_of_lipschitzOn_range
      (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K)
      (u₀ : BUC) N data.continuous u
      (semilinearHeatBUCUniformLocalSolution_isFixedPt
        (E := E) (F := F) K N data u₀)
      (data.lipschitz (K + 1)) hNLipschitz
      hc hca hab hbT hα0 hα1

namespace DeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- The assembled bounded-ball DeTurck coefficient path is automatically
`C1` at strict positive times. -/
theorem uniformSolution_contDiffOn_one_interior
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (D.uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ContDiffOn ℝ 1
      (fun r : ℝ ↦ D.uniformSolution K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property r))
      (Set.Ioo a b) := by
  simpa only [uniformSolution, uniformLifespan] using
    semilinearHeatBUCUniformLocalSolution_contDiffOn_one_interior
      (E := E) (F := F) K D.nonlinearity D.localData u₀
      hc hca hab hbT hα0 hα1

end DeTurckShapedBUCRemainderData

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- The affine bounded-ball coefficient path is automatically `C1` at strict
positive times. -/
theorem uniformSolution_contDiffOn_one_interior
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (D.uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ContDiffOn ℝ 1
      (fun r : ℝ ↦ D.uniformSolution K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property r))
      (Set.Ioo a b) := by
  simpa only [uniformSolution, uniformLifespan] using
    semilinearHeatBUCUniformLocalSolution_contDiffOn_one_interior
      (E := E) (F := F) K D.nonlinearity D.localData u₀
      hc hca hab hbT hα0 hα1

end AffineRecenteredDeTurckShapedBUCRemainderData

section AffineReconstructedMetric

local notation "T₂" => CoordinateTwoTensor E

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- Adding the time-independent background preserves automatic positive-time
`C1` regularity of the reconstructed tensor coefficient. -/
theorem reconstructedMetricCoefficient_contDiffOn_one_interior
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (D.uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ContDiffOn ℝ 1
      (fun r : ℝ ↦ D.reconstructedMetricCoefficient K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property r))
      (Set.Ioo a b) := by
  have hbackground : ContDiffOn ℝ 1
      (fun _r : ℝ ↦ D.recentered.background) (Set.Ioo a b) :=
    contDiffOn_const
  have hsolution := D.uniformSolution_contDiffOn_one_interior
    K u₀ hc hca hab hbT hα0 hα1
  simpa only [reconstructedMetricCoefficient] using
    hbackground.add hsolution

end AffineRecenteredDeTurckShapedBUCRemainderData

end AffineReconstructedMetric

end Poincare
