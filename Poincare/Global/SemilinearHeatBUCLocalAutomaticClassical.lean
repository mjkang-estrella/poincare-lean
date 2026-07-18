import Poincare.Global.SemilinearHeatBUCAutomaticClassical
import Poincare.Global.SemilinearHeatBUCPolynomialLocalData

/-!
# Automatic classicality for bounded-ball semilinear heat solutions

The uniform local solver already keeps its selected path in the closed
zero-centered ball of radius `K + 1`.  The local-data package is Lipschitz on
that same ball.  Consequently the nonlinearity is Lipschitz on the actual path
range, exactly the premise required by
`semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_lipschitzOn_range`.

This removes the earlier need to supply, separately at each positive time, a
heat-generator value and graph witness for the current state.  No derivative
claim at time zero is made here.
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

/-- The same bounded-ball argument also exposes the canonical positive-time
heat-generator graph witness used internally by automatic classicality.  This
is useful when a later spatial theorem identifies that selected generator with
a coordinate Laplacian. -/
theorem semilinearHeatBUCUniformLocalSolution_mem_heatGeneratorDomain_interior
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (semilinearHeatBUCUniformLifespan data K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Icc a b,
      IsInBUCHeatGeneratorDomain (E := E) (F := F)
        (semilinearHeatBUCUniformLocalSolution K N data u₀
          (Set.projIcc 0 (semilinearHeatBUCUniformLifespan data K : ℝ)
            (semilinearHeatBUCUniformLifespan data K).property t))
        (semilinearHeatBUCInteriorGeneratorValue
          (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K)
          (u₀ : BUC) N
          (semilinearHeatBUCUniformLocalSolution K N data u₀) t) := by
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
  obtain ⟨H, hH, hholder⟩ :=
    exists_endpointHolderConstant_semilinearHeatBUCProjectedForcing
      (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K)
      (u₀ : BUC) N data.continuous u
      (semilinearHeatBUCUniformLocalSolution_isFixedPt
        (E := E) (F := F) K N data u₀)
      (data.lipschitz (K + 1)) hNLipschitz
      hc hca hab hbT hα0 hα1
  intro t ht
  have htpos : 0 < t := hc.trans (hca.trans_le ht.1)
  have htT : t ≤ (semilinearHeatBUCUniformLifespan data K : ℝ) :=
    ht.2.trans hbT
  simpa only [u] using
    semilinearHeatBUCFixedPoint_mem_heatGeneratorDomain_of_forcing_holder
      (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K)
      (u₀ : BUC) N data.continuous u
      (semilinearHeatBUCUniformLocalSolution_isFixedPt
        (E := E) (F := F) K N data u₀)
      (t := t) ⟨htpos, htT⟩ hH hα0 (hholder t ht)

/-- The bounded-ball local semilinear solution is classical at every positive
interior time.  Its generator value is selected canonically by the heat
Duhamel construction; no pointwise generator-domain premise is assumed. -/
theorem semilinearHeatBUCUniformLocalSolution_hasDerivAt_interior
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (semilinearHeatBUCUniformLifespan data K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ semilinearHeatBUCUniformLocalSolution K N data u₀
          (Set.projIcc 0 (semilinearHeatBUCUniformLifespan data K : ℝ)
            (semilinearHeatBUCUniformLifespan data K).property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K)
            (u₀ : BUC) N
            (semilinearHeatBUCUniformLocalSolution K N data u₀) t +
          semilinearHeatBUCProjectedForcing
            (semilinearHeatBUCUniformLifespan data K) N
            (semilinearHeatBUCUniformLocalSolution K N data u₀) t) t := by
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
  exact semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_lipschitzOn_range
    (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K)
    (u₀ : BUC) N data.continuous u
    (semilinearHeatBUCUniformLocalSolution_isFixedPt
      (E := E) (F := F) K N data u₀)
    (data.lipschitz (K + 1)) hNLipschitz hc hca hab hbT hα0 hα1

namespace DeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- The assembled DeTurck-shaped bounded-ball solution is automatically
classical at every positive interior time.  Compared with the pointwise
generator-domain interface used by the earlier interior-right regularity
layer, this theorem removes the manual current-state generator value `Au` and
graph witness `hua`. -/
theorem uniformSolution_hasDerivAt_interior
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (D.uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ D.uniformSolution K u₀
          (Set.projIcc 0 (D.uniformLifespan K : ℝ)
            (D.uniformLifespan K).property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := F) (D.uniformLifespan K) (u₀ : BUC)
            D.nonlinearity (D.uniformSolution K u₀) t +
          semilinearHeatBUCProjectedForcing (D.uniformLifespan K)
            D.nonlinearity (D.uniformSolution K u₀) t) t := by
  simpa only [uniformSolution, uniformLifespan] using
    semilinearHeatBUCUniformLocalSolution_hasDerivAt_interior
      (E := E) (F := F) K D.nonlinearity D.localData u₀
      hc hca hab hbT hα0 hα1

end DeTurckShapedBUCRemainderData

end Poincare
