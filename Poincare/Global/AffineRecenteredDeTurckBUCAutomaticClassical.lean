import Poincare.Global.SemilinearHeatBUCLocalAutomaticClassical
import Poincare.Global.DeTurckBUCChartCovariance

/-!
# Automatic positive-time classicality for affine recentered DeTurck solutions

The bounded-ball affine solver is an instance of the uniform local semilinear
heat solver.  Its closed-ball estimate therefore supplies the range-local
Lipschitz hypothesis used by the automatic positive-time regularity theorem.
At every strict positive interior time this gives an ordinary Banach-valued
derivative, with the heat-generator value selected canonically by the mild
construction.  Adding the fixed background preserves that derivative, and a
continuous coordinate evaluation preserves it once more.

These results remove the pointwise `Au` and strong-generator graph witness
required by the earlier right-derivative interface in
`SemilinearHeatBUCInteriorRegularity`.  They deliberately do not identify the
selected generator with a classical coordinate Laplacian.  That is a separate
spatial regularity boundary: it still requires one of the classical-core,
heat-trace, or Laplacian-consistency hypotheses exposed by
`DeTurckBUCClassicalCoreIdentification` and `DeTurckBUCGeneratorLaplacian`.
No claim is made at time zero.
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

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- The affine bounded-ball solution is an ordinary classical solution at
every strict positive interior time.  The derivative uses the generator value
selected by the heat-Duhamel construction, so no current-state generator
value or graph witness is supplied by the caller. -/
theorem uniformSolution_hasDerivAt_interior
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
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

end AffineRecenteredDeTurckShapedBUCRemainderData

section ReconstructedMetric

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "T₂" => CoordinateTwoTensor E
local notation "BUCT₂" => CoordinateBUCTensor E

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- Adding the time-independent background to the automatic affine solution
preserves its ordinary positive-time derivative. -/
theorem reconstructedMetricCoefficient_hasDerivAt_interior
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (D.uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ D.reconstructedMetricCoefficient K u₀
          (Set.projIcc 0 (D.uniformLifespan K : ℝ)
            (D.uniformLifespan K).property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := T₂) (D.uniformLifespan K) (u₀ : BUCT₂)
            D.nonlinearity (D.uniformSolution K u₀) t +
          semilinearHeatBUCProjectedForcing (D.uniformLifespan K)
            D.nonlinearity (D.uniformSolution K u₀) t) t := by
  intro t ht
  have hbackground : HasDerivAt
      (fun _r : ℝ ↦ D.recentered.background) 0 t :=
    hasDerivAt_const (x := t) (c := D.recentered.background)
  have hsolution := D.uniformSolution_hasDerivAt_interior
    K u₀ hc hca hab hbT hα0 hα1 t ht
  simpa only [reconstructedMetricCoefficient, zero_add] using
    hbackground.add hsolution

/-- For the natural shifted-background package, automatic positive-time
classicality has the original DeTurck-shaped nonlinearity evaluated on the
current full coefficient.  Only the selected heat-generator summand remains
abstract at the spatial level. -/
theorem ofShiftedBackground_reconstructedMetricCoefficient_hasDerivAt_interior
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ (ofShiftedBackground D).reconstructedMetricCoefficient
          K u₀
          (Set.projIcc 0 ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := T₂) ((ofShiftedBackground D).uniformLifespan K)
            (u₀ : BUCT₂) (ofShiftedBackground D).nonlinearity
            ((ofShiftedBackground D).uniformSolution K u₀) t +
          D.base.nonlinearity
            ((ofShiftedBackground D).uniformSolution K u₀
                (Set.projIcc 0
                  ((ofShiftedBackground D).uniformLifespan K : ℝ)
                  ((ofShiftedBackground D).uniformLifespan K).property t) +
              D.background)) t := by
  intro t ht
  simpa only [semilinearHeatBUCProjectedForcing_apply,
    ofShiftedBackground_nonlinearity] using
    (ofShiftedBackground D).reconstructedMetricCoefficient_hasDerivAt_interior
      K u₀ hc hca hab hbT hα0 hα1 t ht

end AffineRecenteredDeTurckShapedBUCRemainderData

/-- Ordinary Banach-valued differentiability of coordinate tensor
coefficients may be evaluated at fixed spatial and tangent data. -/
theorem HasDerivAt.coordinateMetricValue
    {g : ℝ → CoordinateBUCTensor E} {g' : CoordinateBUCTensor E}
    {t : ℝ} (h : HasDerivAt g g' t) (x v w : E) :
    HasDerivAt
      (fun r ↦ coordinateMetricValue (g r) x v w)
      (coordinateMetricValue g' x v w) t := by
  simpa only [hasDerivWithinAt_univ] using
    Poincare.HasDerivWithinAt.coordinateMetricValue
      (h.hasDerivWithinAt : HasDerivWithinAt g g' Set.univ t) x v w

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- Scalar coordinate form of automatic positive-time classicality for the
reconstructed natural shifted-background solution.  The derivative is still
written with the canonical selected generator because identifying that
summand with a coordinate Laplacian is an independent spatial theorem. -/
theorem ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (x v w : E) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ coordinateMetricValue
          ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
            (Set.projIcc 0
              ((ofShiftedBackground D).uniformLifespan K : ℝ)
              ((ofShiftedBackground D).uniformLifespan K).property r)) x v w)
        (coordinateMetricValue
          (semilinearHeatBUCInteriorGeneratorValue
              (E := E) (F := T₂)
              ((ofShiftedBackground D).uniformLifespan K)
              (u₀ : BUCT₂) (ofShiftedBackground D).nonlinearity
              ((ofShiftedBackground D).uniformSolution K u₀) t +
            D.base.nonlinearity
              ((ofShiftedBackground D).uniformSolution K u₀
                  (Set.projIcc 0
                    ((ofShiftedBackground D).uniformLifespan K : ℝ)
                    ((ofShiftedBackground D).uniformLifespan K).property t) +
                D.background)) x v w) t := by
  intro t ht
  exact HasDerivAt.coordinateMetricValue
    (ofShiftedBackground_reconstructedMetricCoefficient_hasDerivAt_interior
      D K u₀ hc hca hab hbT hα0 hα1 t ht) x v w

end AffineRecenteredDeTurckShapedBUCRemainderData

end ReconstructedMetric

end Poincare
