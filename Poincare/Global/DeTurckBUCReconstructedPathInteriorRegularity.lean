import Poincare.Global.AffineRecenteredDeTurckBUCClassicalCoreAutomatic
import Poincare.Global.DeTurckBUCInverseGaugeEvolution

/-!
# Automatic interior regularity of the reconstructed coordinate path

Automatic positive-time classicality gives an ordinary Banach-valued
derivative of the affine reconstructed coefficient on every window separated
from time zero.  This file specializes that result directly to
`reconstructedCoordinateMetricPath` at an arbitrary strict interior time.

The selected heat-generator term is a concrete `CoordinateBUCTensor`; its
further identification with the coordinate Laplacian remains a separate
spatial regularity question.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction

namespace Poincare

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {ι κ : Type*}

/--
The projected reconstructed coordinate metric is genuinely two-sided
differentiable at every strict positive time before its uniform lifespan.
The derivative is the canonical heat-generator value selected by the mild
solution construction plus the original DeTurck-shaped nonlinearity evaluated
on the current full coefficient.
-/
theorem reconstructedCoordinateMetricPath_hasDerivAt_interior_automatic
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    {t : ℝ} (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) :
    HasDerivAt
      (reconstructedCoordinateMetricPath D K u₀)
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorGeneratorValue
          K u₀ t +
        D.base.nonlinearity
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
              K u₀ t +
            D.background)) t := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  have hwindow :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground_reconstructedMetricCoefficient_hasDerivAt_interior
      D K u₀
      (c := t / 4) (a := t / 2) (b := (A.uniformLifespan K : ℝ))
      (α := (1 / 2 : ℝ))
      (by linarith) (by linarith) (by dsimp only [A]; linarith)
      (by exact le_rfl) (by norm_num) (by norm_num)
  have ht : t ∈ Set.Ioo (t / 2) (A.uniformLifespan K : ℝ) := by
    constructor
    · linarith
    · exact htT
  simpa only [reconstructedCoordinateMetricPath,
    AffineRecenteredDeTurckShapedBUCRemainderData.uniformInteriorGeneratorValue,
    AffineRecenteredDeTurckShapedBUCRemainderData.uniformInteriorState,
    A] using hwindow t ht

end Poincare
