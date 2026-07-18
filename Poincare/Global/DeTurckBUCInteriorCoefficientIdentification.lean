import Poincare.Global.DeTurckBUCReconstructedPathInteriorRegularity

/-!
# Interior geometric slope of the reconstructed DeTurck coefficient

Automatic positive-time classicality gives a concrete Banach-valued slope
for the reconstructed coordinate metric path.  Honest full/background metric
germs and the pointwise lower-order remainder formula identify every scalar
entry of that slope with the Ricci--DeTurck chart evolution.  Derivative
uniqueness then assembles the scalar identities into one continuous bilinear
form equality.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction Manifold ContDiff

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

/--
At every strict positive interior time, the canonical Banach-valued slope of
the reconstructed coefficient is the concrete Ricci--DeTurck evolution at a
chart point.  The only geometric inputs are honest germs for the current full
coefficient and the fixed background, together with the already isolated
pointwise lower-order remainder identity.
-/
theorem coordinateBilinearFormAt_reconstructedInteriorSlope_eq_deTurckChartMetricEvolutionBilin_of_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    {t : ℝ} (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan
        K : ℝ))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
              K u₀ t +
            D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t z v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorGeneratorValue
            K u₀ t +
          D.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor t z := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  let g' : CoordinateBUCTensor E :=
    A.uniformInteriorGeneratorValue K u₀ t +
      D.base.nonlinearity (A.uniformInteriorState K u₀ t + D.background)
  have hg : HasDerivAt
      (reconstructedCoordinateMetricPath D K u₀) g' t := by
    simpa only [A, g'] using
      reconstructedCoordinateMetricPath_hasDerivAt_interior_automatic
        D K u₀ ht₀ htT
  have htWindow : t ∈ Set.Ioo (t / 2) (A.uniformLifespan K : ℝ) := by
    exact ⟨by linarith, htT⟩
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change coordinateMetricValue g' z v w =
    deTurckChartMetricEvolutionBilin gt bg anchor t z v w
  let L := coordinateMetricEvaluationCLM z v w
  have hvalueRaw := L.hasFDerivAt.comp_hasDerivAt t hg
  have hvalue : HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        (reconstructedCoordinateMetricPath D K u₀ r) z v w)
      (coordinateMetricValue g' z v w) t := by
    simpa only [L, Function.comp_def, coordinateMetricEvaluationCLM_apply] using
      hvalueRaw
  have hvalue' : HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        (A.reconstructedMetricCoefficient K u₀
          (Set.projIcc 0 (A.uniformLifespan K : ℝ)
            (A.uniformLifespan K).property r)) z v w)
      (coordinateMetricValue g' z v w) t := by
    simpa only [reconstructedCoordinateMetricPath, A] using hvalue
  have hgeometric :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_germs
      D K u₀
      (c := t / 4) (a := t / 2) (b := (A.uniformLifespan K : ℝ))
      (α := (1 / 2 : ℝ))
      (by linarith) (by linarith)
      (by dsimp only [A]; linarith) (by exact le_rfl)
      (by norm_num) (by norm_num) htWindow
      gt bg anchor hz v w hfullGerm hbackgroundGerm (hremainder v w)
  exact hvalue'.unique hgeometric

end Poincare
