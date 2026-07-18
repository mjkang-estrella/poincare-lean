import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay

/-!
# A quantitative near-round tail with an automatic Hamilton coefficient gap

The eventual Hamilton package leaves two algebraic choices visible: the
Ricci-eigenvalue pinching constant `epsilon`, and an admissible exponent
`delta`.  It also asks separately that the coefficient remaining after the
scalar-to-mean estimate be positive.

This file records one completely explicit regime in which that last sign is
automatic.  We fix

* `epsilon = 3 / 10`;
* `delta = pinchedTracelessAdmissibleDelta3 epsilon = 54 / 67`; and
* the compact scalar-to-mean factor at most `3 / 2`.

For these values the quotient coefficient is `17 / 50`, the reaction
coefficient multiplying the scalar-to-mean factor is `272 / 335`, and the
remaining gap is bounded below by

`4 / 3 - (272 / 335) * (3 / 2) = 116 / 1005 > 0`.

Thus the narrow input structure below has neither a free `delta` nor a
coefficient-gap hypothesis.  The bound on the scalar-to-mean factor is a real
quantitative near-round assumption; it is not claimed to follow merely from
compactness.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- The fixed Ricci-eigenvalue floor used by the quantitative tail package. -/
def quantitativeNearRoundPinchingEpsilon3 : ℝ := 3 / 10

/-- The largest exponent supplied by the proved Hamilton pinching algebra at
`epsilon = 3 / 10`. -/
noncomputable def quantitativeNearRoundPinchingDelta3 : ℝ :=
  PinchingAlgebra.pinchedTracelessAdmissibleDelta3
    quantitativeNearRoundPinchingEpsilon3

theorem quantitativeNearRoundPinchingDelta3_eq :
    quantitativeNearRoundPinchingDelta3 = 54 / 67 := by
  norm_num [quantitativeNearRoundPinchingDelta3,
    quantitativeNearRoundPinchingEpsilon3,
    PinchingAlgebra.pinchedTracelessAdmissibleDelta3]

theorem quantitativeNearRoundPinchingQuotientCoefficient3_eq :
    1 - 4 * quantitativeNearRoundPinchingEpsilon3 +
        6 * quantitativeNearRoundPinchingEpsilon3 ^ 2 = 17 / 50 := by
  norm_num [quantitativeNearRoundPinchingEpsilon3]

theorem quantitativeNearRoundReactionScalarCoefficient3_eq :
    2 * (2 - quantitativeNearRoundPinchingDelta3) *
        (1 - 4 * quantitativeNearRoundPinchingEpsilon3 +
          6 * quantitativeNearRoundPinchingEpsilon3 ^ 2) = 272 / 335 := by
  rw [quantitativeNearRoundPinchingDelta3_eq,
    quantitativeNearRoundPinchingQuotientCoefficient3_eq]
  norm_num

theorem quantitativeNearRoundCoefficientGapLowerBound3_pos :
    0 < (116 / 1005 : ℝ) := by
  norm_num

/-- Compact normalized-flow data with a fixed quantitative near-round tail.

Unlike the general eventual Hamilton core, this structure contains no
`pinchingEpsilon` or `pinchingDelta` fields. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : Ici (0 : ℝ) → K
  parameterContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous parameter
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  meanScalarFloor : ℝ
  meanScalarFloor_pos : 0 < meanScalarFloor
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  normalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  compactFiniteAtlasChartFrameDensityData :
    CompactFiniteAtlasChartFrameDensityData gt
  jointMetricEntries : ∀ t : ℝ, ∀ x : M,
    MetricEntriesJointContDiffAt gt t x 3
  tailStart : ℝ
  tailStart_nonneg : 0 ≤ tailStart
  scalarPositiveOnTail : ∀ t ∈ Ici tailStart, ∀ x : M,
    0 < (gt t).scalarAt x
  ricciEigenvalueFloorOnTail : ∀ t ∈ Ici tailStart,
    GlobalRicciEigenvalueFloor3 (gt t)
      quantitativeNearRoundPinchingEpsilon3
  finiteVolumeMeasureContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k))
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)

namespace NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Forget the fixed-constant presentation and obtain the general eventual
Hamilton core.  The admissibility proof is equality because the chosen
`delta` is exactly the proved algebraic endpoint. -/
noncomputable def toEventualHamiltonPinchingCoreData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.{u, v}
      M :=
  { K := data.K
    topologicalSpaceK := data.topologicalSpaceK
    compactSpaceK := data.compactSpaceK
    gt := data.gt
    metric := data.metric
    parameter := data.parameter
    parameterContinuous := data.parameterContinuous
    realizesFlow := data.realizesFlow
    meanScalarFloor := data.meanScalarFloor
    meanScalarFloor_pos := data.meanScalarFloor_pos
    meanScalarLower := data.meanScalarLower
    normalizedFlow := data.normalizedFlow
    compactFiniteAtlasChartFrameDensityData :=
      data.compactFiniteAtlasChartFrameDensityData
    jointMetricEntries := data.jointMetricEntries
    tailStart := data.tailStart
    tailStart_nonneg := data.tailStart_nonneg
    pinchingEpsilon := quantitativeNearRoundPinchingEpsilon3
    pinchingEpsilon_pos := by
      norm_num [quantitativeNearRoundPinchingEpsilon3]
    pinchingEpsilon_le_one_third := by
      norm_num [quantitativeNearRoundPinchingEpsilon3]
    pinchingDelta := quantitativeNearRoundPinchingDelta3
    pinchingDelta_nonneg := by
      rw [quantitativeNearRoundPinchingDelta3_eq]
      norm_num
    pinchingDelta_le_two := by
      rw [quantitativeNearRoundPinchingDelta3_eq]
      norm_num
    pinchingDelta_admissible := le_rfl
    scalarPositiveOnTail := data.scalarPositiveOnTail
    ricciEigenvalueFloorOnTail := data.ricciEigenvalueFloorOnTail
    finiteVolumeMeasureContinuous := data.finiteVolumeMeasureContinuous
    scalarJointContinuous := data.scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      data.tracelessRicciNormSqJointContinuous }

end NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3

/-- Quantitative near-round tail data sufficient for eventual Hamilton decay.

The only extra quantitative field is the actual `3 / 2` scalar-to-mean
comparison on the eventual tail.  It deliberately says nothing about the
noncanonical compactness-produced global factor, which must also cover the omitted
initial interval.  No coefficient-gap sign is assumed. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  nearRound :
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3.{u, v}
      M
  scalarAt_le_three_halves_mul_meanScalarOnTail :
    ∀ t ∈ Ici nearRound.tailStart, ∀ x : M,
      (nearRound.gt t).scalarAt x ≤
        (3 / 2 : ℝ) * meanScalar (nearRound.gt t)

namespace NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The fixed constants and the `3/2` scalar-to-mean factor give a completely
explicit Hamilton coefficient gap. -/
theorem pinchingCoefficientGap_eq_explicit
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
        M) :
    (4 / 3 : ℝ) -
        2 * (2 -
          data.nearRound.toEventualHamiltonPinchingCoreData3.pinchingDelta) *
          data.nearRound.toEventualHamiltonPinchingCoreData3.pinchingQuotientCoefficient *
            (3 / 2 : ℝ) =
      116 / 1005 := by
  let core := data.nearRound.toEventualHamiltonPinchingCoreData3
  have hCoefficient :
      2 * (2 - core.pinchingDelta) *
          core.pinchingQuotientCoefficient = 272 / 335 := by
    simpa only
        [core,
          NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3.toEventualHamiltonPinchingCoreData3,
          NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.pinchingQuotientCoefficient] using
      quantitativeNearRoundReactionScalarCoefficient3_eq
  rw [hCoefficient]
  norm_num

theorem pinchingCoefficientGap_pos
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
        M) :
    0 < (4 / 3 : ℝ) -
      2 * (2 -
        data.nearRound.toEventualHamiltonPinchingCoreData3.pinchingDelta) *
        data.nearRound.toEventualHamiltonPinchingCoreData3.pinchingQuotientCoefficient *
          (3 / 2 : ℝ) := by
  rw [data.pinchingCoefficientGap_eq_explicit]
  exact quantitativeNearRoundCoefficientGapLowerBound3_pos

/-- Convert the fixed near-round regime to the general eventual Hamilton
package.  In particular, this construction discharges the general package's
coefficient-gap field rather than forwarding it as a premise. -/
noncomputable def toEventualHamiltonPinchingDecayAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingDecayAnalyticData3.{u, v}
  M :=
  { pinching := data.nearRound.toEventualHamiltonPinchingCoreData3
    tailScalarMeanFactor := 3 / 2
    tailScalarMeanFactor_pos := by norm_num
    scalarAt_le_tailScalarMeanFactor_mul_meanScalar :=
      data.scalarAt_le_three_halves_mul_meanScalarOnTail
    tailPinchingCoefficientGap_pos := data.pinchingCoefficientGap_pos }

/-- The quantitative near-round tail therefore yields finite total forward
traceless-Ricci energy, including the compact interval before the tail. -/
theorem finiteTracelessRicciEnergy
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack data.nearRound.gt) (Ici 0) := by
  simpa only [toEventualHamiltonPinchingDecayAnalyticData3,
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3.toEventualHamiltonPinchingCoreData3] using
    data.toEventualHamiltonPinchingDecayAnalyticData3.finiteTracelessRicciEnergy

/-- The automatic quantitative gap reaches the same compact moving-measure
sphere endpoint as the general eventual Hamilton package. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toEventualHamiltonPinchingDecayAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3

end Poincare
