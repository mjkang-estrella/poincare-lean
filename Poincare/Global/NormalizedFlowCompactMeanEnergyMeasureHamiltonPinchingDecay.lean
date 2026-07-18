import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowCompactScalarMeanComparison
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor

/-!
# Compact mean-energy decay from Hamilton pinching

This module replaces the opaque normalized-reaction domination field in the
compact mean-energy route by geometric Hamilton pinching data.  Two estimates
which follow from the other fields are deliberately not stored:

* the Ricci quotient bound follows from positive scalar curvature and the
  global Ricci-eigenvalue floor; and
* a uniform pointwise scalar-to-mean comparison follows from compactness,
  joint scalar continuity, and the positive mean-scalar floor.

These estimates do not by themselves force decay.  Positivity of the remaining
coefficient gap is therefore retained as an explicit hypothesis.  Multiplying
that gap by the mean-scalar floor gives a positive uniform reaction-decay rate.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- Compact forward-flow data carrying the geometric inputs to Hamilton's
pinching estimate.

The normalized Ricci quotient and scalar-to-mean comparison are consequences,
not fields, of this structure. -/
structure NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3
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
  pinchingEpsilon : ℝ
  pinchingEpsilon_pos : 0 < pinchingEpsilon
  pinchingEpsilon_le_one_third : pinchingEpsilon ≤ 1 / 3
  pinchingDelta : ℝ
  pinchingDelta_nonneg : 0 ≤ pinchingDelta
  pinchingDelta_le_two : pinchingDelta ≤ 2
  pinchingDelta_admissible :
    pinchingDelta ≤
      PinchingAlgebra.pinchedTracelessAdmissibleDelta3 pinchingEpsilon
  scalarPositive : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    0 < (gt t).scalarAt x
  ricciEigenvalueFloor : ∀ t ∈ Ici (0 : ℝ),
    GlobalRicciEigenvalueFloor3 (gt t) pinchingEpsilon
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

/-- The quotient coefficient forced by the Hamilton eigenvalue floor. -/
def
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingQuotientCoefficient
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M) : ℝ :=
  1 - 4 * data.pinchingEpsilon + 6 * data.pinchingEpsilon ^ 2

/-- The quotient coefficient is positive; no separate nonnegativity field is
needed by the downstream reaction theorem. -/
theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingQuotientCoefficient_pos
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M) :
    0 < data.pinchingQuotientCoefficient := by
  simpa only
      [NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingQuotientCoefficient] using
    Poincare.pinchingQuotientCoefficient_pos data.pinchingEpsilon

/-- Positive scalar curvature and the global eigenvalue floor produce the
global quotient bound on every forward slice. -/
theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.globalPinchingQuotientBound
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M)
    (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
    GlobalPinchingQuotientBound3 (data.gt t)
      data.pinchingQuotientCoefficient := by
  simpa only
      [NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingQuotientCoefficient] using
    (data.gt t).globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
      (data.scalarPositive t ht) (data.ricciEigenvalueFloor t ht)

/-- Compactness and the positive mean-scalar floor supply at least one
positive scalar-to-mean comparison factor. -/
theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.existsScalarMeanFactor
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : Ici (0 : ℝ), ∀ x : M,
      (data.gt t.1).scalarAt x ≤ C * meanScalar (data.gt t.1) := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  exact
    exists_pos_uniform_scalarAt_le_mul_meanScalar_of_compact_parameterization_of_meanLower
      data.gt data.metric data.parameter data.realizesFlow
      data.meanScalarFloor_pos data.meanScalarLower data.scalarJointContinuous

/-- A fixed choice of the compactness-produced scalar-to-mean factor.

The accompanying theorems expose exactly the positivity and comparison
properties used below; no numerical property beyond those consequences is
claimed for this choice. -/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.scalarMeanFactor
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M) : ℝ :=
  Classical.choose data.existsScalarMeanFactor

theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.scalarMeanFactor_pos
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M) :
    0 < data.scalarMeanFactor :=
  (Classical.choose_spec data.existsScalarMeanFactor).1

theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.scalarAt_le_scalarMeanFactor_mul_meanScalar
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M)
    (t : Ici (0 : ℝ)) (x : M) :
    (data.gt t.1).scalarAt x ≤
      data.scalarMeanFactor * meanScalar (data.gt t.1) :=
  (Classical.choose_spec data.existsScalarMeanFactor).2 t x

/-- The coefficient which remains after inserting the quotient and
scalar-to-mean estimates into the normalized reaction. -/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingCoefficientGap
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
        M) : ℝ :=
  (4 / 3 : ℝ) -
    2 * (2 - data.pinchingDelta) * data.pinchingQuotientCoefficient *
      data.scalarMeanFactor

/-- The compact mean-energy analytic package with a genuinely geometric
evolution layer.

The only extra hypothesis beyond the compact Hamilton core is positivity of
the explicit coefficient left by the pinching calculation.  In particular,
this structure has no `actualReactionDomination` field. -/
structure NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  pinching :
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
      M
  pinchingCoefficientGap_pos : 0 < pinching.pinchingCoefficientGap

/-- The explicit positive decay rate is the coefficient gap times the
positive uniform mean-scalar floor. -/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.reactionDecayRate
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.{u, v}
        M) : ℝ :=
  data.pinching.pinchingCoefficientGap * data.pinching.meanScalarFloor

theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.reactionDecayRate_pos
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.{u, v}
        M) :
    0 < data.reactionDecayRate :=
  mul_pos data.pinchingCoefficientGap_pos data.pinching.meanScalarFloor_pos

/-- The compact Hamilton package constructs the former opaque reaction-decay
package.  The quotient and scalar/mean premises are discharged by the derived
lemmas above, while the uniform rate follows from the explicit coefficient
gap and the mean-scalar floor. -/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.toReactionDecayAnalyticData3
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
      M := by
  let core := data.pinching
  letI : TopologicalSpace core.K := core.topologicalSpaceK
  letI : CompactSpace core.K := core.compactSpaceK
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (core.gt t).leviCivita 1 :=
    fun _t ↦ inferInstance
  refine
    { K := core.K
      topologicalSpaceK := core.topologicalSpaceK
      compactSpaceK := core.compactSpaceK
      gt := core.gt
      metric := core.metric
      parameter := core.parameter
      parameterContinuous := core.parameterContinuous
      realizesFlow := core.realizesFlow
      meanScalarFloor := core.meanScalarFloor
      meanScalarFloor_pos := core.meanScalarFloor_pos
      meanScalarLower := core.meanScalarLower
      normalizedFlow := core.normalizedFlow
      compactFiniteAtlasChartFrameDensityData :=
        core.compactFiniteAtlasChartFrameDensityData
      jointMetricEntries := core.jointMetricEntries
      reactionDecayRate := data.reactionDecayRate
      reactionDecayRate_pos := data.reactionDecayRate_pos
      actualReactionDomination := ?_
      finiteVolumeMeasureContinuous := core.finiteVolumeMeasureContinuous
      scalarJointContinuous := core.scalarJointContinuous
      tracelessRicciNormSqJointContinuous :=
        core.tracelessRicciNormSqJointContinuous }
  intro t ht x
  apply
    normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
      (core.gt t) core.pinchingEpsilon_pos
        core.pinchingEpsilon_le_one_third core.pinchingDelta_nonneg
        core.pinchingDelta_le_two core.pinchingDelta_admissible
        core.pinchingQuotientCoefficient_pos.le
        (core.scalarPositive t ht) (core.ricciEigenvalueFloor t ht)
        (core.globalPinchingQuotientBound t ht)
        (fun y ↦
          core.scalarAt_le_scalarMeanFactor_mul_meanScalar ⟨t, ht⟩ y)
  have hMeanScale :
      core.pinchingCoefficientGap * core.meanScalarFloor ≤
        core.pinchingCoefficientGap * meanScalar (core.gt t) :=
    mul_le_mul_of_nonneg_left (core.meanScalarLower ⟨t, ht⟩)
      data.pinchingCoefficientGap_pos.le
  simpa only
      [NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.reactionDecayRate,
        NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingCoefficientGap] using
    hMeanScale

/-- The geometric package therefore reaches the existing moving-measure
compact mean-energy analytic endpoint. -/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.toMeasureAnalyticData3
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.{u, v} M :=
  data.toReactionDecayAnalyticData3.toMeasureAnalyticData3

/-- The derived finite-energy package reaches the selected-atlas compact
mean-energy sphere endpoint for any unit-curvature recognition input. -/
theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toMeasureAnalyticData3.sphereConclusion unitRecognition

end Poincare
