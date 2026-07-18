import Poincare.Global.CartanFixedTargetMovingAdaptiveRecognitionBoundary
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint
import Poincare.Global.HausdorffFiniteAtlasChartFrameReduction
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureSelectedSmoothAtlasPoincare

/-!
# Selected-atlas Poincare route from traceless-Ricci reaction domination

This file combines the strongest proof-producing analytic and Cartan routes.
On the analytic side, normalized Ricci flow and global joint `C³` metric
entries derive the exact Laplacian-plus-explicit-reaction evolution for
`|Ric°|²`; coercive domination of that actual geometric reaction then gives
finite total forward traceless-Ricci energy through the compact parabolic
maximum principle.

On the Cartan side, concrete moving-chart inputs construct an exact
target-local generic-data cover, while finite post-realization grid coherence
constructs every rooted overlap transport internally.  The selected package
therefore retains neither a raw generic-data cover, a
canonical-to-generic bridge, a preferred-chart normal comparison, a global
radius function, an arbitrary pointwise exponential estimate, nor a finite
strict-factor completion payload.

The endpoint is the moving-measure compact mean-energy route: weak continuity
of the finite Riemannian volume measures and joint continuity of the curvature
integrands realize a zero-traceless-energy compact limit.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanCanonicalFamilyComparedNeighborhood
open CartanCanonicalFamilyComparedForwardNormalRegularity
open CartanCanonicalFamilyComparedLocallyUniformRadiusEnvelope
open CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
open CartanSourceExponential
open CartanTargetExponential
open CartanFixedTargetMovingAdaptiveRecognitionBoundary

/-- Concrete compact mean-energy data in which finite total forward
traceless-Ricci energy is proved by the compact parabolic maximum principle.

The sole evolution-specific input is a coercive estimate for the explicit
normalized reaction: the exact evolution itself is derived from normalized
flow and joint `C³` metric entries. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3
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
  reactionDecayRate : ℝ
  reactionDecayRate_pos : 0 < reactionDecayRate
  actualReactionDomination : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
      -reactionDecayRate * (gt t).tracelessRicciNormSqAt x
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

/-- The exact evolution and coercive reaction estimate produce the
finite-energy moving-measure package consumed by the compact limit endpoint.
-/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.toMeasureAnalyticData3
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.{u, v} M := by
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1 :=
    fun _t ↦ inferInstance
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  have hEnergyContinuousOn : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack data.gt) (Ici 0) :=
    continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
      data.gt data.metric data.parameter data.parameterContinuous
        data.realizesFlow data.finiteVolumeMeasureContinuous
          data.tracelessRicciNormSqJointContinuous
  have hEnergyMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack data.gt)
      (MeasureTheory.volume.restrict (Ici 0)) :=
    normalizedFlowTracelessRicciEnergyTrack_aestronglyMeasurable_of_continuousOn
      data.gt hEnergyContinuousOn
  exact
    { K := data.K
      topologicalSpaceK := data.topologicalSpaceK
      compactSpaceK := data.compactSpaceK
      gt := data.gt
      metric := data.metric
      parameter := data.parameter
      realizesFlow := data.realizesFlow
      meanScalarFloor := data.meanScalarFloor
      meanScalarFloor_pos := data.meanScalarFloor_pos
      meanScalarLower := data.meanScalarLower
      finiteTracelessRicciEnergy :=
        normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
          data.gt data.normalizedFlow
            (fun t _ht ↦
              data.compactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation.hasDerivAt_totalVolume_of_normalizedFlowAt
                t (data.normalizedFlow t _ht))
            hEnergyMeasurable data.jointMetricEntries
              data.reactionDecayRate_pos data.actualReactionDomination
      finiteVolumeMeasureContinuous := data.finiteVolumeMeasureContinuous
      scalarJointContinuous := data.scalarJointContinuous
      tracelessRicciNormSqJointContinuous :=
        data.tracelessRicciNormSqJointContinuous }

/-- The derived finite-energy package reaches the moving-measure compact
mean-energy sphere endpoint for any unit-curvature recognition input. -/
theorem
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toMeasureAnalyticData3.sphereConclusion unitRecognition

/-- One selected smooth atlas carrying the reaction-domination producer, the
moving-measure compact endpoint, concrete moving-chart successor inputs, and
finite actual-grid coherence.

No arbitrary exponential decay estimate and no Cartan completion object is a
field of this package. -/
structure
    SelectedSmoothAtlasCompactMeanEnergyMeasureReactionDecayDirectUniformPackage3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  chartedSpace : ChartedSpace (ClosedSmoothModel 3) M
  smoothManifold :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    IsManifold (closedSmoothModelWithCorners 3) ∞ M
  analytic :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
      smoothManifold
    letI : SecondCountableTopology M :=
      selectedClosedSmoothAtlasSecondCountableTopology3 M chartedSpace
    letI : ConnectedSpace M :=
      connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
      M
  movingGenericSuccessorInputs :
    FixedTargetMovingGenericSuccessorInputs3 M
  postRealizationGridCoherence :
    FixedTargetMovingPostRealizationGridCoherence3
      M movingGenericSuccessorInputs

/-- Moving-chart successor construction and finite post-realization grid
coherence construct unit-curvature recognition directly; reaction domination
supplies finite energy, and the moving-measure compact endpoint concludes
roundness. -/
theorem
    SelectedSmoothAtlasCompactMeanEnergyMeasureReactionDecayDirectUniformPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasCompactMeanEnergyMeasureReactionDecayDirectUniformPackage3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  letI : ChartedSpace (ClosedSmoothModel 3) M := data.chartedSpace
  letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
    data.smoothManifold
  letI : SecondCountableTopology M :=
    selectedClosedSmoothAtlasSecondCountableTopology3 M data.chartedSpace
  letI : ConnectedSpace M :=
    connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have unitRecognition : UnitConstantCurvatureSphereRecognition3 M :=
    unitConstantCurvatureSphereRecognition3_of_fixedTargetMovingInputs_postRealizationGridCoherence
      data.movingGenericSuccessorInputs
      data.postRealizationGridCoherence
  exact data.analytic.sphereConclusion unitRecognition

/-- Universal existence of the strongest current concrete selected-atlas
package with actual-reaction input and direct Cartan transport. -/
def
    UniversalSelectedSmoothAtlasCompactMeanEnergyMeasureReactionDecayDirectUniformPackage3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasCompactMeanEnergyMeasureReactionDecayDirectUniformPackage3.{u, v}
          M)

/-- A universal moving-measure, reaction-decay, generic-data stability, and
finite adaptive-grid provider proves the canonical topological Poincare
statement. -/
theorem
    poincareConjectureStatement_of_universalSelectedSmoothAtlasCompactMeanEnergyMeasureReactionDecayDirectUniformPackage3
    (provider :
      UniversalSelectedSmoothAtlasCompactMeanEnergyMeasureReactionDecayDirectUniformPackage3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
