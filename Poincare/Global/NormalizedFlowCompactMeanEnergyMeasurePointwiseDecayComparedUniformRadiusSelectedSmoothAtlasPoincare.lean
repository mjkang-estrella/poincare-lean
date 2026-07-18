import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureComparedUniformRadiusSelectedSmoothAtlasPoincare

/-!
# Selected-atlas Poincare route from pointwise forward curvature decay

This file removes the raw finite-energy assumption from the strongest current
moving-measure selected-atlas route.  Instead, the analytic package records a
forward normalized Ricci flow, the explicit moving-volume first-variation
identity, measurability of the total traceless-Ricci energy track, and a
positive-rate pointwise exponential decay estimate.  Volume preservation and
integration of the pointwise bound then prove finite total forward energy.

The Cartan side retains canonical compared-successor provenance, derives one
generic uniform successor radius, and computes every overlap grid rather than
storing row, rung, cross-cell, or predecessor-equality payload.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanAtlasRootedPathSkeleton
open CartanCanonicalFamilyComparedToGenericSuccessorRadius
open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly.CanonicalRootedRealizationPackage
open CartanTargetExponential

/-- Concrete compact mean-energy analytic data in which finite total forward
traceless-Ricci energy is proved from positive-rate pointwise exponential
decay along a volume-preserving normalized flow. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasurePointwiseDecayAnalyticData3
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
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  meanScalarFloor : ℝ
  meanScalarFloor_pos : 0 < meanScalarFloor
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  normalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  movingVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t
  energyTrackMeasurable : AEStronglyMeasurable
    (normalizedFlowTracelessRicciEnergyTrack gt)
    (MeasureTheory.volume.restrict (Ici 0))
  pointwiseDecayCoefficient : ℝ
  pointwiseDecayRate : ℝ
  pointwiseDecayRate_pos : 0 < pointwiseDecayRate
  pointwiseTracelessRicciDecay : ∀ t : Ici (0 : ℝ), ∀ x : M,
    (gt t.1).tracelessRicciNormSqAt x ≤
      pointwiseDecayCoefficient *
        Real.exp ((-pointwiseDecayRate) * t.1)
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

/-- Pointwise exponential decay plus the explicit normalized-flow
volume-preservation inputs produce the finite-energy moving-measure package. -/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasurePointwiseDecayAnalyticData3.toMeasureAnalyticData3
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasurePointwiseDecayAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.{u, v} M :=
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
      normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pointwise_exponential_decay_of_normalizedFlow_Ici
        data.gt data.normalizedFlow data.movingVolumeVariation
          data.energyTrackMeasurable data.pointwiseDecayRate_pos
            data.pointwiseTracelessRicciDecay
    finiteVolumeMeasureContinuous := data.finiteVolumeMeasureContinuous
    scalarJointContinuous := data.scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      data.tracelessRicciNormSqJointContinuous }

/-- The derived finite-energy package reaches the compact mean-energy sphere
endpoint for any unit-curvature recognition input. -/
theorem
    NormalizedFlowSphereCompactMeanEnergyMeasurePointwiseDecayAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasurePointwiseDecayAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toMeasureAnalyticData3.sphereConclusion unitRecognition

/-- One selected smooth atlas carrying pointwise-decay analytic data,
canonical compared-successor stability, and uniformly generated overlap-grid
coherence. -/
structure
    SelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3
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
    NormalizedFlowSphereCompactMeanEnergyMeasurePointwiseDecayAnalyticData3.{u, v}
      M
  comparedJointStability :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
      smoothManifold
    letI : SecondCountableTopology M :=
      selectedClosedSmoothAtlasSecondCountableTopology3 M chartedSpace
    letI : ConnectedSpace M :=
      connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
    ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalComparedSuccessorLocus g ∈
          nhdsSet (successorParameterDiagonal (M := M))
  completion :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
      smoothManifold
    letI : SecondCountableTopology M :=
      selectedClosedSmoothAtlasSecondCountableTopology3 M chartedSpace
    letI : ConnectedSpace M :=
      connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
    ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                Nonempty
                  (UniformRadiusDerivedTerminalGridOverlapCoherence
                    (uniformGenericSuccessorRadiusCertificateOfNeighborhood
                      g
                      (universalSuccessorDataNeighborhood_of_comparedNeighborhood
                        (comparedJointStability g hcurv)))
                    package hcurv hmesh)

/-- Forget the proof-producing pointwise-decay fields after they have derived
finite energy, retaining the same selected atlas and Cartan completion. -/
noncomputable def
    SelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3.toFiniteEnergyPackage
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3.{u, v}
        M) :
    SelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3.{u, v}
      M := by
  letI : ChartedSpace (ClosedSmoothModel 3) M := data.chartedSpace
  letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
    data.smoothManifold
  letI : SecondCountableTopology M :=
    selectedClosedSmoothAtlasSecondCountableTopology3 M data.chartedSpace
  letI : ConnectedSpace M :=
    connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact
    { chartedSpace := data.chartedSpace
      smoothManifold := data.smoothManifold
      analytic := data.analytic.toMeasureAnalyticData3
      comparedJointStability := data.comparedJointStability
      completion := data.completion }

/-- Pointwise exponential traceless-Ricci decay, concrete moving-measure
continuity, and compared-neighborhood uniform-radius Cartan completion imply
the round-sphere conclusion on the selected atlas. -/
theorem
    SelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toFiniteEnergyPackage.sphereConclusion

/-- Universal existence of the strongest concrete selected-atlas package with
pointwise-decay analytic input and provenance-retaining Cartan stability. -/
def
    UniversalSelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3.{u, v}
          M)

/-- A universal pointwise-decay, moving-measure, compared-stability,
uniform-radius selected provider proves the canonical topological Poincare
statement. -/
theorem
    poincareConjectureStatement_of_universalSelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3
    (provider :
      UniversalSelectedSmoothAtlasCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusPackage3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
