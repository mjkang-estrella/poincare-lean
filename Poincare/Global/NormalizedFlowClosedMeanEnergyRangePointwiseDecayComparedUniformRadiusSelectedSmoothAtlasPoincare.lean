import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyDecay
import Poincare.Global.NormalizedFlowClosedMeanEnergyRangeComparedUniformRadiusSelectedSmoothAtlasPoincare

/-!
# Closed-range selected-atlas Poincare route from pointwise decay

This route has neither an auxiliary compact metric-parameter space nor
moving-measure continuity assumptions.  Compactness of the actual forward
invariant-pair range is recovered from its closedness, finite total
traceless-Ricci energy, and two-sided mean-scalar bounds.

The finite-energy field is itself removed here.  It is proved from a forward
normalized Ricci flow, the explicit moving-volume first-variation identity,
measurability of the total energy track, and positive-rate pointwise
exponential traceless-Ricci decay.  The Cartan completion retains canonical
compared-successor provenance and computes all realized grids from one
derived uniform generic successor radius.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

open CartanAtlasRootedPathSkeleton
open CartanCanonicalFamilyComparedToGenericSuccessorRadius
open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly.CanonicalRootedRealizationPackage
open CartanTargetExponential

/-- Closed actual forward invariant-range data whose finite energy is derived
from pointwise exponential traceless-Ricci decay along a normalized flow. -/
structure NormalizedFlowSphereClosedMeanEnergyRangePointwiseDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
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
  forwardMeanEnergyRangeClosed : IsClosed
    (Set.range (fun t : Ici (0 : ℝ) ↦
      closedMetricMeanTracelessEnergyPair (gt t.1)))
  meanScalarFloor : ℝ
  meanScalarFloor_pos : 0 < meanScalarFloor
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  meanScalarCeiling : ℝ
  meanScalarUpper : ∀ t : Ici (0 : ℝ),
    meanScalar (gt t.1) ≤ meanScalarCeiling

/-- The pointwise decay and volume-preservation inputs prove the raw finite
energy field required by the closed-range endpoint. -/
noncomputable def
    NormalizedFlowSphereClosedMeanEnergyRangePointwiseDecayAnalyticData3.toClosedRangeAnalyticData3
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereClosedMeanEnergyRangePointwiseDecayAnalyticData3 M) :
    NormalizedFlowSphereClosedMeanEnergyRangeAnalyticData3 M :=
  { gt := data.gt
    finiteTracelessRicciEnergy :=
      normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pointwise_exponential_decay_of_normalizedFlow_Ici
        data.gt data.normalizedFlow data.movingVolumeVariation
          data.energyTrackMeasurable data.pointwiseDecayRate_pos
            data.pointwiseTracelessRicciDecay
    forwardMeanEnergyRangeClosed := data.forwardMeanEnergyRangeClosed
    meanScalarFloor := data.meanScalarFloor
    meanScalarFloor_pos := data.meanScalarFloor_pos
    meanScalarLower := data.meanScalarLower
    meanScalarCeiling := data.meanScalarCeiling
    meanScalarUpper := data.meanScalarUpper }

/-- The derived finite-energy closed-range package reaches the sphere
endpoint from any supplied unit-curvature recognition theorem. -/
theorem
    NormalizedFlowSphereClosedMeanEnergyRangePointwiseDecayAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      NormalizedFlowSphereClosedMeanEnergyRangePointwiseDecayAnalyticData3 M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toClosedRangeAnalyticData3.sphereConclusion unitRecognition

/-- One selected smooth atlas carrying the no-parameter-space pointwise-decay
closed-range analytic data and compared-family uniform-radius completion. -/
structure
    SelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3
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
    NormalizedFlowSphereClosedMeanEnergyRangePointwiseDecayAnalyticData3 M
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

/-- After deriving finite energy, forget only the proof-producing decay fields
and retain the same selected atlas, closed range, and Cartan completion. -/
noncomputable def
    SelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3.toFiniteEnergyPackage
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3
        M) :
    SelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3 M := by
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
      analytic := data.analytic.toClosedRangeAnalyticData3
      comparedJointStability := data.comparedJointStability
      completion := data.completion }

/-- Pointwise exponential traceless-Ricci decay, a closed actual forward
invariant range with two-sided mean bounds, and compared-neighborhood
uniform-radius Cartan completion imply the round-sphere conclusion. -/
theorem
    SelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toFiniteEnergyPackage.sphereConclusion

/-- Universal existence of the no-parameter-space, no-moving-measure,
pointwise-decay closed-range selected package. -/
def
    UniversalSelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3
          M)

/-- A universal pointwise-decay closed-range, compared-family uniform-radius
provider proves the canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalSelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3
    (provider :
      UniversalSelectedSmoothAtlasClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusPackage3.{u}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
