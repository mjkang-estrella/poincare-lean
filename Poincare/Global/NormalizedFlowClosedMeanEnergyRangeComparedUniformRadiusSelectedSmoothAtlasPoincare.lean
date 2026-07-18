import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyClosedInvariantRangeEndpoint
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureComparedUniformRadiusSelectedSmoothAtlasPoincare

/-!
# Selected-atlas Poincare route from a closed forward invariant range

This route removes the compact metric-parameter space and moving-measure
continuity fields from the analytic package.  It asks instead that the actual
forward range of `(mean scalar, total traceless-Ricci energy)` be closed, with
the mean scalar bounded between a positive floor and a finite ceiling.

The Cartan side retains the strongest compared-family uniform-radius
assembly: generic successor data are derived from canonical compared
successors, and no realized row, rung, cross-cell, or predecessor payload is
stored in the selected package.
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

/-- Minimal closed-range analytic data on one selected smooth atlas. -/
structure NormalizedFlowSphereClosedMeanEnergyRangeAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  finiteTracelessRicciEnergy :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0)
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

/-- Closed-range analytic data reach the sphere endpoint from any supplied
unit-curvature recognition theorem. -/
theorem NormalizedFlowSphereClosedMeanEnergyRangeAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : NormalizedFlowSphereClosedMeanEnergyRangeAnalyticData3 M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
    data.gt data.finiteTracelessRicciEnergy
      data.forwardMeanEnergyRangeClosed data.meanScalarFloor_pos
      data.meanScalarLower data.meanScalarUpper unitRecognition

/-- One selected smooth atlas carrying the closed-range analytic data and the
compared-family uniform-radius Cartan completion. -/
structure SelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3
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
    NormalizedFlowSphereClosedMeanEnergyRangeAnalyticData3 M
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

/-- The closed-range analytic package and the compared-family uniform-radius
Cartan package imply the round-sphere conclusion. -/
theorem
    SelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3 M) :
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
  let jointStability :=
    fun (g : ClosedSmoothRiemannianMetric 3 M)
      (hcurv : HasConstantSectionalCurvature3 g 1) ↦
        universalSuccessorDataNeighborhood_of_comparedNeighborhood
          (data.comparedJointStability g hcurv)
  have unitRecognition : UnitConstantCurvatureSphereRecognition3 M :=
    unitConstantCurvatureSphereRecognition3_of_canonicalRootedReparameterizedUniformRadiusGridOverlapCoherence
      jointStability (by
        intro g hcurv
        simpa only [jointStability] using data.completion g hcurv)
  exact data.analytic.sphereConclusion unitRecognition

/-- Universal existence of the closed-range, compared-family selected
package. -/
def UniversalSelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3 M)

/-- A universal closed-range, compared-family uniform-radius provider proves
the canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalSelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3
    (provider :
      UniversalSelectedSmoothAtlasClosedMeanEnergyRangeComparedUniformRadiusPackage3.{u}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
