import Poincare.Global.CartanCanonicalFamilyComparedToGenericSuccessorRadius
import Poincare.Global.CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureSelectedSmoothAtlasPoincare

/-!
# Selected-atlas Poincare route from compared canonical stability

This file combines the concrete moving-measure compact mean-energy endpoint
with the strongest current canonical-rooted Cartan assembly.  Its stability
input is the provenance-retaining canonical compared-successor locus near the
full parameter diagonal.  Forgetting the provenance derives one uniform
generic successor radius.  Every realized overlap grid is then computed from
that radius and four finite geometric fields.

In particular, the selected package below stores no row-chain, rung,
cross-cell, or boundary-predecessor data.
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

/-- One selected smooth atlas carrying concrete moving-measure analytic data,
canonical compared-successor stability at the whole parameter diagonal, and
only the remaining finite geometry/feedback data for uniformly generated
reparameterized overlap grids. -/
structure
    SelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3
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
    NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.{u, v} M
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

/-- The compared canonical neighborhood is forgotten to generic successor
data, uniformly realized grids provide the restricted compatible Cartan
atlas, and the concrete compact mean-energy endpoint concludes roundness. -/
theorem
    SelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3.{u, v}
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

/-- Universal existence of the concrete selected-atlas package whose Cartan
input retains canonical-family provenance but no realized grid payload. -/
def
    UniversalSelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3.{u, v}
          M)

/-- A universal moving-measure, compared-stability, uniform-radius selected
provider proves the repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalSelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3
    (provider :
      UniversalSelectedSmoothAtlasCompactMeanEnergyMeasureComparedUniformRadiusPackage3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
