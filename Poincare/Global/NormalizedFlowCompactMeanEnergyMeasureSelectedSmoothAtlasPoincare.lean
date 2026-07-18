import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity
import Poincare.Global.NormalizedFlowCompactMeanEnergySelectedSmoothAtlasPoincare

/-!
# Selected-atlas Poincare route from measure-continuous compact mean-energy data

This file replaces the abstract continuity assumption on the compact
mean-energy invariant pair by concrete analytic inputs:

* weak continuity of the finite Riemannian volume measures;
* joint continuity of scalar curvature; and
* joint continuity of squared traceless-Ricci norm.

The moving-measure continuity theorem converts those inputs to the weaker
pair-continuity package already consumed by the compact mean-energy endpoint.
The selected-atlas and canonical-rooted recognition layers are then reused
without change.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanAtlasRootedPathSkeleton
open CartanCanonicalRootedEndpointAssembly

/-- Concrete compact mean-energy data on one selected smooth atlas.

Unlike `NormalizedFlowSphereCompactMeanEnergyAnalyticData3`, this record does
not assume continuity of an already-integrated invariant pair.  It records
weak continuity of the bundled finite volume measures and joint continuity of
the two pointwise curvature integrands from which that pair is derived. -/
structure NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3
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
  finiteTracelessRicciEnergy :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0)
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

/-- The concrete moving-measure hypotheses produce exactly the weaker
pair-continuity package consumed by the existing compact mean-energy
endpoint. -/
noncomputable def
    NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.toCompactMeanEnergyAnalyticData3
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.{u, v} M) :
    NormalizedFlowSphereCompactMeanEnergyAnalyticData3.{u, v} M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  have hInvariantPair :
      Continuous
        (fun k ↦ closedMetricMeanTracelessEnergyPair (data.metric k)) :=
    continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint
      data.metric data.finiteVolumeMeasureContinuous
      data.scalarJointContinuous data.tracelessRicciNormSqJointContinuous
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
      finiteTracelessRicciEnergy := data.finiteTracelessRicciEnergy
      invariantPairContinuous := hInvariantPair }

/-- The concrete measure-continuity analytic package reaches the same sphere
endpoint as its pair-continuity target. -/
theorem NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.{u, v} M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toCompactMeanEnergyAnalyticData3.sphereConclusion unitRecognition

/-- One selected smooth atlas carrying concrete moving-measure analytic data
and the reparameterized derived-terminal canonical-rooted completion data. -/
structure SelectedSmoothAtlasCompactMeanEnergyMeasureCanonicalRootedPackage3
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
                  (CanonicalRootedRealizationPackage.ReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
                    package hcurv hmesh)

/-- The concrete analytic fields and reparameterized canonical-rooted field
on one selected atlas imply the round-sphere conclusion. -/
theorem SelectedSmoothAtlasCompactMeanEnergyMeasureCanonicalRootedPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasCompactMeanEnergyMeasureCanonicalRootedPackage3.{u, v} M) :
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
    CanonicalRootedRealizationPackage.unitConstantCurvatureSphereRecognition3_of_canonicalRootedReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
      data.completion
  exact data.analytic.sphereConclusion unitRecognition

/-- Universal existence of the concrete selected-atlas measure-continuity
package on every target manifold. -/
def UniversalSelectedSmoothAtlasCompactMeanEnergyMeasureCanonicalRootedPackage3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasCompactMeanEnergyMeasureCanonicalRootedPackage3.{u, v} M)

/-- A universal concrete measure-continuity provider proves the repository's
canonical topological Poincare statement. -/
theorem poincareConjectureStatement_of_universalSelectedSmoothAtlasCompactMeanEnergyMeasureCanonicalRootedPackage3
    (provider :
      UniversalSelectedSmoothAtlasCompactMeanEnergyMeasureCanonicalRootedPackage3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
