import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint
import Poincare.Global.NormalizedFlowMeanScalarSelectedSmoothAtlasPoincare
import Poincare.Global.CartanCanonicalRootedReparameterizedDerivedTerminalHomotopyGridAssembly

/-!
# Selected-atlas Poincare route from compact mean-energy data

Finite forward traceless-Ricci energy already selects times with vanishing
energy.  Consequently the analytic half of the selected-atlas route needs no
scalar-variance domination, derivative-sign argument, flow differentiation,
or spatial concentration package.  It is enough to realize every forward
metric in a compact parameter family on which the pair

`(mean scalar, total squared traceless-Ricci energy)`

is continuous, and to retain a positive forward lower bound for the mean
scalar.  This file combines that reduced analytic package with the
reparameterized derived-terminal canonical rooted recognition boundary, in
which boundary predecessor identities are proved from reachable chains.

Continuity of the invariant pair is explicit.  Joint continuity of the two
pointwise curvature densities alone would not control their integrals against
the varying Riemannian volume measures.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanAtlasRootedPathSkeleton
open CartanCanonicalRootedEndpointAssembly

/-- Fixed-target canonical completion with reparameterized boundary
provenance.  Per-overlap certificates retain the realized grid and its mesh
bounds, but no predecessor-state equalities. -/
def FixedTargetCanonicalRootedReparameterizedDerivedTerminalHomotopyGridOverlapCompletion3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        ∀ hcurv : HasConstantSectionalCurvature3 g 1,
          ∃ skeleton : RootedCartanPathSkeleton g,
            ∃ package : CanonicalRootedRealizationPackage skeleton,
              ∃ mesh : ℝ,
                ∃ hmesh : 0 < mesh,
                  Nonempty
                    (CanonicalRootedRealizationPackage.ReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
                      package hcurv hmesh)

/-- Minimal forward analytic data consumed by the compact mean-energy
endpoint on one already selected smooth atlas. -/
structure NormalizedFlowSphereCompactMeanEnergyAnalyticData3
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
  invariantPairContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k))

/-- Fixed-target provider for the minimal compact mean-energy package under
the smooth instances selected downstream. -/
def FixedTargetNormalizedFlowSphereCompactMeanEnergyAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactMeanEnergyAnalyticData3.{u, v} M

/-- Compact mean-energy data construct a unit-curvature metric and then use
only the supplied unit-curvature recognition theorem. -/
theorem NormalizedFlowSphereCompactMeanEnergyAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : NormalizedFlowSphereCompactMeanEnergyAnalyticData3.{u, v} M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  exact
    sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      data.gt data.finiteTracelessRicciEnergy data.metric data.parameter
      data.realizesFlow data.invariantPairContinuous
      data.meanScalarFloor_pos data.meanScalarLower unitRecognition

/-- Eliminate one proof-bearing smooth-transition atlas into the reduced
compact mean-energy endpoint.  Atlas selection remains independent of both
the analytic provider and unit-curvature recognition. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_compactMeanEnergyAnalyticData_of_unitRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereCompactMeanEnergyAnalyticData3.{u, v} M)
    (unitRecognition :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  refine normalizedFlowTarget_elim_of_cInfinityLocalTransitionAtlasData3
    smoothData ?_
  intro _charted _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact analytic.sphereConclusion unitRecognition

/-- The same fixed-target bridge with unit-curvature recognition discharged
by the existing derived-terminal canonical rooted provider. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_compactMeanEnergyAnalyticData_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereCompactMeanEnergyAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedDerivedTerminalHomotopyGridOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_compactMeanEnergyAnalyticData_of_unitRecognition
      smoothData analytic
  intro _charted _smoothManifold _secondCountable _connected
  exact
    CanonicalRootedRealizationPackage.unitConstantCurvatureSphereRecognition3_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
      completion

/-- Fixed-target compact mean-energy bridge through the stronger
reparameterized completion, where both predecessor identities are derived
from reachable-chain boundary provenance. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_compactMeanEnergyAnalyticData_of_canonicalRootedReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereCompactMeanEnergyAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedReparameterizedDerivedTerminalHomotopyGridOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_compactMeanEnergyAnalyticData_of_unitRecognition
      smoothData analytic
  intro _charted _smoothManifold _secondCountable _connected
  exact
    CanonicalRootedRealizationPackage.unitConstantCurvatureSphereRecognition3_of_canonicalRootedReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
      completion

/-- One selected smooth atlas carrying the reduced analytic data and the
reparameterized derived-terminal canonical rooted completion data. -/
structure SelectedSmoothAtlasCompactMeanEnergyCanonicalRootedPackage3
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
    NormalizedFlowSphereCompactMeanEnergyAnalyticData3.{u, v} M
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

/-- The two fields on the selected atlas give the sphere conclusion. -/
theorem SelectedSmoothAtlasCompactMeanEnergyCanonicalRootedPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasCompactMeanEnergyCanonicalRootedPackage3.{u, v} M) :
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

/-- Universal existence of one reduced selected-atlas package on each target
manifold. -/
def UniversalSelectedSmoothAtlasCompactMeanEnergyCanonicalRootedPackage3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasCompactMeanEnergyCanonicalRootedPackage3.{u, v} M)

/-- The reduced compact mean-energy provider proves the repository's
topological Poincare statement. -/
theorem poincareConjectureStatement_of_universalSelectedSmoothAtlasCompactMeanEnergyCanonicalRootedPackage3
    (provider :
      UniversalSelectedSmoothAtlasCompactMeanEnergyCanonicalRootedPackage3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
