import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterVolume

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The finite-extinction production frontier once surgery-volume nonincrease has
been supplied after the width, curvature, and volume-evolution frontiers.
-/
structure FiniteExtinctionProductionSurgeryVolumeFrontier
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl)
    (_volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    Prop where
  /-- Nonincrease of volume through surgery and discarded components. -/
  surgeryVolumeNonincrease :
    HasFiniteExtinctionSurgeryVolumeNonincrease
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl

/--
The surgery construction package and volume-evolution frontier supply
nonincrease of volume across surgery times for the same controlled components.
-/
theorem finite_extinction_surgery_volume_nonincrease_of_volume_frontier
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl)
    (volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    HasFiniteExtinctionSurgeryVolumeNonincrease
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl :=
  HasFiniteExtinctionSurgeryVolumeNonincrease.of_surgery_metric_volume_inputs
    surgeryConstruction.neckDecomposition
    surgeryConstruction.capMetricInterpolation
    surgeryConstruction.metricControl
    surgeryConstruction.surgeryTimeLocalFiniteness
    volumeFrontier.volumeEvolutionFormula

/--
After the volume-evolution frontier, the surgery-volume frontier is produced
from the construction package's surgery geometry and metric-control inputs.
-/
theorem finite_extinction_surgery_volume_frontier_of_volume_frontier
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl)
    (volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    FiniteExtinctionProductionSurgeryVolumeFrontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier :=
  { surgeryVolumeNonincrease :=
      finite_extinction_surgery_volume_nonincrease_of_volume_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier }

/--
The remaining finite-extinction production data after the width, curvature,
volume-evolution, and surgery-volume frontiers have been supplied.

The first field here is the next unavailable production input: the scalar-
curvature differential inequality used in the extinction estimate.
-/
structure FiniteExtinctionProductionPackageRemainderAfterSurgeryVolume
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl) :
    Prop where
  /-- Scalar-curvature differential inequality used in the extinction bound. -/
  scalarCurvatureDifferentialInequality :
    HasFiniteExtinctionScalarCurvatureDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
  /-- Volume differential inequality behind the extinction estimate. -/
  volumeDifferentialInequality :
    HasFiniteExtinctionVolumeDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
  /-- Volume-decay estimate used to bound extinction time. -/
  volumeDecayEstimate :
    HasFiniteExtinctionVolumeDecayEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
  /-- Time-bound or decay input for finite extinction. -/
  timeBound :
    HasFiniteExtinctionTimeBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
  /-- Integration of the differential inequality behind the extinction time bound. -/
  differentialInequalityIntegration :
    HasFiniteExtinctionDifferentialInequalityIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound
  /-- Integration of the decay estimate to finite-time extinction. -/
  finiteTimeIntegration :
    HasFiniteExtinctionFiniteTimeIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound
  /-- Summability of surgery-time losses in the extinction estimate. -/
  surgeryTimeSummability :
    HasFiniteExtinctionSurgeryTimeSummability
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound
  /-- Contradiction step forcing extinction by the time bound. -/
  extinctionTimeContradiction :
    HasFiniteExtinctionExtinctionTimeContradiction
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound
  /-- Derivation of finite extinction from the preceding data. -/
  derivation :
    HasFiniteExtinctionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- The finite-extinction conclusion used by the topological assembly layer. -/
  finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M
  /-- Certificate tying the post-surgery-volume inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound derivation finiteExtinction

/--
Convert the post-surgery-volume production boundary into the existing
post-volume remainder interface.
-/
theorem finite_extinction_production_remainder_after_volume_of_surgery_volume_frontier
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl)
    (volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier)
    (surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryVolume
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    FiniteExtinctionProductionPackageRemainderAfterVolume
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier :=
  { surgeryVolumeNonincrease :=
      surgeryVolumeFrontier.surgeryVolumeNonincrease
    scalarCurvatureDifferentialInequality :=
      remainder.scalarCurvatureDifferentialInequality
    volumeDifferentialInequality := remainder.volumeDifferentialInequality
    volumeDecayEstimate := remainder.volumeDecayEstimate
    timeBound := remainder.timeBound
    differentialInequalityIntegration :=
      remainder.differentialInequalityIntegration
    finiteTimeIntegration := remainder.finiteTimeIntegration
    surgeryTimeSummability := remainder.surgeryTimeSummability
    extinctionTimeContradiction := remainder.extinctionTimeContradiction
    derivation := remainder.derivation
    finiteExtinction := remainder.finiteExtinction
    conclusionDerivation := remainder.conclusionDerivation }

/--
Production bridge after the surgery-volume frontier: width supplies the
sweepout/area/min-max/surgery-discard fields, the curvature frontier supplies
pinching and component control, the volume frontier supplies volume evolution,
the surgery-volume frontier supplies volume nonincrease across surgeries, and
only the post-surgery-volume scalar/volume/time-bound and conclusion data
remain.
-/
theorem finite_extinction_surgery_package_nonempty_of_width_curvature_volume_and_surgery_volume_frontiers
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (widthStatement :
      FiniteExtinctionWidthSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl)
    (volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier)
    (surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryVolume
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_width_curvature_and_volume_frontiers
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier
    (finite_extinction_production_remainder_after_volume_of_surgery_volume_frontier
      analyticFoundation surgeryConstruction perelmanControl curvatureFrontier
      volumeFrontier surgeryVolumeFrontier remainder)

/--
The post-surgery-volume production boundary supplies not only a fixed-index
surgery package, but also the package-layer sigma target and the concrete
finite-extinction conclusion with its derivation certificate.
-/
theorem finite_extinction_package_layer_target_and_conclusion_of_width_curvature_volume_and_surgery_volume_frontiers
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (widthStatement :
      FiniteExtinctionWidthSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl)
    (volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier)
    (surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryVolume
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
      FiniteExtinctionByRicciFlowWithSurgery M ∧
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control ∧
      HasFiniteExtinctionConclusionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        remainder.timeBound remainder.derivation remainder.finiteExtinction := by
  rcases finite_extinction_surgery_package_nonempty_of_width_curvature_volume_and_surgery_volume_frontiers
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier remainder with
    ⟨package⟩
  exact
    ⟨ ⟨⟨n, package⟩⟩
    , remainder.finiteExtinction
    , remainder.derivation
    , remainder.conclusionDerivation
    ⟩

end Poincare
