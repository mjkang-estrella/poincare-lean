import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterSurgeryVolume

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The finite-extinction production frontier once the scalar-curvature differential
inequality has been supplied after the width, curvature, volume-evolution, and
surgery-volume frontiers.
-/
structure FiniteExtinctionProductionScalarCurvatureFrontier
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
    (_surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier) :
    Prop where
  /-- Scalar-curvature differential inequality used in the extinction bound. -/
  scalarCurvatureDifferentialInequality :
    HasFiniteExtinctionScalarCurvatureDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl

/--
The curvature frontier already contains the lower-bound, persistence, and
component-control inputs needed for the scalar-curvature differential
inequality interface.
-/
theorem finite_extinction_scalar_curvature_differential_inequality_of_curvature_frontier
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
    HasFiniteExtinctionScalarCurvatureDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl :=
  HasFiniteExtinctionScalarCurvatureDifferentialInequality.of_positive_scalar_curvature_inputs
    curvatureFrontier.positiveScalarCurvatureLowerBound
    curvatureFrontier.positiveScalarCurvaturePersistence

/--
After the surgery-volume frontier, the scalar-curvature frontier is produced
from the curvature frontier's scalar lower-bound and persistence inputs.
-/
theorem finite_extinction_scalar_curvature_frontier_of_curvature_frontier
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
        curvatureFrontier volumeFrontier) :
    FiniteExtinctionProductionScalarCurvatureFrontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier :=
  { scalarCurvatureDifferentialInequality :=
      finite_extinction_scalar_curvature_differential_inequality_of_curvature_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier }

/--
The remaining finite-extinction production data after the width, curvature,
volume-evolution, surgery-volume, and scalar-curvature frontiers have been
supplied.

This compatibility remainder still stores the post-scalar data expected by
older bridges; the volume differential inequality itself is now produced below
from the scalar-curvature, volume-evolution, and surgery-volume frontiers.
-/
structure FiniteExtinctionProductionPackageRemainderAfterScalarCurvature
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
  /-- Certificate tying the post-scalar-curvature inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound derivation finiteExtinction

/--
The scalar-curvature frontier supplies the volume differential inequality once
the smooth volume-evolution and surgery-volume frontiers are available.
-/
theorem finite_extinction_volume_differential_inequality_of_scalar_curvature_frontier
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
    (scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier) :
    HasFiniteExtinctionVolumeDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl :=
  HasFiniteExtinctionVolumeDifferentialInequality.of_volume_scalar_inputs
    volumeFrontier.volumeEvolutionFormula
    surgeryVolumeFrontier.surgeryVolumeNonincrease
    scalarCurvatureFrontier.scalarCurvatureDifferentialInequality

/--
Convert the post-scalar-curvature production boundary into the existing
post-surgery-volume remainder interface.
-/
theorem finite_extinction_production_remainder_after_surgery_volume_of_scalar_curvature_frontier
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
    (scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterScalarCurvature
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    FiniteExtinctionProductionPackageRemainderAfterSurgeryVolume
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier :=
  { scalarCurvatureDifferentialInequality :=
      scalarCurvatureFrontier.scalarCurvatureDifferentialInequality
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
Production bridge after the scalar-curvature frontier: width supplies the
sweepout/area/min-max/surgery-discard fields, curvature supplies pinching and
component control, volume frontiers supply volume evolution and surgery-volume
nonincrease, the scalar frontier supplies the scalar-curvature differential
inequality, and the volume differential inequality is now produced from those
frontiers by `finite_extinction_volume_differential_inequality_of_scalar_curvature_frontier`.
-/
theorem finite_extinction_surgery_package_nonempty_of_width_curvature_volume_surgery_volume_and_scalar_curvature_frontiers
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
    (scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterScalarCurvature
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_width_curvature_volume_and_surgery_volume_frontiers
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    (finite_extinction_production_remainder_after_surgery_volume_of_scalar_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl curvatureFrontier
      volumeFrontier surgeryVolumeFrontier scalarCurvatureFrontier remainder)

end Poincare
