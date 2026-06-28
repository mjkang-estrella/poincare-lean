import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterCurvature

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The finite-extinction production frontier once the volume evolution formula has
been supplied for the shared flow/surgery/control data after the curvature
frontier.
-/
structure FiniteExtinctionProductionVolumeEvolutionFrontier
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
  /-- Volume evolution formula on smooth intervals. -/
  volumeEvolutionFormula :
    HasFiniteExtinctionVolumeEvolutionFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl

/--
The analytic foundation package supplies the metric time-derivative,
Ricci-flow equation, scalar-curvature theory, and evolution-equation inputs
needed for the smooth-interval finite-extinction volume evolution formula.
-/
theorem finite_extinction_volume_evolution_formula_of_curvature_frontier
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
    HasFiniteExtinctionVolumeEvolutionFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl :=
  HasFiniteExtinctionVolumeEvolutionFormula.of_analytic_volume_evolution_inputs
    (metric_regularity_of_analytic_foundation_package analyticFoundation)
    (metric_time_derivative_of_analytic_foundation_package analyticFoundation)
    (scalar_curvature_theory_of_analytic_foundation_package analyticFoundation)
    (equation_derivation_of_analytic_foundation_package analyticFoundation)
    (metric_evolution_equation_of_analytic_foundation_package analyticFoundation)
    (scalar_curvature_evolution_equation_of_analytic_foundation_package
      analyticFoundation)

/--
After the curvature frontier, the volume-evolution frontier is produced from
the analytic foundation package's Ricci-flow equation and scalar-evolution
inputs.
-/
theorem finite_extinction_volume_evolution_frontier_of_curvature_frontier
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
    FiniteExtinctionProductionVolumeEvolutionFrontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier :=
  { volumeEvolutionFormula :=
      finite_extinction_volume_evolution_formula_of_curvature_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier }

/--
The remaining finite-extinction production data after the width, curvature, and
volume-evolution frontiers have been supplied.

The first field here is the next unavailable production input after the volume
evolution formula: nonincrease of volume through surgery and discarded
components. The later fields in the current API depend on the curvature
frontier, not on the volume-evolution witness itself.
-/
structure FiniteExtinctionProductionPackageRemainderAfterVolume
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
  /-- Nonincrease of volume through surgery and discarded components. -/
  surgeryVolumeNonincrease :
    HasFiniteExtinctionSurgeryVolumeNonincrease
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
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
  /-- Certificate tying the post-volume inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound derivation finiteExtinction

/--
Convert the post-volume production boundary into the existing post-curvature
remainder interface.
-/
theorem finite_extinction_production_remainder_after_curvature_of_volume_frontier
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
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterVolume
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    FiniteExtinctionProductionPackageRemainderAfterCurvature
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier :=
  { volumeEvolutionFormula := volumeFrontier.volumeEvolutionFormula
    surgeryVolumeNonincrease := remainder.surgeryVolumeNonincrease
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
Production bridge after the volume-evolution frontier: width supplies the
sweepout/area/min-max/surgery-discard fields, the curvature frontier supplies
pinching and component control, the volume frontier supplies the volume
evolution formula, and only the post-volume surgery-volume, time-bound, and
conclusion data remain.
-/
theorem finite_extinction_surgery_package_nonempty_of_width_curvature_and_volume_frontiers
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
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterVolume
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_width_statement_and_curvature_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier
    (finite_extinction_production_remainder_after_curvature_of_volume_frontier
      analyticFoundation surgeryConstruction perelmanControl curvatureFrontier
      volumeFrontier remainder)

end Poincare
