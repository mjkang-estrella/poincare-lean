import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterWidth

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The finite-extinction production frontier once curvature pinching has been
supplied for the shared flow/surgery/control data.

This is the first post-width analytic frontier needed by the package: it stores
pinching together with the scalar-curvature and component-control inputs that
depend directly on that pinching datum.
-/
structure FiniteExtinctionProductionCurvatureFrontier
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
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)) :
    Prop where
  /-- Curvature pinching input for finite extinction. -/
  curvaturePinching :
    HasFiniteExtinctionCurvaturePinching
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- Scalar-curvature lower bound extracted from pinching. -/
  positiveScalarCurvatureLowerBound :
    HasFiniteExtinctionPositiveScalarCurvatureLowerBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
  /-- Positive scalar curvature or pinching persistence under surgery. -/
  positiveScalarCurvaturePersistence :
    HasFiniteExtinctionPositiveScalarCurvaturePersistence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
  /-- Component-control input for finite extinction. -/
  componentControl :
    HasFiniteExtinctionComponentControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching

/--
Construct the finite-extinction curvature-pinching interface from the existing
analytic curvature-evolution package, Perelman control package, and
post-surgery pinching estimate.
-/
theorem finite_extinction_curvature_pinching_of_control_frontier
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
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)) :
    HasFiniteExtinctionCurvaturePinching
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control :=
  HasFiniteExtinctionCurvaturePinching.of_perelman_curvature_control
    (ricci_contraction_theory_of_analytic_foundation_package
      analyticFoundation)
    (scalar_curvature_theory_of_analytic_foundation_package
      analyticFoundation)
    (curvature_evolution_of_analytic_foundation_package analyticFoundation)
    (curvature_norm_evolution_inequality_of_analytic_foundation_package
      analyticFoundation)
    perelmanControl.canonicalNeighborhood
    perelmanControl.noLocalCollapsing
    perelmanControl.reducedVolume
    surgeryConstruction.postSurgeryCurvaturePinching

/--
Construct the scalar-curvature lower-bound input attached to a finite-extinction
pinching witness.
-/
theorem finite_extinction_positive_scalar_curvature_lower_bound_of_curvature_pinching
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
    (curvaturePinching :
      HasFiniteExtinctionCurvaturePinching
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) :
    HasFiniteExtinctionPositiveScalarCurvatureLowerBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching :=
  HasFiniteExtinctionPositiveScalarCurvatureLowerBound.of_scalar_curvature_pinching
    (scalar_curvature_theory_of_analytic_foundation_package
      analyticFoundation)
    (scalar_curvature_evolution_equation_of_analytic_foundation_package
      analyticFoundation)
    perelmanControl.reducedVolumePositiveLowerBound

/--
Construct the positive-scalar-curvature persistence input attached to a
finite-extinction pinching witness.
-/
theorem finite_extinction_positive_scalar_curvature_persistence_of_curvature_pinching
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
    (curvaturePinching :
      HasFiniteExtinctionCurvaturePinching
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) :
    HasFiniteExtinctionPositiveScalarCurvaturePersistence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching :=
  HasFiniteExtinctionPositiveScalarCurvaturePersistence.of_post_surgery_pinching
    surgeryConstruction.postSurgeryCurvaturePinching
    surgeryConstruction.postSurgeryCanonicalNeighborhoodPersistence
    perelmanControl.canonicalNeighborhoodPersistenceAcrossScales

/--
Construct the component-control input attached to a finite-extinction pinching
witness.
-/
theorem finite_extinction_component_control_of_curvature_pinching
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
    (curvaturePinching :
      HasFiniteExtinctionCurvaturePinching
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) :
    HasFiniteExtinctionComponentControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching :=
  HasFiniteExtinctionComponentControl.of_canonical_noncollapsing
    perelmanControl.canonicalNeighborhood
    perelmanControl.noLocalCollapsing
    perelmanControl.singularityModelClassification
    surgeryConstruction.postSurgeryNoncollapsing

/--
The curvature frontier is constructible from the already-packaged analytic,
surgery, and Perelman control data.
-/
theorem finite_extinction_curvature_frontier_of_control_frontier
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
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)) :
    FiniteExtinctionProductionCurvatureFrontier
      analyticFoundation surgeryConstruction perelmanControl :=
  let curvaturePinching :=
    finite_extinction_curvature_pinching_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  { curvaturePinching := curvaturePinching
    positiveScalarCurvatureLowerBound :=
      finite_extinction_positive_scalar_curvature_lower_bound_of_curvature_pinching
        analyticFoundation surgeryConstruction perelmanControl
        curvaturePinching
    positiveScalarCurvaturePersistence :=
      finite_extinction_positive_scalar_curvature_persistence_of_curvature_pinching
        analyticFoundation surgeryConstruction perelmanControl
        curvaturePinching
    componentControl :=
      finite_extinction_component_control_of_curvature_pinching
        analyticFoundation surgeryConstruction perelmanControl
        curvaturePinching }

/--
The remaining finite-extinction production data after the width frontier and
the curvature frontier have both been supplied.

The first field here is the next unavailable production input after curvature
pinching and its immediate consequences: the volume evolution formula for the
same flow/surgery/control data.
-/
structure FiniteExtinctionProductionPackageRemainderAfterCurvature
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
  /-- Certificate tying the post-curvature inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      timeBound derivation finiteExtinction

/--
Convert the post-curvature production boundary into the existing post-width
remainder interface.
-/
theorem finite_extinction_production_remainder_after_width_of_curvature_frontier
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
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterCurvature
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    FiniteExtinctionProductionPackageRemainderAfterWidth
      analyticFoundation surgeryConstruction perelmanControl :=
  { curvaturePinching := curvatureFrontier.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      curvatureFrontier.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      curvatureFrontier.positiveScalarCurvaturePersistence
    componentControl := curvatureFrontier.componentControl
    volumeEvolutionFormula := remainder.volumeEvolutionFormula
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
Production bridge after the curvature frontier: the width statement supplies
the sweepout/area/min-max/surgery-discard fields, the curvature frontier supplies
pinching and its immediate dependent data, and only the post-curvature volume,
time-bound, and conclusion data remain.
-/
theorem finite_extinction_surgery_package_nonempty_of_width_statement_and_curvature_frontier
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
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterCurvature
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_width_statement
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    (finite_extinction_production_remainder_after_width_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl curvatureFrontier
      remainder)

end Poincare
