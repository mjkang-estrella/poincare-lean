import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterScalarCurvature

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The finite-extinction production frontier once the volume differential
inequality has been supplied after the width, curvature, volume-evolution,
surgery-volume, and scalar-curvature frontiers.
-/
structure FiniteExtinctionProductionVolumeDifferentialFrontier
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
    (_scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier) :
    Prop where
  /-- Volume differential inequality behind the extinction estimate. -/
  volumeDifferentialInequality :
    HasFiniteExtinctionVolumeDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl

/--
The scalar-curvature frontier closes the volume-differential frontier when
combined with the volume-evolution and surgery-volume frontiers.
-/
theorem finite_extinction_volume_differential_frontier_of_scalar_curvature_frontier
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
    FiniteExtinctionProductionVolumeDifferentialFrontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier :=
  { volumeDifferentialInequality :=
      finite_extinction_volume_differential_inequality_of_scalar_curvature_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier }

/--
The post-volume-differential frontiers also supply the finite-extinction time
bound. The constructor is intentionally tied to the same analytic data as the
volume-decay estimate rather than being a marker.
-/
theorem finite_extinction_time_bound_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    HasFiniteExtinctionTimeBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl :=
  HasFiniteExtinctionTimeBound.of_volume_differential_inputs
    volumeFrontier.volumeEvolutionFormula
    surgeryVolumeFrontier.surgeryVolumeNonincrease
    scalarCurvatureFrontier.scalarCurvatureDifferentialInequality
    volumeDifferentialFrontier.volumeDifferentialInequality

/--
The width statement supplies the component-topology payload needed by the
production derivation interface.
-/
theorem finite_extinction_derivation_of_width_statement
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    HasFiniteExtinctionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control := by
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨_finiteFundamentalGroup, _sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth, widthTheory,
      _firstVariationFormula, _secondVariationInequality, _gaussBonnetEstimate,
      _scalarCurvatureWidthBound, widthEvolution, _widthDifferentialInequality,
      _surgeryMetricComparison, _surgeryWidthComparisonMap, _surgeryWidthDrop,
      surgeryDiscardControl, _discardedComponentWidthNeutrality,
      _discardedComponentSweepoutTriviality, _discardedComponentClassification,
      _survivingComponentTracking, componentTopology⟩
  exact HasFiniteExtinctionDerivation.of_width_component_topology
    widthTheory widthEvolution surgeryDiscardControl componentTopology

/--
The post-volume-differential frontier data and width statement supply the
finite-extinction production certificate consumed by the Ricci-flow interface.
-/
def finite_extinction_production_certificate_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M :=
  { flowEvidence :=
        Nonempty (RicciFlowData ThreeManifoldModelWithCorners n M)
    surgeryEvidence := HasRicciFlowWithSurgery n M
    controlEvidence :=
        HasPerelmanSingularityControl (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
    widthEvidence :=
        FiniteExtinctionWidthSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
    curvatureEvidence :=
        HasFiniteExtinctionCurvaturePinching
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
    timeBoundEvidence :=
        HasFiniteExtinctionTimeBound
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
    derivationEvidence :=
        HasFiniteExtinctionDerivation
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
    flow := ⟨ricci_flow_data_of_analytic_foundation_package analyticFoundation⟩
    surgery := surgeryConstruction.withSurgery
    control := perelmanControl.control
    width := widthStatement
    curvature := curvatureFrontier.curvaturePinching
    timeBound :=
        finite_extinction_time_bound_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier
    derivation :=
        finite_extinction_derivation_of_width_statement
          analyticFoundation surgeryConstruction perelmanControl widthStatement }

/--
The post-volume-differential frontier data and width statement supply the
finite-extinction conclusion certificate consumed by the Ricci-flow interface.
-/
theorem finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    FiniteExtinctionByRicciFlowWithSurgery M :=
  FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
    (finite_extinction_production_certificate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)

/--
The remaining finite-extinction production data after the width, curvature,
volume-evolution, surgery-volume, scalar-curvature, and volume-differential
frontiers have been supplied.

The volume-decay estimate, time bound, differential-inequality integration,
finite-time integration, surgery-time summability, extinction-time
contradiction, and finite-extinction derivation are now produced from the
previous frontiers and width statement; the conclusion-derivation certificate
is also constructible from the same frontier data.
-/
structure FiniteExtinctionProductionPackageRemainderAfterVolumeDifferential
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
    (widthStatement :
      FiniteExtinctionWidthSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    Prop where
  /-- Certificate tying the post-volume-differential inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      (finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier)
      (finite_extinction_derivation_of_width_statement
        analyticFoundation surgeryConstruction perelmanControl widthStatement)
      (finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier)

/--
The post-volume-differential frontiers supply the production volume-decay
estimate: volume evolution on smooth intervals, nonincrease through surgery,
the scalar-curvature differential inequality, and the volume differential
inequality are exactly the constructor data.
-/
theorem finite_extinction_volume_decay_estimate_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    HasFiniteExtinctionVolumeDecayEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl :=
  HasFiniteExtinctionVolumeDecayEstimate.of_volume_differential_inputs
    volumeFrontier.volumeEvolutionFormula
    surgeryVolumeFrontier.surgeryVolumeNonincrease
    scalarCurvatureFrontier.scalarCurvatureDifferentialInequality
    volumeDifferentialFrontier.volumeDifferentialInequality

/--
The post-volume-differential frontiers supply integration of the differential
inequality through the differential inequality itself and the derived
volume-decay estimate.
-/
theorem finite_extinction_differential_inequality_integration_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    HasFiniteExtinctionDifferentialInequalityIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      (finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier) :=
  HasFiniteExtinctionDifferentialInequalityIntegration.of_volume_decay_estimate
    volumeDifferentialFrontier.volumeDifferentialInequality
    (finite_extinction_volume_decay_estimate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)

/--
The post-volume-differential frontiers supply finite-time integration by
integrating the derived volume-decay estimate up to the constructed time bound.
-/
theorem finite_extinction_finite_time_integration_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    HasFiniteExtinctionFiniteTimeIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      (finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier) :=
  HasFiniteExtinctionFiniteTimeIntegration.of_volume_decay_estimate
    (finite_extinction_volume_decay_estimate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)

/--
The post-volume-differential frontiers supply summability of surgery-time
losses from volume nonincrease through surgery and the derived finite-time
integration estimate.
-/
theorem finite_extinction_surgery_time_summability_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    HasFiniteExtinctionSurgeryTimeSummability
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      (finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier) :=
  HasFiniteExtinctionSurgeryTimeSummability.of_finite_time_integration
    surgeryVolumeFrontier.surgeryVolumeNonincrease
    (finite_extinction_finite_time_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)

/-- The volume-differential frontier supplies the terminal extinction evidence bundle. -/
theorem finite_extinction_terminal_evidence_of_volume_differential_frontier
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
        analyticFoundation surgeryConstruction perelmanControl curvatureFrontier)
    (surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier)
    (scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier)
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier scalarCurvatureFrontier) :
    HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
      HasFiniteExtinctionVolumeDecayEstimate
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
      HasFiniteExtinctionFiniteTimeIntegration
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        (finite_extinction_time_bound_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier) ∧
      HasFiniteExtinctionSurgeryTimeSummability
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        (finite_extinction_time_bound_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier) ∧
      FiniteExtinctionByRicciFlowWithSurgery M := by
  exact
    ⟨finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_volume_decay_estimate_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_finite_time_integration_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_surgery_time_summability_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier⟩

/--
The post-volume-differential frontiers supply the contradiction forcing
extinction before the time bound from finite-time integration and surgery-time
summability.
-/
theorem finite_extinction_extinction_time_contradiction_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    HasFiniteExtinctionExtinctionTimeContradiction
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      (finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier) :=
  HasFiniteExtinctionExtinctionTimeContradiction.of_time_bound_estimates
    (finite_extinction_finite_time_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)
    (finite_extinction_surgery_time_summability_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)

/--
The volume-differential frontier data prove the conclusion-derivation
certificate for the finite-extinction witness produced from the same frontier.
-/
theorem finite_extinction_conclusion_derivation_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
      (finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier)
      (finite_extinction_derivation_of_width_statement
        analyticFoundation surgeryConstruction perelmanControl widthStatement)
      (finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier) :=
  HasFiniteExtinctionConclusionDerivation.of_extinction_time_contradiction
    (finite_extinction_volume_decay_estimate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)
    (finite_extinction_differential_inequality_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)
    (finite_extinction_finite_time_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)
    (finite_extinction_surgery_time_summability_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)
    (finite_extinction_extinction_time_contradiction_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)
    (finite_extinction_production_certificate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)
    rfl

/--
The volume-differential frontier exposes the concrete production certificate,
the finite-extinction witness produced from that certificate, and the terminal
conclusion-derivation source whose stored certificate is definitionally the
same certificate.
-/
theorem finite_extinction_conclusion_source_certificate_coherence_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    ∃ productionCertificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ source :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
      source.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          source.conclusionCertificate = finiteExtinction := by
  let productionCertificate :=
    finite_extinction_production_certificate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let finiteExtinction :=
    FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
      productionCertificate
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let derivation :=
    finite_extinction_derivation_of_width_statement
      analyticFoundation surgeryConstruction perelmanControl widthStatement
  let source :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction :=
    { volumeDecayEstimate :=
        finite_extinction_volume_decay_estimate_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier
      differentialInequalityIntegration :=
        finite_extinction_differential_inequality_integration_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier
      finiteTimeIntegration :=
        finite_extinction_finite_time_integration_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier
      surgeryTimeSummability :=
        finite_extinction_surgery_time_summability_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier
      extinctionTimeContradiction :=
        finite_extinction_extinction_time_contradiction_of_volume_differential_frontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier volumeDifferentialFrontier
      conclusionCertificate := productionCertificate
      conclusionEq := rfl }
  exact ⟨productionCertificate, finiteExtinction, timeBound, derivation, source,
    rfl, source.conclusionEq⟩

/--
After the volume-differential frontier, the remaining production package
remainder is constructible from the same frontier data.
-/
theorem finite_extinction_production_remainder_after_volume_differential_of_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    FiniteExtinctionProductionPackageRemainderAfterVolumeDifferential
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier widthStatement volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier :=
  { conclusionDerivation :=
      finite_extinction_conclusion_derivation_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier }

/--
Convert the post-volume-differential production boundary into the existing
post-scalar-curvature remainder interface.
-/
theorem finite_extinction_production_remainder_after_scalar_curvature_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterVolumeDifferential
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier widthStatement volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier) :
    FiniteExtinctionProductionPackageRemainderAfterScalarCurvature
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier :=
  { volumeDifferentialInequality :=
      volumeDifferentialFrontier.volumeDifferentialInequality
    volumeDecayEstimate :=
      finite_extinction_volume_decay_estimate_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    timeBound :=
      finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    differentialInequalityIntegration :=
      finite_extinction_differential_inequality_integration_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    finiteTimeIntegration :=
      finite_extinction_finite_time_integration_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    surgeryTimeSummability :=
      finite_extinction_surgery_time_summability_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    extinctionTimeContradiction :=
      finite_extinction_extinction_time_contradiction_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    derivation :=
      finite_extinction_derivation_of_width_statement
        analyticFoundation surgeryConstruction perelmanControl widthStatement
    finiteExtinction :=
      finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    conclusionDerivation := remainder.conclusionDerivation }

/--
Production bridge after the volume-differential frontier: width supplies the
sweepout/area/min-max/surgery-discard fields, curvature supplies pinching and
component control, previous volume frontiers supply volume evolution and
surgery-volume nonincrease, the scalar frontier supplies the scalar-curvature
differential inequality, the volume-differential frontier supplies the volume
differential inequality, and the volume-decay estimate and time bound are
derived from these frontiers. Integration of the differential inequality,
finite-time integration, surgery-time summability, and the extinction-time
contradiction and finite-extinction derivation are also derived from the
frontier and width-statement data; the finite-extinction conclusion is packaged
from the same named evidence, leaving only the conclusion-derivation data.
-/
theorem finite_extinction_surgery_package_nonempty_of_width_curvature_volume_surgery_volume_scalar_curvature_and_volume_differential_frontiers
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterVolumeDifferential
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier widthStatement volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_width_curvature_volume_surgery_volume_and_scalar_curvature_frontiers
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    scalarCurvatureFrontier
    (finite_extinction_production_remainder_after_scalar_curvature_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier remainder)

/--
The width statement and volume-differential frontier close the remaining
finite-extinction production remainder and construct the surgery package.
-/
theorem finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_width_curvature_volume_surgery_volume_scalar_curvature_and_volume_differential_frontiers
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    scalarCurvatureFrontier volumeDifferentialFrontier
    (finite_extinction_production_remainder_after_volume_differential_of_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier)

/--
The volume-differential frontier data supply a completed surgery package, hence
the theorem-shaped finite-extinction statement.
-/
theorem finite_extinction_statement_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    FiniteExtinctionStatement n M := by
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    scalarCurvatureFrontier volumeDifferentialFrontier with ⟨package⟩
  exact finite_extinction_statement_of_surgery_package package

/-- The volume-differential frontier supplies both the finite-extinction statement and conclusion. -/
theorem finite_extinction_statement_and_conclusion_of_volume_differential_frontier
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
    (volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier) :
    FiniteExtinctionStatement n M ∧
      FiniteExtinctionByRicciFlowWithSurgery M := by
  exact
    ⟨finite_extinction_statement_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier⟩

/--
The scalar-curvature frontier now supplies the volume-differential frontier, so
the finite-extinction surgery package is constructible without a separate
post-scalar-curvature remainder.
-/
theorem finite_extinction_surgery_package_nonempty_of_scalar_curvature_frontier
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
        curvatureFrontier volumeFrontier surgeryVolumeFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    scalarCurvatureFrontier
    (finite_extinction_volume_differential_frontier_of_scalar_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier)

/--
The scalar-curvature frontier closes the volume-differential frontier and then
supplies the theorem-shaped finite-extinction statement through the package.
-/
theorem finite_extinction_statement_of_scalar_curvature_frontier
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
        curvatureFrontier volumeFrontier surgeryVolumeFrontier) :
    FiniteExtinctionStatement n M := by
  rcases finite_extinction_surgery_package_nonempty_of_scalar_curvature_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    scalarCurvatureFrontier with ⟨package⟩
  exact finite_extinction_statement_of_surgery_package package

/--
The surgery-volume frontier now also closes the volume-differential frontier:
the scalar-curvature frontier is produced from the curvature frontier, and the
existing scalar-to-volume bridge supplies the volume differential inequality.
-/
theorem finite_extinction_volume_differential_frontier_of_surgery_volume_frontier
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
    FiniteExtinctionProductionVolumeDifferentialFrontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      (finite_extinction_scalar_curvature_frontier_of_curvature_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier) :=
  finite_extinction_volume_differential_frontier_of_scalar_curvature_frontier
    analyticFoundation surgeryConstruction perelmanControl
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    (finite_extinction_scalar_curvature_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier)

/--
With the scalar-curvature differential inequality constructed from the
curvature frontier, the finite-extinction package is constructible from the
width, curvature, volume-evolution, and surgery-volume frontiers.
-/
theorem finite_extinction_surgery_package_nonempty_of_surgery_volume_frontier
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
        curvatureFrontier volumeFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  let scalarCurvatureFrontier :=
    finite_extinction_scalar_curvature_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
  let volumeDifferentialFrontier :=
    finite_extinction_volume_differential_frontier_of_scalar_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier
  finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier
    scalarCurvatureFrontier volumeDifferentialFrontier

/--
The surgery-volume frontier produces the scalar-curvature and
volume-differential frontiers needed for a completed package, hence the
theorem-shaped finite-extinction statement.
-/
theorem finite_extinction_statement_of_surgery_volume_frontier
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
        curvatureFrontier volumeFrontier) :
    FiniteExtinctionStatement n M := by
  rcases finite_extinction_surgery_package_nonempty_of_surgery_volume_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier with ⟨package⟩
  exact finite_extinction_statement_of_surgery_package package

/--
With surgery-volume nonincrease constructed from the surgery package and
volume-evolution frontier, the finite-extinction package is constructible from
the width, curvature, and volume-evolution frontiers.
-/
theorem finite_extinction_surgery_package_nonempty_of_volume_frontier
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
        curvatureFrontier) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  let surgeryVolumeFrontier :=
    finite_extinction_surgery_volume_frontier_of_volume_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier
  finite_extinction_surgery_package_nonempty_of_surgery_volume_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier surgeryVolumeFrontier

/--
With the volume-evolution frontier constructed from the analytic foundation,
the finite-extinction package is constructible from the width statement and
curvature frontier.
-/
theorem finite_extinction_surgery_package_nonempty_of_curvature_frontier
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
        analyticFoundation surgeryConstruction perelmanControl) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  let volumeFrontier :=
    finite_extinction_volume_evolution_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier
  finite_extinction_surgery_package_nonempty_of_volume_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier volumeFrontier

/--
With the curvature frontier now constructed from the analytic, surgery, and
Perelman control packages, the finite-extinction package is constructible from
the width subobligations statement alone.
-/
theorem finite_extinction_surgery_package_nonempty_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  let curvatureFrontier :=
    finite_extinction_curvature_frontier_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  finite_extinction_surgery_package_nonempty_of_curvature_frontier
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    curvatureFrontier

/--
The same width and control-frontier data do not merely produce a package:
they project both the theorem-shaped finite-extinction statement and the actual
finite-extinction witness for the underlying three-manifold.
-/
theorem finite_extinction_statement_and_conclusion_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    FiniteExtinctionStatement n M ∧
      FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases
      finite_extinction_surgery_package_nonempty_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl
        widthStatement with
    ⟨package⟩
  exact
    ⟨finite_extinction_statement_of_surgery_package package,
      finite_extinction_from_statement_payload_of_surgery_package package⟩

/--
The width statement and control frontier determine the concrete frontier chain,
the production certificate, the finite-extinction witness, and the terminal
conclusion-derivation certificate.
-/
theorem finite_extinction_witness_chain_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
    ∃ volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier,
    ∃ surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier,
    ∃ scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier,
    ∃ volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier,
    ∃ productionCertificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ volumeDifferentialInequality :
      HasFiniteExtinctionVolumeDifferentialInequality
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
      volumeDifferentialInequality =
          volumeDifferentialFrontier.volumeDifferentialInequality ∧
      HasFiniteExtinctionConclusionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction ∧
      FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
        productionCertificate = finiteExtinction := by
  let curvatureFrontier :=
    finite_extinction_curvature_frontier_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  let volumeFrontier :=
    finite_extinction_volume_evolution_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier
  let surgeryVolumeFrontier :=
    finite_extinction_surgery_volume_frontier_of_volume_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier
  let scalarCurvatureFrontier :=
    finite_extinction_scalar_curvature_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
  let volumeDifferentialFrontier :=
    finite_extinction_volume_differential_frontier_of_scalar_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier
  let productionCertificate :=
    finite_extinction_production_certificate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let finiteExtinction :=
    finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let derivation :=
    finite_extinction_derivation_of_width_statement
      analyticFoundation surgeryConstruction perelmanControl widthStatement
  exact
    ⟨curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation,
      volumeDifferentialFrontier.volumeDifferentialInequality, rfl,
      finite_extinction_conclusion_derivation_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      rfl⟩

/--
The width statement and control frontier also expose the terminal source records
behind the constructed finite-extinction evidence chain.
-/
theorem finite_extinction_terminal_source_bundle_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
    ∃ volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier,
    ∃ surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier,
    ∃ scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier,
    ∃ volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier,
    ∃ volumeDifferentialInequality :
      HasFiniteExtinctionVolumeDifferentialInequality
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
      volumeDifferentialInequality =
          volumeDifferentialFrontier.volumeDifferentialInequality ∧
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
      Nonempty
        (FiniteExtinctionVolumeDifferentialInequalitySource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl) ∧
      Nonempty
        (FiniteExtinctionTimeBoundSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl) ∧
      Nonempty
        (FiniteExtinctionVolumeDecayEstimateSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl) ∧
      Nonempty
        (FiniteExtinctionDifferentialInequalityIntegrationSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl timeBound) ∧
      Nonempty
        (FiniteExtinctionFiniteTimeIntegrationSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl timeBound) ∧
      Nonempty
        (FiniteExtinctionSurgeryTimeSummabilitySource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl timeBound) ∧
      Nonempty
        (FiniteExtinctionExtinctionTimeContradictionSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl timeBound) ∧
      Nonempty
        (FiniteExtinctionConclusionDerivationSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
          timeBound derivation finiteExtinction) := by
  let curvatureFrontier :=
    finite_extinction_curvature_frontier_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  let volumeFrontier :=
    finite_extinction_volume_evolution_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier
  let surgeryVolumeFrontier :=
    finite_extinction_surgery_volume_frontier_of_volume_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier
  let scalarCurvatureFrontier :=
    finite_extinction_scalar_curvature_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
  let volumeDifferentialFrontier :=
    finite_extinction_volume_differential_frontier_of_scalar_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let derivation :=
    finite_extinction_derivation_of_width_statement
      analyticFoundation surgeryConstruction perelmanControl widthStatement
  let finiteExtinction :=
    finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let volumeDecay :=
    finite_extinction_volume_decay_estimate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let differentialIntegration :=
    finite_extinction_differential_inequality_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let finiteTimeIntegration :=
    finite_extinction_finite_time_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let surgeryTimeSummability :=
    finite_extinction_surgery_time_summability_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let extinctionTimeContradiction :=
    finite_extinction_extinction_time_contradiction_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let conclusionDerivation :=
    finite_extinction_conclusion_derivation_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  exact
    ⟨curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      volumeDifferentialFrontier.volumeDifferentialInequality, rfl,
      timeBound, derivation, finiteExtinction,
      volumeDifferentialFrontier.volumeDifferentialInequality
        |>.finiteExtinctionVolumeDifferentialInequality_source,
      timeBound.finiteExtinctionTimeBound_source,
      volumeDecay.finiteExtinctionVolumeDecayEstimate_source,
      differentialIntegration.finiteExtinctionDifferentialInequalityIntegration_source,
      finiteTimeIntegration.finiteExtinctionFiniteTimeIntegration_source,
      surgeryTimeSummability.finiteExtinctionSurgeryTimeSummability_source,
      extinctionTimeContradiction.finiteExtinctionExtinctionTimeContradiction_source,
      conclusionDerivation.finiteExtinctionConclusionDerivation_source⟩

/--
The width statement and control frontier expose the concrete production
certificate together with the witness obtained from it, the time-bound and
derivation inputs, and terminal source records whose conclusion certificate is
the same certificate.
-/
theorem finite_extinction_certificate_witness_source_payload_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
    ∃ volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier,
    ∃ surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier,
    ∃ scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier,
    ∃ volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier,
    ∃ productionCertificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ volumeDifferentialSource :
      FiniteExtinctionVolumeDifferentialInequalitySource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ timeBoundSource :
      FiniteExtinctionTimeBoundSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivationSource :
      FiniteExtinctionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ conclusionSource :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
      (volumeDifferentialFrontier.volumeDifferentialInequality
        |>.finiteExtinctionVolumeDifferentialInequality_source) =
          ⟨volumeDifferentialSource⟩ ∧
      timeBound.finiteExtinctionTimeBound_source = ⟨timeBoundSource⟩ ∧
      derivation.finiteExtinctionDerivation_source = ⟨derivationSource⟩ ∧
      conclusionSource.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          productionCertificate = finiteExtinction ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          conclusionSource.conclusionCertificate = finiteExtinction := by
  let curvatureFrontier :=
    finite_extinction_curvature_frontier_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  let volumeFrontier :=
    finite_extinction_volume_evolution_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier
  let surgeryVolumeFrontier :=
    finite_extinction_surgery_volume_frontier_of_volume_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier
  let scalarCurvatureFrontier :=
    finite_extinction_scalar_curvature_frontier_of_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
  let volumeDifferentialFrontier :=
    finite_extinction_volume_differential_frontier_of_scalar_curvature_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier
  let productionCertificate :=
    finite_extinction_production_certificate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let finiteExtinction :=
    FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
      productionCertificate
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let derivation :=
    finite_extinction_derivation_of_width_statement
      analyticFoundation surgeryConstruction perelmanControl widthStatement
  let volumeDifferentialSource :=
    Classical.choice
      (volumeDifferentialFrontier.volumeDifferentialInequality
        |>.finiteExtinctionVolumeDifferentialInequality_source)
  let timeBoundSource :=
    Classical.choice timeBound.finiteExtinctionTimeBound_source
  let derivationSource :=
    Classical.choice derivation.finiteExtinctionDerivation_source
  let volumeDecay :=
    finite_extinction_volume_decay_estimate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let differentialIntegration :=
    finite_extinction_differential_inequality_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let finiteTimeIntegration :=
    finite_extinction_finite_time_integration_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let surgeryTimeSummability :=
    finite_extinction_surgery_time_summability_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let extinctionTimeContradiction :=
    finite_extinction_extinction_time_contradiction_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let conclusionSource :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction :=
    { volumeDecayEstimate := volumeDecay
      differentialInequalityIntegration := differentialIntegration
      finiteTimeIntegration := finiteTimeIntegration
      surgeryTimeSummability := surgeryTimeSummability
      extinctionTimeContradiction := extinctionTimeContradiction
      conclusionCertificate := productionCertificate
      conclusionEq := rfl }
  exact
    ⟨curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation,
      volumeDifferentialSource, timeBoundSource, derivationSource,
      conclusionSource,
      by exact Subsingleton.elim _ _,
      by exact Subsingleton.elim _ _,
      by exact Subsingleton.elim _ _,
      rfl, rfl, rfl⟩

/--
The certificate payload can be pushed one step farther: after destructuring the
frontier witness chain, terminal source bundle, and certificate/source payload,
it exposes concrete downstream sources and coherence back to the terminal
conclusion source.
-/
theorem finite_extinction_downstream_source_coherence_payload_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
    ∃ volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier,
    ∃ surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier,
    ∃ scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier,
    ∃ volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier,
    ∃ productionCertificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ volumeDifferentialSource :
      FiniteExtinctionVolumeDifferentialInequalitySource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ timeBoundSource :
      FiniteExtinctionTimeBoundSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivationSource :
      FiniteExtinctionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ volumeDecaySource :
      FiniteExtinctionVolumeDecayEstimateSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ differentialIntegrationSource :
      FiniteExtinctionDifferentialInequalityIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ finiteTimeIntegrationSource :
      FiniteExtinctionFiniteTimeIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ surgeryTimeSummabilitySource :
      FiniteExtinctionSurgeryTimeSummabilitySource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ extinctionTimeContradictionSource :
      FiniteExtinctionExtinctionTimeContradictionSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ conclusionDerivation :
      HasFiniteExtinctionConclusionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
    ∃ conclusionSource :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
      (volumeDifferentialFrontier.volumeDifferentialInequality
        |>.finiteExtinctionVolumeDifferentialInequality_source) =
          ⟨volumeDifferentialSource⟩ ∧
      timeBound.finiteExtinctionTimeBound_source = ⟨timeBoundSource⟩ ∧
      derivation.finiteExtinctionDerivation_source = ⟨derivationSource⟩ ∧
      conclusionDerivation.finiteExtinctionConclusionDerivation_source =
        ⟨conclusionSource⟩ ∧
      (conclusionSource.volumeDecayEstimate
        |>.finiteExtinctionVolumeDecayEstimate_source) =
        ⟨volumeDecaySource⟩ ∧
      (conclusionSource.differentialInequalityIntegration
        |>.finiteExtinctionDifferentialInequalityIntegration_source) =
        ⟨differentialIntegrationSource⟩ ∧
      (conclusionSource.finiteTimeIntegration
        |>.finiteExtinctionFiniteTimeIntegration_source) =
        ⟨finiteTimeIntegrationSource⟩ ∧
      (conclusionSource.surgeryTimeSummability
        |>.finiteExtinctionSurgeryTimeSummability_source) =
        ⟨surgeryTimeSummabilitySource⟩ ∧
      (conclusionSource.extinctionTimeContradiction
        |>.finiteExtinctionExtinctionTimeContradiction_source) =
        ⟨extinctionTimeContradictionSource⟩ ∧
      conclusionSource.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          productionCertificate = finiteExtinction ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          conclusionSource.conclusionCertificate = finiteExtinction := by
  rcases
      finite_extinction_witness_chain_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases
      finite_extinction_terminal_source_bundle_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases
      finite_extinction_certificate_witness_source_payload_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation,
      volumeDifferentialSource, timeBoundSource, derivationSource,
      conclusionSource, hVolumeDifferentialSource, hTimeBoundSource,
      hDerivationSource, hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩
  let volumeDecaySource :=
    Classical.choice
      conclusionSource.volumeDecayEstimate.finiteExtinctionVolumeDecayEstimate_source
  let differentialIntegrationSource :=
    Classical.choice
      (conclusionSource.differentialInequalityIntegration
        |>.finiteExtinctionDifferentialInequalityIntegration_source)
  let finiteTimeIntegrationSource :=
    Classical.choice
      conclusionSource.finiteTimeIntegration.finiteExtinctionFiniteTimeIntegration_source
  let surgeryTimeSummabilitySource :=
    Classical.choice
      conclusionSource.surgeryTimeSummability.finiteExtinctionSurgeryTimeSummability_source
  let extinctionTimeContradictionSource :=
    Classical.choice
      (conclusionSource.extinctionTimeContradiction
        |>.finiteExtinctionExtinctionTimeContradiction_source)
  let conclusionDerivation :
      HasFiniteExtinctionConclusionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction :=
    ⟨⟨conclusionSource⟩⟩
  exact
    ⟨curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation,
      volumeDifferentialSource, timeBoundSource, derivationSource,
      volumeDecaySource, differentialIntegrationSource,
      finiteTimeIntegrationSource, surgeryTimeSummabilitySource,
      extinctionTimeContradictionSource, conclusionDerivation,
      conclusionSource, hVolumeDifferentialSource, hTimeBoundSource,
      hDerivationSource, rfl, by exact Subsingleton.elim _ _,
      by exact Subsingleton.elim _ _, by exact Subsingleton.elim _ _,
      by exact Subsingleton.elim _ _, by exact Subsingleton.elim _ _,
      hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩

/--
The downstream coherence payload has a compact endpoint form for callers that
only need the production certificate, its finite-extinction witness, the
conclusion source and derivation, and the downstream source records.
-/
theorem finite_extinction_compact_downstream_consequence_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ productionCertificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ volumeDecaySource :
      FiniteExtinctionVolumeDecayEstimateSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ differentialIntegrationSource :
      FiniteExtinctionDifferentialInequalityIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ finiteTimeIntegrationSource :
      FiniteExtinctionFiniteTimeIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ surgeryTimeSummabilitySource :
      FiniteExtinctionSurgeryTimeSummabilitySource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ extinctionTimeContradictionSource :
      FiniteExtinctionExtinctionTimeContradictionSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ conclusionSource :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
    ∃ conclusionDerivation :
      HasFiniteExtinctionConclusionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
      conclusionDerivation.finiteExtinctionConclusionDerivation_source =
        ⟨conclusionSource⟩ ∧
      (conclusionSource.volumeDecayEstimate
        |>.finiteExtinctionVolumeDecayEstimate_source) =
        ⟨volumeDecaySource⟩ ∧
      (conclusionSource.differentialInequalityIntegration
        |>.finiteExtinctionDifferentialInequalityIntegration_source) =
        ⟨differentialIntegrationSource⟩ ∧
      (conclusionSource.finiteTimeIntegration
        |>.finiteExtinctionFiniteTimeIntegration_source) =
        ⟨finiteTimeIntegrationSource⟩ ∧
      (conclusionSource.surgeryTimeSummability
        |>.finiteExtinctionSurgeryTimeSummability_source) =
        ⟨surgeryTimeSummabilitySource⟩ ∧
      (conclusionSource.extinctionTimeContradiction
        |>.finiteExtinctionExtinctionTimeContradiction_source) =
        ⟨extinctionTimeContradictionSource⟩ ∧
      conclusionSource.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          productionCertificate = finiteExtinction ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          conclusionSource.conclusionCertificate = finiteExtinction := by
  rcases
      finite_extinction_downstream_source_coherence_payload_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨curvatureFrontier, _volumeFrontier, _surgeryVolumeFrontier,
      _scalarCurvatureFrontier, _volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation,
      _volumeDifferentialSource, _timeBoundSource, _derivationSource,
      volumeDecaySource, differentialIntegrationSource,
      finiteTimeIntegrationSource, surgeryTimeSummabilitySource,
      extinctionTimeContradictionSource, conclusionDerivation,
      conclusionSource, _hVolumeDifferentialSource, _hTimeBoundSource,
      _hDerivationSource, hConclusionDerivationSource, hVolumeDecaySource,
      hDifferentialIntegrationSource, hFiniteTimeIntegrationSource,
      hSurgeryTimeSummabilitySource, hExtinctionTimeContradictionSource,
      hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩
  exact
    ⟨productionCertificate, finiteExtinction, curvatureFrontier, timeBound,
      derivation, volumeDecaySource, differentialIntegrationSource,
      finiteTimeIntegrationSource, surgeryTimeSummabilitySource,
      extinctionTimeContradictionSource, conclusionSource,
      conclusionDerivation, hConclusionDerivationSource, hVolumeDecaySource,
      hDifferentialIntegrationSource, hFiniteTimeIntegrationSource,
      hSurgeryTimeSummabilitySource, hExtinctionTimeContradictionSource,
      hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩

/--
The compact downstream endpoint can be coupled back to the theorem-shaped
finite-extinction statement: callers get the formal statement, the production
certificate, the certificate witness, and all terminal source-coherence records
in one bundle.
-/
theorem finite_extinction_statement_certificate_source_coherence_bundle_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ _theoremStatement : FiniteExtinctionStatement n M,
    ∃ statementFiniteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ productionCertificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ volumeDecaySource :
      FiniteExtinctionVolumeDecayEstimateSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ differentialIntegrationSource :
      FiniteExtinctionDifferentialInequalityIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ finiteTimeIntegrationSource :
      FiniteExtinctionFiniteTimeIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ surgeryTimeSummabilitySource :
      FiniteExtinctionSurgeryTimeSummabilitySource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ extinctionTimeContradictionSource :
      FiniteExtinctionExtinctionTimeContradictionSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ conclusionSource :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
    ∃ conclusionDerivation :
      HasFiniteExtinctionConclusionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation finiteExtinction,
      statementFiniteExtinction = finiteExtinction ∧
      conclusionDerivation.finiteExtinctionConclusionDerivation_source =
        ⟨conclusionSource⟩ ∧
      (conclusionSource.volumeDecayEstimate
        |>.finiteExtinctionVolumeDecayEstimate_source) =
        ⟨volumeDecaySource⟩ ∧
      (conclusionSource.differentialInequalityIntegration
        |>.finiteExtinctionDifferentialInequalityIntegration_source) =
        ⟨differentialIntegrationSource⟩ ∧
      (conclusionSource.finiteTimeIntegration
        |>.finiteExtinctionFiniteTimeIntegration_source) =
        ⟨finiteTimeIntegrationSource⟩ ∧
      (conclusionSource.surgeryTimeSummability
        |>.finiteExtinctionSurgeryTimeSummability_source) =
        ⟨surgeryTimeSummabilitySource⟩ ∧
      (conclusionSource.extinctionTimeContradiction
        |>.finiteExtinctionExtinctionTimeContradiction_source) =
        ⟨extinctionTimeContradictionSource⟩ ∧
      conclusionSource.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          productionCertificate = finiteExtinction ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          conclusionSource.conclusionCertificate = finiteExtinction := by
  rcases
      finite_extinction_statement_and_conclusion_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨theoremStatement, statementFiniteExtinction⟩
  rcases
      finite_extinction_compact_downstream_consequence_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨productionCertificate, finiteExtinction, curvatureFrontier, timeBound,
      derivation, volumeDecaySource, differentialIntegrationSource,
      finiteTimeIntegrationSource, surgeryTimeSummabilitySource,
      extinctionTimeContradictionSource, conclusionSource,
      conclusionDerivation, hConclusionDerivationSource, hVolumeDecaySource,
      hDifferentialIntegrationSource, hFiniteTimeIntegrationSource,
      hSurgeryTimeSummabilitySource, hExtinctionTimeContradictionSource,
      hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩
  exact
    ⟨theoremStatement, statementFiniteExtinction, productionCertificate,
      finiteExtinction, curvatureFrontier, timeBound, derivation,
      volumeDecaySource, differentialIntegrationSource,
      finiteTimeIntegrationSource, surgeryTimeSummabilitySource,
      extinctionTimeContradictionSource, conclusionSource,
      conclusionDerivation, by exact Subsingleton.elim _ _,
      hConclusionDerivationSource, hVolumeDecaySource,
      hDifferentialIntegrationSource, hFiniteTimeIntegrationSource,
      hSurgeryTimeSummabilitySource, hExtinctionTimeContradictionSource,
      hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩

/--
The width/control-frontier endpoint also returns a concrete surgery package
whose theorem-shaped statement and finite-extinction witness agree with the
production-certificate endpoint and all downstream source-coherence records.
-/
theorem finite_extinction_surgery_package_statement_certificate_source_coherence_bundle_of_width_statement_and_control_frontier
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
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ surgeryPackage : FiniteExtinctionSurgeryPackage n M,
    ∃ theoremStatement : FiniteExtinctionStatement n M,
    ∃ packageFiniteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ productionCertificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
    ∃ certificateFiniteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
    ∃ volumeDecaySource :
      FiniteExtinctionVolumeDecayEstimateSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl,
    ∃ differentialIntegrationSource :
      FiniteExtinctionDifferentialInequalityIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ finiteTimeIntegrationSource :
      FiniteExtinctionFiniteTimeIntegrationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ surgeryTimeSummabilitySource :
      FiniteExtinctionSurgeryTimeSummabilitySource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ extinctionTimeContradictionSource :
      FiniteExtinctionExtinctionTimeContradictionSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound,
    ∃ conclusionSource :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation certificateFiniteExtinction,
    ∃ conclusionDerivation :
      HasFiniteExtinctionConclusionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
        timeBound derivation certificateFiniteExtinction,
      theoremStatement = finite_extinction_statement_of_surgery_package surgeryPackage ∧
      packageFiniteExtinction =
        finite_extinction_from_statement_payload_of_surgery_package surgeryPackage ∧
      packageFiniteExtinction = certificateFiniteExtinction ∧
      conclusionDerivation.finiteExtinctionConclusionDerivation_source =
        ⟨conclusionSource⟩ ∧
      (conclusionSource.volumeDecayEstimate
        |>.finiteExtinctionVolumeDecayEstimate_source) =
        ⟨volumeDecaySource⟩ ∧
      (conclusionSource.differentialInequalityIntegration
        |>.finiteExtinctionDifferentialInequalityIntegration_source) =
        ⟨differentialIntegrationSource⟩ ∧
      (conclusionSource.finiteTimeIntegration
        |>.finiteExtinctionFiniteTimeIntegration_source) =
        ⟨finiteTimeIntegrationSource⟩ ∧
      (conclusionSource.surgeryTimeSummability
        |>.finiteExtinctionSurgeryTimeSummability_source) =
        ⟨surgeryTimeSummabilitySource⟩ ∧
      (conclusionSource.extinctionTimeContradiction
        |>.finiteExtinctionExtinctionTimeContradiction_source) =
        ⟨extinctionTimeContradictionSource⟩ ∧
      conclusionSource.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          productionCertificate = certificateFiniteExtinction ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          conclusionSource.conclusionCertificate = certificateFiniteExtinction := by
  rcases
      finite_extinction_surgery_package_nonempty_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨surgeryPackage⟩
  rcases
      finite_extinction_statement_certificate_source_coherence_bundle_of_width_statement_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement with
    ⟨_theoremStatement, _statementFiniteExtinction, productionCertificate,
      certificateFiniteExtinction, curvatureFrontier, timeBound, derivation,
      volumeDecaySource, differentialIntegrationSource,
      finiteTimeIntegrationSource, surgeryTimeSummabilitySource,
      extinctionTimeContradictionSource, conclusionSource,
      conclusionDerivation, _hStatementFiniteExtinction,
      hConclusionDerivationSource, hVolumeDecaySource,
      hDifferentialIntegrationSource, hFiniteTimeIntegrationSource,
      hSurgeryTimeSummabilitySource, hExtinctionTimeContradictionSource,
      hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩
  let theoremStatement := finite_extinction_statement_of_surgery_package surgeryPackage
  let packageFiniteExtinction :=
    finite_extinction_from_statement_payload_of_surgery_package surgeryPackage
  exact
    ⟨surgeryPackage, theoremStatement, packageFiniteExtinction,
      productionCertificate, certificateFiniteExtinction, curvatureFrontier,
      timeBound, derivation, volumeDecaySource, differentialIntegrationSource,
      finiteTimeIntegrationSource, surgeryTimeSummabilitySource,
      extinctionTimeContradictionSource, conclusionSource,
      conclusionDerivation, rfl, rfl, by exact Subsingleton.elim _ _,
      hConclusionDerivationSource, hVolumeDecaySource,
      hDifferentialIntegrationSource, hFiniteTimeIntegrationSource,
      hSurgeryTimeSummabilitySource, hExtinctionTimeContradictionSource,
      hConclusionCertificate, hProductionCertificateEq,
      hConclusionCertificateEq⟩

/-- Theorem contract for `finite_extinction_surgery_package_statement_certificate_source_coherence_bundle_of_width_statement_and_control_frontier`. -/
theorem finite_extinction_surgery_package_statement_certificate_source_coherence_bundle_of_width_statement_and_control_frontier_eq :
    @Poincare.finite_extinction_surgery_package_statement_certificate_source_coherence_bundle_of_width_statement_and_control_frontier =
      @Poincare.finite_extinction_surgery_package_statement_certificate_source_coherence_bundle_of_width_statement_and_control_frontier :=
  rfl

end Poincare
