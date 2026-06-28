import Poincare.ProofProgress.FiniteExtinctionSweepoutInterfaceBundle

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The remaining finite-extinction production data after a
`FiniteExtinctionWidthSubobligationsStatement` has supplied the target
sweepout, area-functional setup, min-max width theory, width evolution, surgery
discard control, and component-topology frontier.

This compatibility remainder still stores all post-width fields consumed by the
older width bridge. The curvature frontier can now supply the first four fields,
so the remaining upstream obstruction is construction of the width statement
itself.
-/
structure FiniteExtinctionProductionPackageRemainderAfterWidth
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
  /-- Volume evolution formula on smooth intervals. -/
  volumeEvolutionFormula :
    HasFiniteExtinctionVolumeEvolutionFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl
  /-- Nonincrease of volume through surgery and discarded components. -/
  surgeryVolumeNonincrease :
    HasFiniteExtinctionSurgeryVolumeNonincrease
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl
  /-- Scalar-curvature differential inequality used in the extinction bound. -/
  scalarCurvatureDifferentialInequality :
    HasFiniteExtinctionScalarCurvatureDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl
  /-- Volume differential inequality behind the extinction estimate. -/
  volumeDifferentialInequality :
    HasFiniteExtinctionVolumeDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl
  /-- Volume-decay estimate used to bound extinction time. -/
  volumeDecayEstimate :
    HasFiniteExtinctionVolumeDecayEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl
  /-- Time-bound or decay input for finite extinction. -/
  timeBound :
    HasFiniteExtinctionTimeBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl
  /-- Integration of the differential inequality behind the extinction time bound. -/
  differentialInequalityIntegration :
    HasFiniteExtinctionDifferentialInequalityIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound
  /-- Integration of the decay estimate to finite-time extinction. -/
  finiteTimeIntegration :
    HasFiniteExtinctionFiniteTimeIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound
  /-- Summability of surgery-time losses in the extinction estimate. -/
  surgeryTimeSummability :
    HasFiniteExtinctionSurgeryTimeSummability
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound
  /-- Contradiction step forcing extinction by the time bound. -/
  extinctionTimeContradiction :
    HasFiniteExtinctionExtinctionTimeContradiction
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound
  /-- Derivation of finite extinction from the preceding data. -/
  derivation :
    HasFiniteExtinctionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- The finite-extinction conclusion used by the topological assembly layer. -/
  finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M
  /-- Certificate tying the post-width finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
Production bridge after the width frontier: a theorem-shaped width statement
supplies the area-functional setup and every min-max/width/discard-control
field of `FiniteExtinctionSurgeryPackage`; only the post-width curvature,
volume, and conclusion data remain.
-/
theorem finite_extinction_surgery_package_of_width_statement
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
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidth
        analyticFoundation surgeryConstruction perelmanControl) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) := by
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
      sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
      areaFunctional, widthDefinition, widthCompactness,
      widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
      minMaxStationarity, minSurfaceRegularity, positiveWidth, widthTheory,
      firstVariationFormula, secondVariationInequality, gaussBonnetEstimate,
      scalarCurvatureWidthBound, widthEvolution, widthDifferentialInequality,
      surgeryMetricComparison, surgeryWidthComparisonMap, surgeryWidthDrop,
      surgeryDiscardControl, discardedComponentWidthNeutrality,
      discardedComponentSweepoutTriviality, discardedComponentClassification,
      survivingComponentTracking, componentTopology⟩
  exact ⟨
    { analyticFoundation := analyticFoundation
      surgeryConstruction := surgeryConstruction
      perelmanControl := perelmanControl
      extinctionFundamentalGroupInput := finiteFundamentalGroup
      extinctionSweepout := sweepout
      extinctionSweepoutParameterSpace := sweepoutParameterSpace
      extinctionSweepoutContinuity := sweepoutContinuity
      extinctionSweepoutAreaBound := sweepoutAreaBound
      extinctionSweepoutNontriviality := sweepoutNontriviality
      extinctionAreaFunctional := areaFunctional
      extinctionMinMaxWidth := widthDefinition
      extinctionWidthCompactness := widthCompactness
      extinctionWidthLowerSemicontinuity := widthLowerSemicontinuity
      extinctionMinimizingSequence := minimizingSequence
      extinctionPullTightArgument := pullTightArgument
      extinctionMinMaxStationarity := minMaxStationarity
      extinctionMinSurfaceRegularity := minSurfaceRegularity
      extinctionPositiveWidth := positiveWidth
      extinctionWidthTheory := widthTheory
      extinctionFirstVariationFormula := firstVariationFormula
      extinctionSecondVariationInequality := secondVariationInequality
      extinctionGaussBonnetEstimate := gaussBonnetEstimate
      extinctionScalarCurvatureWidthBound := scalarCurvatureWidthBound
      extinctionWidthEvolution := widthEvolution
      extinctionWidthDifferentialInequality := widthDifferentialInequality
      extinctionSurgeryMetricComparison := surgeryMetricComparison
      extinctionSurgeryWidthComparisonMap := surgeryWidthComparisonMap
      extinctionSurgeryWidthDrop := surgeryWidthDrop
      extinctionSurgeryDiscardControl := surgeryDiscardControl
      extinctionDiscardedComponentWidthNeutrality :=
        discardedComponentWidthNeutrality
      extinctionDiscardedComponentSweepoutTriviality :=
        discardedComponentSweepoutTriviality
      extinctionDiscardedComponentClassification :=
        discardedComponentClassification
      extinctionSurvivingComponentTracking := survivingComponentTracking
      extinctionComponentTopology := componentTopology
      extinctionCurvaturePinching := remainder.curvaturePinching
      extinctionPositiveScalarCurvatureLowerBound :=
        remainder.positiveScalarCurvatureLowerBound
      extinctionPositiveScalarCurvaturePersistence :=
        remainder.positiveScalarCurvaturePersistence
      extinctionComponentControl := remainder.componentControl
      extinctionVolumeEvolutionFormula := remainder.volumeEvolutionFormula
      extinctionSurgeryVolumeNonincrease := remainder.surgeryVolumeNonincrease
      extinctionScalarCurvatureDifferentialInequality :=
        remainder.scalarCurvatureDifferentialInequality
      extinctionVolumeDifferentialInequality :=
        remainder.volumeDifferentialInequality
      extinctionVolumeDecayEstimate := remainder.volumeDecayEstimate
      extinctionTimeBound := remainder.timeBound
      extinctionDifferentialInequalityIntegration :=
        remainder.differentialInequalityIntegration
      extinctionFiniteTimeIntegration := remainder.finiteTimeIntegration
      extinctionSurgeryTimeSummability := remainder.surgeryTimeSummability
      extinctionExtinctionTimeContradiction :=
        remainder.extinctionTimeContradiction
      extinctionDerivation := remainder.derivation
      finiteExtinction := remainder.finiteExtinction
      extinctionConclusionDerivation := remainder.conclusionDerivation }⟩

/--
Nonempty package-layer form of the post-width production bridge.
-/
theorem finite_extinction_surgery_package_nonempty_of_width_statement
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
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidth
        analyticFoundation surgeryConstruction perelmanControl) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_of_width_statement
    analyticFoundation surgeryConstruction perelmanControl widthStatement
    remainder

end Poincare
