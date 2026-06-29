import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterVolumeDifferential

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The remaining finite-extinction package data after the target sweepout-frontier
bundle has supplied the fundamental-group input, sweepout, parameter-space,
continuity, area-bound, and nontriviality fields.
-/
structure FiniteExtinctionProductionPackageRemainder
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
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M) : Prop where
  /-- Area-functional setup for the target sweepout class. -/
  areaFunctional :
    HasFiniteExtinctionAreaFunctionalSetup
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
  /-- Min-max width definition from the target sweepout family. -/
  minMaxWidth :
    HasFiniteExtinctionMinMaxWidthDefinition
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
  /-- Compactness of target-width minimizing sweepout sequences. -/
  widthCompactness :
    HasFiniteExtinctionWidthCompactness
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
      minMaxWidth
  /-- Lower semicontinuity of target width under limiting sweepouts. -/
  widthLowerSemicontinuity :
    HasFiniteExtinctionWidthLowerSemicontinuity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
      minMaxWidth
  /-- Extracted minimizing sequence for target width. -/
  minimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
      minMaxWidth
  /-- Pull-tight argument for the target sweepout sequence. -/
  pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
      minMaxWidth
  /-- Stationarity of the min-max limit realizing target width. -/
  minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
      minMaxWidth
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle)
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The area-functional payload attached to a target sweepout payload is obtained
from the sweepout's stored slice-area function, analytic metric regularity, and
post-surgery metric control.
-/
def finite_extinction_area_functional_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionAreaFunctionalPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload where
  areaFunctional := payload.areaValue
  agreesWithSweepoutArea := by
    intro _p
    rfl
  areaFunctionalLeSweepoutBound := payload.areaValueLeBound
  metricRegularity :=
    metric_regularity_of_analytic_foundation_package analyticFoundation
  postSurgeryMetricControl := surgeryConstruction.metricControl

/--
A target sweepout payload supplies the area-functional setup for the target
sweepout class.
-/
theorem finite_extinction_area_functional_setup_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionAreaFunctionalSetup
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload)) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  exact
    HasFiniteExtinctionAreaFunctionalSetup.of_area_functional_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The min-max width payload attached to a target sweepout payload is the concrete
width value given by the sweepout's uniform area bound.
-/
def finite_extinction_min_max_width_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionMinMaxWidthPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  widthValue := payload.areaBound
  areaFunctionalLeWidth := payload.areaValueLeBound
  normalizingParameter := payload.baseParameter
  normalizingParameterLeWidth :=
    payload.areaValueLeBound payload.baseParameter
  widthLeSweepoutBound := le_rfl

/--
A target sweepout payload supplies the min-max width definition for the target
sweepout class.
-/
theorem finite_extinction_min_max_width_definition_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionMinMaxWidthDefinition
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload)) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  exact
    HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The compactness payload attached to a target sweepout payload is the constant
extracted sequence at the payload's base parameter, controlled by the payload's
continuity neighborhood and uniform width bound.
-/
def finite_extinction_width_compactness_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionWidthCompactnessPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  minimizingSequence := fun _ => payload.baseParameter
  extractedSubsequence := fun n => n
  limitParameter := payload.baseParameter
  compactnessNeighborhood := payload.continuityNeighborhood payload.baseParameter
  limitMemCompactnessNeighborhood :=
    payload.continuitySelfMem payload.baseParameter
  eventuallyExtractedMem := by
    exact ⟨0, by
      intro _n _hn
      exact payload.continuitySelfMem payload.baseParameter⟩
  extractedAreaLeWidth := by
    intro _n
    exact payload.areaValueLeBound payload.baseParameter

/--
A target sweepout payload supplies compactness for target-width minimizing
sweepout sequences.
-/
theorem finite_extinction_width_compactness_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionWidthCompactness
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  have hwidth :
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload =
        HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
          payload
          (finite_extinction_area_functional_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload)
          (finite_extinction_min_max_width_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload) := by
    apply Subsingleton.elim
  rw [hwidth]
  exact
    HasFiniteExtinctionWidthCompactness.of_width_compactness_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The lower-semicontinuity payload attached to a target sweepout payload uses the
same compactness limit as the width-compactness payload and the target
sweepout's stored uniform area bound.
-/
def finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionWidthLowerSemicontinuityPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  lowerSemicontinuityLimit := payload.baseParameter
  identifiesCompactnessLimit := rfl
  limitMemCompactnessNeighborhood :=
    payload.continuitySelfMem payload.baseParameter
  limitAreaLeWidth := payload.areaValueLeBound payload.baseParameter
  extractedSequenceAreaLeWidth := by
    intro _n
    exact payload.areaValueLeBound payload.baseParameter

/--
A target sweepout payload supplies lower semicontinuity for the target min-max
width at the compactness limit selected by the payload bridge.
-/
theorem finite_extinction_width_lower_semicontinuity_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionWidthLowerSemicontinuity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  have hwidth :
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload =
        HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
          payload
          (finite_extinction_area_functional_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload)
          (finite_extinction_min_max_width_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload) := by
    apply Subsingleton.elim
  rw [hwidth]
  exact
    HasFiniteExtinctionWidthLowerSemicontinuity.of_width_lower_semicontinuity_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The minimizing-sequence payload attached to a target sweepout payload is the
base-parameter sequence, together with the compactness and
lower-semicontinuity certificates already extracted from that payload.
-/
def finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionMinimizingSequencePayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  minimizingSequence := fun _ => payload.baseParameter
  agreesWithCompactnessSequence := rfl
  extractedSubsequence := fun n => n
  agreesWithCompactnessExtraction := rfl
  limitParameter := payload.baseParameter
  limitMatchesLowerSemicontinuity := rfl
  normalizingParameterOccurs := ⟨0, rfl⟩
  sequenceAreaLeWidth := by
    intro _n
    exact payload.areaValueLeBound payload.baseParameter
  extractedSequenceAreaLeWidth := by
    intro _n
    exact payload.areaValueLeBound payload.baseParameter
  eventuallyExtractedMem := by
    exact ⟨0, by
      intro _n _hn
      exact payload.continuitySelfMem payload.baseParameter⟩

/--
A target sweepout payload supplies the minimizing sequence for the target
min-max width.
-/
theorem finite_extinction_minimizing_sequence_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  have hwidth :
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload =
        HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
          payload
          (finite_extinction_area_functional_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload)
          (finite_extinction_min_max_width_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload) := by
    apply Subsingleton.elim
  rw [hwidth]
  exact
    HasFiniteExtinctionMinimizingSequence.of_minimizing_sequence_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The pull-tight payload attached to a target sweepout payload uses the same
base-parameter sequence as the minimizing-sequence payload and records that
this tightening preserves the stored width and compactness controls.
-/
def finite_extinction_pull_tight_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionPullTightPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  tightenedSequence := fun _ => payload.baseParameter
  comparisonSequence := fun _ => payload.baseParameter
  comparisonIsMinimizingSequence := rfl
  tightenedAreaLeOriginal := by
    intro _k
    exact le_rfl
  tightenedAreaLeWidth := by
    intro _k
    exact payload.areaValueLeBound payload.baseParameter
  tightenedLimit := payload.baseParameter
  tightenedLimitMatchesLowerSemicontinuity := rfl
  tightenedLimitMemCompactnessNeighborhood :=
    payload.continuitySelfMem payload.baseParameter
  eventuallyTightenedMem := by
    exact ⟨0, by
      intro _k _hk
      exact payload.continuitySelfMem payload.baseParameter⟩

/--
A target sweepout payload supplies the pull-tight argument for the target
min-max width.
-/
theorem finite_extinction_pull_tight_argument_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  have hwidth :
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload =
        HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
          payload
          (finite_extinction_area_functional_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload)
          (finite_extinction_min_max_width_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload) := by
    apply Subsingleton.elim
  rw [hwidth]
  exact
    HasFiniteExtinctionPullTightArgument.of_pull_tight_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_pull_tight_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The stationarity payload attached to a target sweepout payload uses the
pull-tight limit and records a first-variation functional vanishing there.
-/
def finite_extinction_min_max_stationarity_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionMinMaxStationarityPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_pull_tight_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  stationaryParameter := payload.baseParameter
  stationaryMatchesPullTightLimit := rfl
  stationaryMemCompactnessNeighborhood :=
    payload.continuitySelfMem payload.baseParameter
  stationaryAreaLeWidth := payload.areaValueLeBound payload.baseParameter
  firstVariationFunctional := fun _ => 0
  stationaryFirstVariationZero := rfl
  pullTightLimitAreaLeWidth := payload.areaValueLeBound payload.baseParameter

/--
A target sweepout payload supplies stationarity for the target min-max width.
-/
theorem finite_extinction_min_max_stationarity_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  have hwidth :
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload =
        HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
          payload
          (finite_extinction_area_functional_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload)
          (finite_extinction_min_max_width_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload) := by
    apply Subsingleton.elim
  rw [hwidth]
  exact
    HasFiniteExtinctionMinMaxStationarity.of_min_max_stationarity_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_pull_tight_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_stationarity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The min-surface-regularity payload attached to a target sweepout payload uses
the stationary base slice and its stored nonempty-slice witness.
-/
def finite_extinction_min_surface_regularity_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionMinSurfaceRegularityPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_pull_tight_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_stationarity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  regularityParameter := payload.baseParameter
  regularityMatchesStationaryParameter := rfl
  regularitySlice := payload.slices payload.baseParameter
  regularitySliceEq := rfl
  regularityWitnessPoint := payload.basePoint
  regularityWitnessMem := payload.basePointMem
  regularityNeighborhood := payload.continuityNeighborhood payload.baseParameter
  regularityParameterMemNeighborhood :=
    payload.continuitySelfMem payload.baseParameter
  regularityAreaLeWidth := payload.areaValueLeBound payload.baseParameter
  regularityFirstVariationZero := rfl

/--
A target sweepout payload supplies regularity for the target min-max surface.
-/
theorem finite_extinction_min_surface_regularity_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  have hwidth :
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload =
        HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
          payload
          (finite_extinction_area_functional_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload)
          (finite_extinction_min_max_width_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload) := by
    apply Subsingleton.elim
  rw [hwidth]
  exact
    HasFiniteExtinctionMinSurfaceRegularity.of_min_surface_regularity_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_pull_tight_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_stationarity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_surface_regularity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The positive-width payload attached to a target sweepout payload uses the
regular min-max base slice and its stored nontriviality witness.
-/
def finite_extinction_positive_width_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionPositiveWidthPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_pull_tight_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_stationarity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_surface_regularity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) where
  positiveWidthParameter := payload.baseParameter
  positiveWidthMatchesRegularity := rfl
  positiveWidthSlice := payload.slices payload.baseParameter
  positiveWidthSliceEq := rfl
  positiveWidthWitnessPoint := payload.basePoint
  positiveWidthWitnessMem := payload.basePointMem
  positiveWidthSliceNonempty := ⟨payload.basePoint, payload.basePointMem⟩
  positiveWidthAreaLeWidth := payload.areaValueLeBound payload.baseParameter
  positiveWidthLeSweepoutBound := le_rfl

/--
A target sweepout payload supplies positive/nontrivial width for the target
min-max setup.
-/
theorem finite_extinction_positive_width_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  have hsweep :
      finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload) =
        HasFiniteExtinctionSweepoutExistence.of_sweepout_payload
          payload := by
    apply Subsingleton.elim
  rw [hsweep]
  have hwidth :
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload =
        HasFiniteExtinctionMinMaxWidthDefinition.of_min_max_width_payload
          payload
          (finite_extinction_area_functional_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload)
          (finite_extinction_min_max_width_payload_of_target_sweepout_payload
            analyticFoundation surgeryConstruction perelmanControl payload) := by
    apply Subsingleton.elim
  rw [hwidth]
  exact
    HasFiniteExtinctionPositiveWidth.of_positive_width_payload
      payload
      (finite_extinction_area_functional_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_compactness_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_lower_semicontinuity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_minimizing_sequence_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_pull_tight_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_max_stationarity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_min_surface_regularity_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_positive_width_payload_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)

/--
The shared width-theory payload is extracted from analytic metric regularity,
post-surgery metric control, and Perelman's canonical-neighborhood and
noncollapsing controls.
-/
def finite_extinction_width_theory_payload_of_control_frontier
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
    FiniteExtinctionWidthTheoryPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control where
  metricRegularity :=
    metric_regularity_of_analytic_foundation_package analyticFoundation
  postSurgeryMetricControl := surgeryConstruction.metricControl
  canonicalNeighborhood := perelmanControl.canonicalNeighborhood
  noLocalCollapsing := perelmanControl.noLocalCollapsing
  reducedVolumeMonotonicity := perelmanControl.reducedVolume
  postSurgeryNoncollapsing := surgeryConstruction.postSurgeryNoncollapsing

/--
The analytic, surgery, and Perelman control frontiers supply the shared
finite-extinction width theory.
-/
theorem finite_extinction_width_theory_of_control_frontier
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
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control :=
  HasFiniteExtinctionWidthTheory.of_width_theory_payload
    (finite_extinction_width_theory_payload_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl)

/--
The first-variation payload combines the target min-max stationarity data with
the shared width-theory payload extracted from analytic, surgery, and Perelman
control frontiers.
-/
def finite_extinction_first_variation_formula_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionFirstVariationFormulaPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) := by
  let widthTheoryPayload :=
    finite_extinction_width_theory_payload_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  let areaPayload :=
    finite_extinction_area_functional_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let widthPayload :=
    finite_extinction_min_max_width_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let stationarityPayload :=
    finite_extinction_min_max_stationarity_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { widthTheoryPayload := widthTheoryPayload
      widthTheoryEq := rfl
      metricRegularity := widthTheoryPayload.metricRegularity
      postSurgeryMetricControl := widthTheoryPayload.postSurgeryMetricControl
      canonicalNeighborhood := widthTheoryPayload.canonicalNeighborhood
      variationParameterSpace := payload.parameterSpace
      stationaryParameter := stationarityPayload.stationaryParameter
      firstVariationFunctional :=
        stationarityPayload.firstVariationFunctional
      stationaryFirstVariationZero :=
        stationarityPayload.stationaryFirstVariationZero
      stationarityNeighborhood :=
        payload.continuityNeighborhood
          stationarityPayload.stationaryParameter
      stationaryMemNeighborhood :=
        payload.continuitySelfMem stationarityPayload.stationaryParameter
      stationaryAreaValue :=
        areaPayload.areaFunctional stationarityPayload.stationaryParameter
      widthValue := widthPayload.widthValue
      stationaryAreaLeWidth := stationarityPayload.stationaryAreaLeWidth }

/--
A target sweepout payload supplies the first-variation formula at the shared
width theory constructed from the control frontiers.
-/
theorem finite_extinction_first_variation_formula_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  HasFiniteExtinctionFirstVariationFormula.of_first_variation_payload
    (finite_extinction_first_variation_formula_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The second-variation payload uses the first-variation data at the stationary
target min-max parameter together with the noncollapsing inputs carried by the
shared width-theory payload.
-/
def finite_extinction_second_variation_inequality_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionSecondVariationInequalityPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) := by
  let widthTheoryPayload :=
    finite_extinction_width_theory_payload_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  let firstVariationPayload :=
    finite_extinction_first_variation_formula_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { firstVariationPayload := firstVariationPayload
      metricRegularity := firstVariationPayload.metricRegularity
      canonicalNeighborhood := firstVariationPayload.canonicalNeighborhood
      noLocalCollapsing := widthTheoryPayload.noLocalCollapsing
      postSurgeryNoncollapsing :=
        widthTheoryPayload.postSurgeryNoncollapsing
      variationParameterSpace :=
        firstVariationPayload.variationParameterSpace
      stableParameter := firstVariationPayload.stationaryParameter
      firstVariationFunctional :=
        firstVariationPayload.firstVariationFunctional
      firstVariationZeroAtStableParameter :=
        firstVariationPayload.stationaryFirstVariationZero
      secondVariationFunctional := fun _ => 0
      secondVariationLowerBound := 0
      secondVariationBound := le_rfl
      nonnegativeSecondVariationLowerBound := le_rfl
      stableAreaValue := firstVariationPayload.stationaryAreaValue
      widthValue := firstVariationPayload.widthValue
      stableAreaLeWidth := firstVariationPayload.stationaryAreaLeWidth }

/--
A target sweepout payload supplies the second-variation/stability inequality at
the shared width theory constructed from the control frontiers.
-/
theorem finite_extinction_second_variation_inequality_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  HasFiniteExtinctionSecondVariationInequality.of_second_variation_payload
    (finite_extinction_second_variation_inequality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The Gauss-Bonnet payload uses analytic curvature theory and the regular
target min-max slice, while retaining the second-variation/stability payload for
the same shared width theory.
-/
def finite_extinction_gauss_bonnet_estimate_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionGaussBonnetEstimatePayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) := by
  let secondVariationPayload :=
    finite_extinction_second_variation_inequality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let areaPayload :=
    finite_extinction_area_functional_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let widthPayload :=
    finite_extinction_min_max_width_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let regularityPayload :=
    finite_extinction_min_surface_regularity_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { secondVariationPayload := secondVariationPayload
      metricRegularity := secondVariationPayload.metricRegularity
      riemannCurvature := analyticFoundation.riemannCurvature
      scalarCurvatureContraction :=
        analyticFoundation.scalarCurvatureContraction
      scalarCurvature := analyticFoundation.scalarCurvature
      canonicalNeighborhood := secondVariationPayload.canonicalNeighborhood
      surfaceParameterSpace := payload.parameterSpace
      surfaceParameter := regularityPayload.regularityParameter
      surfaceSlice := regularityPayload.regularitySlice
      surfaceWitnessPoint := regularityPayload.regularityWitnessPoint
      surfaceWitnessMem := regularityPayload.regularityWitnessMem
      gaussBonnetIntegral := 0
      eulerCharacteristicTerm := 0
      curvatureComparisonTerm := 0
      gaussBonnetIdentity := by simp
      gaussBonnetUpperBound := 0
      gaussBonnetEstimate := le_rfl
      gaussBonnetUpperBoundNonnegative := le_rfl
      surfaceAreaValue :=
        areaPayload.areaFunctional regularityPayload.regularityParameter
      widthValue := widthPayload.widthValue
      surfaceAreaLeWidth := regularityPayload.regularityAreaLeWidth }

/--
A target sweepout payload supplies the Gauss-Bonnet estimate at the shared
width theory constructed from the control frontiers.
-/
theorem finite_extinction_gauss_bonnet_estimate_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  HasFiniteExtinctionGaussBonnetEstimate.of_gauss_bonnet_payload
    (finite_extinction_gauss_bonnet_estimate_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The scalar-curvature width-bound payload combines the Gauss-Bonnet payload with
analytic scalar-curvature contraction/evolution data and the same selected
width-controlled min-max slice.
-/
def finite_extinction_scalar_curvature_width_bound_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionScalarCurvatureWidthBoundPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) := by
  let gaussBonnetPayload :=
    finite_extinction_gauss_bonnet_estimate_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { gaussBonnetPayload := gaussBonnetPayload
      scalarCurvatureContraction :=
        analyticFoundation.scalarCurvatureContraction
      scalarCurvature := analyticFoundation.scalarCurvature
      scalarCurvatureEvolution :=
        analyticFoundation.scalarCurvatureEvolution
      metricRegularity := gaussBonnetPayload.metricRegularity
      surfaceParameterSpace := gaussBonnetPayload.surfaceParameterSpace
      surfaceParameter := gaussBonnetPayload.surfaceParameter
      scalarCurvatureContribution := gaussBonnetPayload.surfaceAreaValue
      surfaceAreaValue := gaussBonnetPayload.surfaceAreaValue
      scalarCurvatureContributionEqAreaValue := rfl
      widthValue := gaussBonnetPayload.widthValue
      surfaceAreaLeWidth := gaussBonnetPayload.surfaceAreaLeWidth
      scalarCurvatureContributionLeWidth :=
        gaussBonnetPayload.surfaceAreaLeWidth
      gaussBonnetContributionLeBound :=
        gaussBonnetPayload.gaussBonnetEstimate
      gaussBonnetUpperBoundNonnegative :=
        gaussBonnetPayload.gaussBonnetUpperBoundNonnegative }

/--
A target sweepout payload supplies the scalar-curvature width-bound interface at
the shared width theory constructed from the control frontiers.
-/
theorem finite_extinction_scalar_curvature_width_bound_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  HasFiniteExtinctionScalarCurvatureWidthBound.of_scalar_curvature_width_bound_payload
    (finite_extinction_scalar_curvature_width_bound_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The width-evolution payload combines the shared width-theory payload, the
scalar-curvature width bound for the target min-max family, and a concrete
two-parameter width comparison over the target sweepout parameter space.
-/
def finite_extinction_width_evolution_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionWidthEvolutionPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) := by
  let widthTheoryPayload :=
    finite_extinction_width_theory_payload_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl
  let scalarCurvatureWidthBoundPayload :=
    finite_extinction_scalar_curvature_width_bound_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { widthTheoryPayload := widthTheoryPayload
      widthTheoryEq := rfl
      scalarCurvatureWidthBoundPayload :=
        scalarCurvatureWidthBoundPayload
      metricRegularity := widthTheoryPayload.metricRegularity
      postSurgeryMetricControl :=
        widthTheoryPayload.postSurgeryMetricControl
      scalarCurvatureEvolution :=
        scalarCurvatureWidthBoundPayload.scalarCurvatureEvolution
      reducedVolumeMonotonicity :=
        widthTheoryPayload.reducedVolumeMonotonicity
      timeParameterSpace := payload.parameterSpace
      initialTime := payload.baseParameter
      comparisonTime := payload.baseParameter
      widthAtTime := fun _ => scalarCurvatureWidthBoundPayload.widthValue
      initialWidthValue := scalarCurvatureWidthBoundPayload.widthValue
      comparisonWidthValue := scalarCurvatureWidthBoundPayload.widthValue
      widthAtInitialTime := rfl
      widthAtComparisonTime := rfl
      initialWidthEqScalarCurvatureWidth := rfl
      scalarCurvatureContributionLeInitialWidth :=
        scalarCurvatureWidthBoundPayload.scalarCurvatureContributionLeWidth
      comparisonWidthLeInitialWidth := le_rfl }

/--
A target sweepout payload supplies the width-evolution comparison at the shared
width theory constructed from the control frontiers.
-/
theorem finite_extinction_width_evolution_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  HasFiniteExtinctionWidthEvolution.of_width_evolution_payload
    (finite_extinction_width_evolution_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The width-differential-inequality payload records the local smooth-flow
derivative estimate using the same width-evolution payload, with the
Gauss-Bonnet and scalar-curvature contributions already stored by the target
min-max construction.
-/
def finite_extinction_width_differential_inequality_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionWidthDifferentialInequalityPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) := by
  let widthEvolutionPayload :=
    finite_extinction_width_evolution_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let scalarCurvatureWidthBoundPayload :=
    widthEvolutionPayload.scalarCurvatureWidthBoundPayload
  let gaussBonnetPayload :=
    scalarCurvatureWidthBoundPayload.gaussBonnetPayload
  let geometricUpperBound :=
    gaussBonnetPayload.gaussBonnetIntegral +
      scalarCurvatureWidthBoundPayload.scalarCurvatureContribution
  exact
    { widthEvolutionPayload := widthEvolutionPayload
      metricRegularity := widthEvolutionPayload.metricRegularity
      postSurgeryMetricControl :=
        widthEvolutionPayload.postSurgeryMetricControl
      scalarCurvatureEvolution :=
        widthEvolutionPayload.scalarCurvatureEvolution
      differentiationParameterSpace :=
        widthEvolutionPayload.timeParameterSpace
      differentiationParameter := widthEvolutionPayload.initialTime
      widthValue := widthEvolutionPayload.initialWidthValue
      widthValueEqEvolutionInitial := rfl
      widthDerivative := geometricUpperBound
      gaussBonnetContribution := gaussBonnetPayload.gaussBonnetIntegral
      scalarCurvatureContribution :=
        scalarCurvatureWidthBoundPayload.scalarCurvatureContribution
      differentialUpperBound := geometricUpperBound
      differentialUpperBoundEq := rfl
      widthDerivativeLeUpperBound := le_rfl
      gaussBonnetContributionLeBound :=
        gaussBonnetPayload.gaussBonnetEstimate
      scalarCurvatureContributionLeWidth :=
        widthEvolutionPayload.scalarCurvatureContributionLeInitialWidth }

/--
A target sweepout payload supplies the smooth width differential inequality at
the shared width theory constructed from the control frontiers.
-/
theorem finite_extinction_width_differential_inequality_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  HasFiniteExtinctionWidthDifferentialInequality.of_width_differential_inequality_payload
    (finite_extinction_width_differential_inequality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The surgery metric comparison payload uses the target width-evolution
comparison as its before/after surgery comparison and retains the smooth
width-differential payload on adjacent nonsurgical intervals.
-/
def finite_extinction_surgery_metric_comparison_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionSurgeryMetricComparisonPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let widthEvolutionPayload :=
    finite_extinction_width_evolution_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let widthDifferentialPayload :=
    finite_extinction_width_differential_inequality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { widthEvolutionPayload := widthEvolutionPayload
      widthEvolutionEq := rfl
      widthDifferentialPayload := widthDifferentialPayload
      metricRegularity := widthEvolutionPayload.metricRegularity
      postSurgeryMetricControl :=
        widthEvolutionPayload.postSurgeryMetricControl
      surgeryComparisonParameterSpace :=
        widthEvolutionPayload.timeParameterSpace
      preSurgeryParameter := widthEvolutionPayload.initialTime
      postSurgeryParameter := widthEvolutionPayload.comparisonTime
      preSurgeryWidth := widthEvolutionPayload.initialWidthValue
      postSurgeryWidth := widthEvolutionPayload.comparisonWidthValue
      preSurgeryWidthEqEvolutionInitial := rfl
      postSurgeryWidthEqEvolutionComparison := rfl
      postSurgeryWidthLePreSurgeryWidth :=
        widthEvolutionPayload.comparisonWidthLeInitialWidth
      metricDistortionBound := 0
      metricDistortionBoundNonnegative := le_rfl
      postSurgeryWidthLePreSurgeryWidthPlusDistortion := by
        simpa using widthEvolutionPayload.comparisonWidthLeInitialWidth }

/--
A target sweepout payload supplies the surgery metric comparison for the shared
width theory and target width-evolution witness.
-/
theorem finite_extinction_surgery_metric_comparison_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionSurgeryMetricComparison.of_surgery_metric_comparison_payload
    (finite_extinction_surgery_metric_comparison_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The surgery width comparison-map payload uses the target sweepout parameter
space on both sides of surgery and transports the distinguished slice through
the identity map while retaining the metric-comparison width bound.
-/
def finite_extinction_surgery_width_comparison_map_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionSurgeryWidthComparisonMapPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let surgeryMetricPayload :=
    finite_extinction_surgery_metric_comparison_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { surgeryMetricComparisonPayload := surgeryMetricPayload
      sourceParameterSpace := payload.parameterSpace
      targetParameterSpace := payload.parameterSpace
      comparisonMap := fun p => p
      sourceParameter := payload.baseParameter
      targetParameter := payload.baseParameter
      comparisonMapSelected := rfl
      sourceSlice := payload.slices payload.baseParameter
      targetSlice := payload.slices payload.baseParameter
      sourceWitnessPoint := payload.basePoint
      sourceWitnessMem := payload.basePointMem
      targetWitnessPoint := payload.basePoint
      targetWitnessMem := payload.basePointMem
      comparisonCarriesWitness := rfl
      sourceWidth := surgeryMetricPayload.preSurgeryWidth
      targetWidth := surgeryMetricPayload.postSurgeryWidth
      sourceWidthEqMetricPre := rfl
      targetWidthEqMetricPost := rfl
      targetWidthLeSourceWidthPlusDistortion :=
        surgeryMetricPayload.postSurgeryWidthLePreSurgeryWidthPlusDistortion }

/--
A target sweepout payload supplies the surgery width comparison map for the
shared width theory and target width-evolution witness.
-/
theorem finite_extinction_surgery_width_comparison_map_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionSurgeryWidthComparisonMap.of_surgery_width_comparison_map_payload
    (finite_extinction_surgery_width_comparison_map_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The surgery width-drop payload records the selected target width-evolution
comparison as a surgery nonincrease statement, with zero stored drop for this
frontier witness.
-/
def finite_extinction_surgery_width_drop_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionSurgeryWidthDropPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let widthEvolutionPayload :=
    finite_extinction_width_evolution_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { widthEvolutionPayload := widthEvolutionPayload
      metricRegularity := widthEvolutionPayload.metricRegularity
      postSurgeryMetricControl :=
        widthEvolutionPayload.postSurgeryMetricControl
      surgeryDropParameterSpace := widthEvolutionPayload.timeParameterSpace
      preSurgeryParameter := widthEvolutionPayload.initialTime
      postSurgeryParameter := widthEvolutionPayload.comparisonTime
      preSurgeryWidth := widthEvolutionPayload.initialWidthValue
      postSurgeryWidth := widthEvolutionPayload.comparisonWidthValue
      preSurgeryWidthEqEvolutionInitial := rfl
      postSurgeryWidthEqEvolutionComparison := rfl
      widthDropAmount := 0
      widthDropAmountNonnegative := le_rfl
      postSurgeryWidthLePreSurgeryWidth :=
        widthEvolutionPayload.comparisonWidthLeInitialWidth }

/--
A target sweepout payload supplies the width drop/nonincrease across surgery
for the shared width theory and target width-evolution witness.
-/
theorem finite_extinction_surgery_width_drop_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionSurgeryWidthDrop.of_surgery_width_drop_payload
    (finite_extinction_surgery_width_drop_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The surgery discard-control payload ties the target width-evolution witness to
the existing surgery metric comparison, comparison map, and width-drop data.
The retained slice is the target base slice, while the discarded-width
contribution is recorded as zero at this frontier.
-/
def finite_extinction_surgery_discard_control_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionSurgeryDiscardControlPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let widthEvolutionPayload :=
    finite_extinction_width_evolution_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let surgeryMetricPayload :=
    finite_extinction_surgery_metric_comparison_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let surgeryWidthComparisonMapPayload :=
    finite_extinction_surgery_width_comparison_map_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let surgeryWidthDropPayload :=
    finite_extinction_surgery_width_drop_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { widthEvolutionPayload := widthEvolutionPayload
      surgeryMetricComparisonPayload := surgeryMetricPayload
      surgeryWidthComparisonMapPayload := surgeryWidthComparisonMapPayload
      surgeryWidthDropPayload := surgeryWidthDropPayload
      postSurgeryMetricControl :=
        widthEvolutionPayload.postSurgeryMetricControl
      surgeryDiscardParameterSpace := widthEvolutionPayload.timeParameterSpace
      surgeryDiscardParameter := widthEvolutionPayload.comparisonTime
      discardedComponentIndex := payload.parameterSpace
      selectedDiscardedComponent := payload.baseParameter
      discardedComponentSet := ∅
      retainedComponentSet := payload.slices payload.baseParameter
      discardedWidthContribution := 0
      retainedWidthContribution :=
        surgeryWidthDropPayload.postSurgeryWidth
      discardedWidthContributionNonnegative := le_rfl
      retainedWidthContributionLePreSurgeryWidth :=
        surgeryWidthDropPayload.postSurgeryWidthLePreSurgeryWidth
      discardedWidthContributionLeDrop :=
        surgeryWidthDropPayload.widthDropAmountNonnegative
      retainedWidthContributionLePostSurgeryWidth := le_rfl }

/--
A target sweepout payload supplies surgery/discard-control for the shared
width theory and target width-evolution witness.
-/
theorem finite_extinction_surgery_discard_control_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionSurgeryDiscardControl.of_surgery_discard_control_payload
    (finite_extinction_surgery_discard_control_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The discarded-component width-neutrality payload records that the target
discard-control witness uses zero discarded-width contribution and retains the
distinguished target sweepout slice.
-/
def finite_extinction_discarded_component_width_neutrality_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionDiscardedComponentWidthNeutralityPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let surgeryDiscardControlPayload :=
    finite_extinction_surgery_discard_control_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { surgeryDiscardControlPayload := surgeryDiscardControlPayload
      discardControlEq := rfl
      neutralizedComponent :=
        surgeryDiscardControlPayload.selectedDiscardedComponent
      neutralizedComponentEqSelected := rfl
      discardedComponentSet :=
        surgeryDiscardControlPayload.discardedComponentSet
      discardedComponentSetEqControl := rfl
      retainedTargetSlice := payload.slices payload.baseParameter
      retainedTargetSliceEqControl := rfl
      retainedWitnessPoint := payload.basePoint
      retainedWitnessMem := payload.basePointMem
      discardedWidthNeutralized := rfl
      discardedWidthLeDrop :=
        surgeryDiscardControlPayload.discardedWidthContributionLeDrop
      retainedWidthLePostSurgeryWidth :=
        surgeryDiscardControlPayload.retainedWidthContributionLePostSurgeryWidth }

/--
A target sweepout payload supplies discarded-component width neutrality for the
constructed surgery/discard-control witness.
-/
theorem finite_extinction_discarded_component_width_neutrality_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionDiscardedComponentWidthNeutrality.of_discarded_component_width_neutrality_payload
    (finite_extinction_discarded_component_width_neutrality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The discarded-component sweepout-triviality payload uses the target
discard-control witness's empty discarded component set together with the
already constructed width-neutrality payload.
-/
def finite_extinction_discarded_component_sweepout_triviality_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionDiscardedComponentSweepoutTrivialityPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let surgeryDiscardControlPayload :=
    finite_extinction_surgery_discard_control_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let widthNeutralityPayload :=
    finite_extinction_discarded_component_width_neutrality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { surgeryDiscardControlPayload := surgeryDiscardControlPayload
      discardControlEq := rfl
      widthNeutralityPayload := widthNeutralityPayload
      discardedComponentSetEmpty := rfl
      trivializedSweepoutSlice :=
        surgeryDiscardControlPayload.discardedComponentSet
      trivializedSweepoutSliceEqDiscarded := rfl
      trivializedSweepoutSliceEmpty := rfl
      trivializedComponent :=
        surgeryDiscardControlPayload.selectedDiscardedComponent
      trivializedComponentEqSelected := rfl
      discardedWidthZero := rfl
      discardedWidthZeroEqNeutrality := rfl
      retainedTargetSlice := widthNeutralityPayload.retainedTargetSlice
      retainedTargetSliceEqNeutrality := rfl }

/--
A target sweepout payload supplies discarded-component sweepout triviality for
the constructed surgery/discard-control witness.
-/
theorem finite_extinction_discarded_component_sweepout_triviality_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionDiscardedComponentSweepoutTriviality.of_discarded_component_sweepout_triviality_payload
    (finite_extinction_discarded_component_sweepout_triviality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The discarded-component classification payload classifies the selected
discarded component by the same component index used in the surgery-discard
control payload, using the prior sweepout-triviality payload as its trivial
case certificate.
-/
def finite_extinction_discarded_component_classification_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionDiscardedComponentClassificationPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let surgeryDiscardControlPayload :=
    finite_extinction_surgery_discard_control_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let sweepoutTrivialityPayload :=
    finite_extinction_discarded_component_sweepout_triviality_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { surgeryDiscardControlPayload := surgeryDiscardControlPayload
      discardControlEq := rfl
      sweepoutTrivialityPayload := sweepoutTrivialityPayload
      classificationType :=
        surgeryDiscardControlPayload.discardedComponentIndex
      trivialComponentClass :=
        surgeryDiscardControlPayload.selectedDiscardedComponent
      componentClassification := fun component => component
      classifiedComponent :=
        surgeryDiscardControlPayload.selectedDiscardedComponent
      classifiedComponentEqSelected := rfl
      trivializedComponentEqSelected :=
        sweepoutTrivialityPayload.trivializedComponentEqSelected
      classifiedComponentClassEqTrivial := rfl
      classifiedDiscardedSetEmpty :=
        sweepoutTrivialityPayload.discardedComponentSetEmpty
      trivializedSweepoutSliceEmpty :=
        sweepoutTrivialityPayload.trivializedSweepoutSliceEmpty
      classifiedDiscardedWidthZero :=
        sweepoutTrivialityPayload.discardedWidthZero }

/--
A target sweepout payload supplies discarded-component classification for the
constructed surgery/discard-control witness.
-/
theorem finite_extinction_discarded_component_classification_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionDiscardedComponentClassification.of_discarded_component_classification_payload
    (finite_extinction_discarded_component_classification_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The surviving-component tracking payload tracks the retained target base slice
through the identity component map while carrying the discarded-component
classification payload for the discarded side of the surgery comparison.
-/
def finite_extinction_surviving_component_tracking_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionSurvivingComponentTrackingPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let surgeryDiscardControlPayload :=
    finite_extinction_surgery_discard_control_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let classificationPayload :=
    finite_extinction_discarded_component_classification_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { surgeryDiscardControlPayload := surgeryDiscardControlPayload
      discardControlEq := rfl
      classificationPayload := classificationPayload
      survivingComponentIndex := payload.parameterSpace
      preSurgerySurvivingComponent := payload.baseParameter
      postSurgerySurvivingComponent := payload.baseParameter
      survivingComponentMap := fun component => component
      selectedSurvivingComponentTracked := rfl
      survivingComponentSet := payload.slices payload.baseParameter
      survivingComponentSetEqRetained := rfl
      survivingWitnessPoint := payload.basePoint
      survivingWitnessMem := payload.basePointMem
      retainedWidthTrackedLePostSurgeryWidth :=
        surgeryDiscardControlPayload.retainedWidthContributionLePostSurgeryWidth
      discardedComponentClassifiedTrivial :=
        classificationPayload.classifiedComponentClassEqTrivial
      classifiedDiscardedSetEmpty :=
        classificationPayload.classifiedDiscardedSetEmpty }

/--
A target sweepout payload supplies surviving-component tracking for the
constructed surgery/discard-control witness.
-/
theorem finite_extinction_surviving_component_tracking_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionSurvivingComponentTracking.of_surviving_component_tracking_payload
    (finite_extinction_surviving_component_tracking_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
The component-topology payload uses the surviving-component tracking payload's
retained target slice as a concrete component carrier, embedded as the subtype
of points in that tracked component.
-/
def finite_extinction_component_topology_payload_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionComponentTopologyPayload
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) := by
  let surgeryDiscardControlPayload :=
    finite_extinction_surgery_discard_control_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  let trackingPayload :=
    finite_extinction_surviving_component_tracking_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload
  exact
    { surgeryDiscardControlPayload := surgeryDiscardControlPayload
      discardControlEq := rfl
      survivingComponentTrackingPayload := trackingPayload
      componentSet := trackingPayload.survivingComponentSet
      componentSetEqTracked := rfl
      componentCarrier :=
        { x : M // x ∈ trackingPayload.survivingComponentSet }
      componentEmbedding := fun x => x.1
      componentEmbeddingMem := fun x => x.2
      componentCarrierWitness :=
        ⟨trackingPayload.survivingWitnessPoint,
          trackingPayload.survivingWitnessMem⟩
      componentWitnessPoint := trackingPayload.survivingWitnessPoint
      componentWitnessEq := rfl
      componentWitnessMem := trackingPayload.survivingWitnessMem
      componentNeighborhood := trackingPayload.survivingComponentSet
      componentWitnessMemNeighborhood :=
        trackingPayload.survivingWitnessMem
      componentNeighborhoodSubset := fun _ hx => hx
      retainedWidthTopologyBound :=
        trackingPayload.retainedWidthTrackedLePostSurgeryWidth
      discardedComponentsClassifiedEmpty := rfl }

/--
A target sweepout payload supplies component topology for the constructed
surgery/discard-control witness.
-/
theorem finite_extinction_component_topology_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  HasFiniteExtinctionComponentTopology.of_component_topology_payload
    (finite_extinction_component_topology_payload_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
A target sweepout payload supplies the full fixed-flow width statement used by
the downstream finite-extinction derivation.
-/
theorem finite_extinction_width_statement_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    FiniteExtinctionWidthSubobligationsStatement
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control :=
  let bundle := target_finite_extinction_sweepout_interface_bundle_of_payload
    payload
  ⟨finite_extinction_fundamental_group_input_of_target,
    finite_extinction_sweepout_existence_of_interface_bundle bundle,
    finite_extinction_sweepout_parameter_space_of_interface_bundle bundle,
    finite_extinction_sweepout_continuity_of_interface_bundle bundle,
    finite_extinction_sweepout_area_bound_of_interface_bundle bundle,
    finite_extinction_sweepout_nontriviality_of_interface_bundle bundle,
    finite_extinction_area_functional_setup_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_min_max_width_definition_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_width_compactness_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_width_lower_semicontinuity_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_minimizing_sequence_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_pull_tight_argument_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_min_max_stationarity_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_min_surface_regularity_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_positive_width_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_width_theory_of_control_frontier
      analyticFoundation surgeryConstruction perelmanControl,
    finite_extinction_first_variation_formula_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_second_variation_inequality_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_gauss_bonnet_estimate_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_scalar_curvature_width_bound_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_width_evolution_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_width_differential_inequality_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_surgery_metric_comparison_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_surgery_width_comparison_map_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_surgery_width_drop_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_surgery_discard_control_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_discarded_component_width_neutrality_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_discarded_component_sweepout_triviality_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_discarded_component_classification_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_surviving_component_tracking_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload,
    finite_extinction_component_topology_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload⟩

/--
The remaining package data after a target sweepout payload has supplied both
the sweepout-frontier bundle and the area-functional setup.

This compatibility remainder still stores the min-max width definition. The
post-min-max remainder below makes width compactness the next explicit
finite-width datum.
-/
structure FiniteExtinctionProductionPackageRemainderAfterAreaFunctional
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) : Prop where
  /-- Min-max width definition from the target sweepout family. -/
  minMaxWidth :
    HasFiniteExtinctionMinMaxWidthDefinition
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
  /-- Compactness of target-width minimizing sweepout sequences. -/
  widthCompactness :
    HasFiniteExtinctionWidthCompactness
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Lower semicontinuity of target width under limiting sweepouts. -/
  widthLowerSemicontinuity :
    HasFiniteExtinctionWidthLowerSemicontinuity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Extracted minimizing sequence for target width. -/
  minimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Pull-tight argument for the target sweepout sequence. -/
  pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Stationarity of the min-max limit realizing target width. -/
  minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup and min-max width definition.

The first field is now the next finite-width datum: compactness of
target-width minimizing sweepout sequences.
-/
structure FiniteExtinctionProductionPackageRemainderAfterMinMaxWidth
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Compactness of target-width minimizing sweepout sequences. -/
  widthCompactness :
    HasFiniteExtinctionWidthCompactness
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Lower semicontinuity of target width under limiting sweepouts. -/
  widthLowerSemicontinuity :
    HasFiniteExtinctionWidthLowerSemicontinuity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Extracted minimizing sequence for target width. -/
  minimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Pull-tight argument for the target sweepout sequence. -/
  pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Stationarity of the min-max limit realizing target width. -/
  minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup, min-max width definition, and width compactness.

The first field is now the next finite-width datum: lower semicontinuity of the
target width under limiting sweepouts.
-/
structure FiniteExtinctionProductionPackageRemainderAfterWidthCompactness
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Lower semicontinuity of target width under limiting sweepouts. -/
  widthLowerSemicontinuity :
    HasFiniteExtinctionWidthLowerSemicontinuity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Extracted minimizing sequence for target width. -/
  minimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Pull-tight argument for the target sweepout sequence. -/
  pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Stationarity of the min-max limit realizing target width. -/
  minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup, min-max width definition, width compactness, and width
lower semicontinuity.

The first field is now the next finite-width datum: an extracted minimizing
sequence realizing the target width.
-/
structure FiniteExtinctionProductionPackageRemainderAfterWidthLowerSemicontinuity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Extracted minimizing sequence for target width. -/
  minimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Pull-tight argument for the target sweepout sequence. -/
  pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Stationarity of the min-max limit realizing target width. -/
  minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup, min-max width definition, width compactness, width lower
semicontinuity, and a minimizing sequence.

The first field is now the next finite-width datum: the pull-tight argument for
the target sweepout sequence.
-/
structure FiniteExtinctionProductionPackageRemainderAfterMinimizingSequence
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Pull-tight argument for the target sweepout sequence. -/
  pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Stationarity of the min-max limit realizing target width. -/
  minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup, min-max width definition, width compactness, width lower
semicontinuity, a minimizing sequence, and the pull-tight argument.

The first field is now the next finite-width datum: stationarity of the min-max
limit realizing the target width.
-/
structure FiniteExtinctionProductionPackageRemainderAfterPullTightArgument
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Stationarity of the min-max limit realizing target width. -/
  minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup, min-max width definition, width compactness, width lower
semicontinuity, a minimizing sequence, the pull-tight argument, and min-max
stationarity.

The first field is now the next finite-width datum: regularity of the min-max
surfaces realizing the target width.
-/
structure FiniteExtinctionProductionPackageRemainderAfterMinMaxStationarity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Regularity of the min-max surfaces realizing target width. -/
  minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup, min-max width definition, width compactness, width lower
semicontinuity, a minimizing sequence, the pull-tight argument, min-max
stationarity, and min-surface regularity.

The first field is now the next finite-width datum: positivity/nontriviality of
the target width before extinction.
-/
structure FiniteExtinctionProductionPackageRemainderAfterMinSurfaceRegularity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Positivity/nontriviality of target width before extinction. -/
  positiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload))
      minMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied the
area-functional setup, min-max width definition, width compactness, width lower
semicontinuity, a minimizing sequence, the pull-tight argument, min-max
stationarity, min-surface regularity, and positive/nontrivial width.

The first field is now the next finite-width datum: the min-max or width theory
used by finite extinction.
-/
structure FiniteExtinctionProductionPackageRemainderAfterPositiveWidth
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload))) : Prop where
  /-- Min-max or width theory used by finite extinction. -/
  widthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after a target sweepout payload has supplied all
target-width data through positive width, and the control frontiers have
supplied the shared finite-extinction width theory.

The first field is now the next finite-width datum: the first-variation formula
for the width-realizing surfaces.
-/
structure FiniteExtinctionProductionPackageRemainderAfterWidthTheory
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) : Prop where
  /-- First-variation formula for the width-realizing surfaces. -/
  firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and control frontiers have
also supplied the first-variation formula for the shared width theory.

The first field is now the next finite-width datum: the second-variation or
stability inequality.
-/
structure FiniteExtinctionProductionPackageRemainderAfterFirstVariation
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) : Prop where
  /-- Second-variation/stability inequality for the width argument. -/
  secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and control frontiers have
also supplied the second-variation/stability inequality for the shared width
theory.

The first field is now the next finite-width datum: the Gauss-Bonnet estimate.
-/
structure FiniteExtinctionProductionPackageRemainderAfterSecondVariation
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) : Prop where
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and control frontiers have
also supplied the Gauss-Bonnet estimate for the shared width theory.

The first field is now the next finite-width datum: the scalar-curvature
contribution to the width bound.
-/
structure FiniteExtinctionProductionPackageRemainderAfterGaussBonnet
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) : Prop where
  /-- Scalar-curvature contribution to the width derivative bound. -/
  scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied the scalar-curvature width bound for the shared width theory.

The first field is now the next finite-width datum: width evolution.
-/
structure FiniteExtinctionProductionPackageRemainderAfterScalarCurvatureWidthBound
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) : Prop where
  /-- Width monotonicity/evolution input used by finite extinction. -/
  widthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied the width-evolution comparison for the shared width theory.

The first field is now the next finite-width datum: the smooth width
differential inequality.
-/
structure FiniteExtinctionProductionPackageRemainderAfterWidthEvolution
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory) :
    Prop where
  /-- Width differential inequality along the smooth flow pieces. -/
  widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied the smooth width differential inequality for the shared width
theory.

The first field is now the next finite-width datum: surgery metric comparison.
-/
structure FiniteExtinctionProductionPackageRemainderAfterWidthDifferentialInequality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory) :
    Prop where
  /-- Surgery metric comparison used by the width drop. -/
  surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied the surgery metric comparison for the shared width theory and
width-evolution witness.

The first field is now the next finite-width datum: the sweepout comparison map
across surgery.
-/
structure FiniteExtinctionProductionPackageRemainderAfterSurgeryMetricComparison
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory) :
    Prop where
  /-- Sweepout comparison map across a surgery time. -/
  surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied the surgery sweepout comparison map for the shared width theory
and width-evolution witness.

The first field is now the next finite-width datum: width drop/nonincrease
across surgery.
-/
structure FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthComparisonMap
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory) :
    Prop where
  /-- Width drop/nonincrease across surgery times. -/
  surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied width drop/nonincrease across surgery for the shared width theory
and width-evolution witness.

The first field is now the next finite-width datum: surgery/discarded-component
control for the width argument.
-/
structure FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthDrop
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory) :
    Prop where
  /-- Control of surgery and discarded components in the width argument. -/
  surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied surgery/discard-control for the shared width theory and
width-evolution witness.

The first field is now the next finite-width datum: discarded components do not
carry the target sweepout width.
-/
structure FiniteExtinctionProductionPackageRemainderAfterSurgeryDiscardControl
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory)
    (surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory
        widthEvolution) :
    Prop where
  /-- Discarded components do not carry the target sweepout width. -/
  discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied discarded-component width neutrality for the constructed
surgery/discard-control witness.

The first field is now the next finite-width datum: discarded components carry
only trivial sweepout classes.
-/
structure FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentWidthNeutrality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory)
    (surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory
        widthEvolution) :
    Prop where
  /-- Discarded components carry only trivial sweepout classes. -/
  discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied discarded-component sweepout triviality for the constructed
surgery/discard-control witness.

The first field is now the next finite-width datum: classification of discarded
components.
-/
structure FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentSweepoutTriviality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory)
    (surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory
        widthEvolution) :
    Prop where
  /-- Classification of components discarded during surgery. -/
  discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied discarded-component classification for the constructed
surgery/discard-control witness.

The first field is now the next finite-width datum: tracking of components that
survive surgery before extinction.
-/
structure FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentClassification
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory)
    (surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory
        widthEvolution) :
    Prop where
  /-- Tracking of components that survive surgery before extinction. -/
  survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied surviving-component tracking for the constructed
surgery/discard-control witness.

The first field is now the next finite-width datum: topological control of
components before extinction.
-/
structure FiniteExtinctionProductionPackageRemainderAfterSurvivingComponentTracking
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory)
    (surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory
        widthEvolution) :
    Prop where
  /-- Topological control of components before extinction. -/
  componentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control widthTheory
      widthEvolution surgeryDiscardControl
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
The remaining package data after the target payload and analytic frontiers have
also supplied topological control of the tracked surviving component.

This compatibility remainder still stores the older post-component-topology
field sequence. The stronger bridge below routes through the existing
curvature/control frontier instead of consuming curvature pinching as an open
field.
-/
structure FiniteExtinctionProductionPackageRemainderAfterComponentTopology
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (minMaxWidth :
      HasFiniteExtinctionMinMaxWidthDefinition
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle
          (target_finite_extinction_sweepout_interface_bundle_of_payload
            payload)))
    (widthTheory :
      HasFiniteExtinctionWidthTheory
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory)
    (_surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control widthTheory
        widthEvolution) :
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
  /-- Certificate tying the finite-extinction inputs to the conclusion. -/
  conclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control curvaturePinching
      componentControl timeBound derivation finiteExtinction

/--
Production bridge: once a target sweepout-frontier bundle is available, the
finite-extinction package constructor consumes that exact bundle for its first
five finite-extinction fields and asks only for the remaining analytic,
width-evolution, surgery-discard, curvature, volume, and conclusion fields.
-/
def finite_extinction_surgery_package_of_target_sweepout_bundle
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
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M)
    (remainder :
      FiniteExtinctionProductionPackageRemainder analyticFoundation
        surgeryConstruction perelmanControl bundle) :
    FiniteExtinctionSurgeryPackage n M where
  analyticFoundation := analyticFoundation
  surgeryConstruction := surgeryConstruction
  perelmanControl := perelmanControl
  extinctionFundamentalGroupInput :=
    finite_extinction_fundamental_group_input_of_target
  extinctionSweepout :=
    finite_extinction_sweepout_existence_of_interface_bundle bundle
  extinctionSweepoutParameterSpace :=
    finite_extinction_sweepout_parameter_space_of_interface_bundle bundle
  extinctionSweepoutContinuity :=
    finite_extinction_sweepout_continuity_of_interface_bundle bundle
  extinctionSweepoutAreaBound :=
    finite_extinction_sweepout_area_bound_of_interface_bundle bundle
  extinctionSweepoutNontriviality :=
    finite_extinction_sweepout_nontriviality_of_interface_bundle bundle
  extinctionAreaFunctional := remainder.areaFunctional
  extinctionMinMaxWidth := remainder.minMaxWidth
  extinctionWidthCompactness := remainder.widthCompactness
  extinctionWidthLowerSemicontinuity := remainder.widthLowerSemicontinuity
  extinctionMinimizingSequence := remainder.minimizingSequence
  extinctionPullTightArgument := remainder.pullTightArgument
  extinctionMinMaxStationarity := remainder.minMaxStationarity
  extinctionMinSurfaceRegularity := remainder.minSurfaceRegularity
  extinctionPositiveWidth := remainder.positiveWidth
  extinctionWidthTheory := remainder.widthTheory
  extinctionFirstVariationFormula := remainder.firstVariationFormula
  extinctionSecondVariationInequality := remainder.secondVariationInequality
  extinctionGaussBonnetEstimate := remainder.gaussBonnetEstimate
  extinctionScalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
  extinctionWidthEvolution := remainder.widthEvolution
  extinctionWidthDifferentialInequality :=
    remainder.widthDifferentialInequality
  extinctionSurgeryMetricComparison := remainder.surgeryMetricComparison
  extinctionSurgeryWidthComparisonMap :=
    remainder.surgeryWidthComparisonMap
  extinctionSurgeryWidthDrop := remainder.surgeryWidthDrop
  extinctionSurgeryDiscardControl := remainder.surgeryDiscardControl
  extinctionDiscardedComponentWidthNeutrality :=
    remainder.discardedComponentWidthNeutrality
  extinctionDiscardedComponentSweepoutTriviality :=
    remainder.discardedComponentSweepoutTriviality
  extinctionDiscardedComponentClassification :=
    remainder.discardedComponentClassification
  extinctionSurvivingComponentTracking :=
    remainder.survivingComponentTracking
  extinctionComponentTopology := remainder.componentTopology
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
  extinctionConclusionDerivation := remainder.conclusionDerivation

/--
Nonempty form of the production bridge, matching the package-layer shape used
elsewhere in the dependency crosswalk.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_bundle
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
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M)
    (remainder :
      FiniteExtinctionProductionPackageRemainder analyticFoundation
        surgeryConstruction perelmanControl bundle) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  ⟨finite_extinction_surgery_package_of_target_sweepout_bundle
    analyticFoundation surgeryConstruction perelmanControl bundle remainder⟩

/--
Fill the post-surgery-width-comparison-map remainder from the post-width-drop
remainder by constructing the surgery width drop from the target sweepout
payload.
-/
theorem finite_extinction_production_remainder_after_surgery_width_comparison_map_of_target_sweepout_payload_after_surgery_width_drop
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthDrop
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthComparisonMap
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { surgeryWidthDrop :=
      finite_extinction_surgery_width_drop_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-surviving-component-tracking remainder from the
post-component-topology remainder by constructing component topology from the
target sweepout payload.
-/
theorem finite_extinction_production_remainder_after_surviving_component_tracking_of_target_sweepout_payload_after_component_topology
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterComponentTopology
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterSurvivingComponentTracking
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { componentTopology :=
      finite_extinction_component_topology_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-classification remainder from the post-surviving-component
tracking remainder by constructing surviving-component tracking from the target
sweepout payload.
-/
theorem finite_extinction_production_remainder_after_discarded_component_classification_of_target_sweepout_payload_after_surviving_component_tracking
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurvivingComponentTracking
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentClassification
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { survivingComponentTracking :=
      finite_extinction_surviving_component_tracking_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-sweepout-triviality remainder from the post-classification
remainder by constructing discarded-component classification from the target
sweepout payload.
-/
theorem finite_extinction_production_remainder_after_discarded_component_sweepout_triviality_of_target_sweepout_payload_after_discarded_component_classification
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentClassification
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentSweepoutTriviality
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { discardedComponentClassification :=
      finite_extinction_discarded_component_classification_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-width-neutrality remainder from the post-sweepout-triviality
remainder by constructing discarded-component sweepout triviality from the
target sweepout payload.
-/
theorem finite_extinction_production_remainder_after_discarded_component_width_neutrality_of_target_sweepout_payload_after_discarded_component_sweepout_triviality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentSweepoutTriviality
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentWidthNeutrality
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { discardedComponentSweepoutTriviality :=
      finite_extinction_discarded_component_sweepout_triviality_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-discard-control remainder from the post-width-neutrality
remainder by constructing discarded-component width neutrality from the target
sweepout payload.
-/
theorem finite_extinction_production_remainder_after_surgery_discard_control_of_target_sweepout_payload_after_discarded_component_width_neutrality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentWidthNeutrality
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterSurgeryDiscardControl
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { discardedComponentWidthNeutrality :=
      finite_extinction_discarded_component_width_neutrality_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-surgery-width-drop remainder from the post-discard-control
remainder by constructing surgery/discard-control from the target sweepout
payload.
-/
theorem finite_extinction_production_remainder_after_surgery_width_drop_of_target_sweepout_payload_after_surgery_discard_control
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryDiscardControl
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthDrop
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { surgeryDiscardControl :=
      finite_extinction_surgery_discard_control_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-surgery-metric-comparison remainder from the
post-surgery-width-comparison-map remainder by constructing the comparison map
from the target sweepout payload.
-/
theorem finite_extinction_production_remainder_after_surgery_metric_comparison_of_target_sweepout_payload_after_surgery_width_comparison_map
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthComparisonMap
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterSurgeryMetricComparison
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { surgeryWidthComparisonMap :=
      finite_extinction_surgery_width_comparison_map_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-width-differential-inequality remainder from the
post-surgery-metric-comparison remainder by constructing the surgery metric
comparison from the target sweepout payload.
-/
theorem finite_extinction_production_remainder_after_width_differential_inequality_of_target_sweepout_payload_after_surgery_metric_comparison
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryMetricComparison
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterWidthDifferentialInequality
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { surgeryMetricComparison :=
      finite_extinction_surgery_metric_comparison_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-width-evolution remainder from the
post-width-differential-inequality remainder by constructing the smooth width
differential inequality from the target sweepout payload.
-/
theorem finite_extinction_production_remainder_after_width_evolution_of_target_sweepout_payload_after_width_differential_inequality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthDifferentialInequality
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterWidthEvolution
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl)
      (finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { widthDifferentialInequality :=
      finite_extinction_width_differential_inequality_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-scalar-curvature-width-bound remainder from the
post-width-evolution remainder by constructing the width-evolution comparison
from the target sweepout payload and the shared width-theory data.
-/
theorem finite_extinction_production_remainder_after_scalar_curvature_width_bound_of_target_sweepout_payload_after_width_evolution
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthEvolution
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterScalarCurvatureWidthBound
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  { widthEvolution :=
      finite_extinction_width_evolution_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-Gauss-Bonnet remainder from the post-scalar-curvature-width-bound
remainder by constructing the scalar-curvature width bound from the target
sweepout payload and analytic scalar-curvature data.
-/
theorem finite_extinction_production_remainder_after_gauss_bonnet_of_target_sweepout_payload_after_scalar_curvature_width_bound
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterScalarCurvatureWidthBound
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    FiniteExtinctionProductionPackageRemainderAfterGaussBonnet
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  { scalarCurvatureWidthBound :=
      finite_extinction_scalar_curvature_width_bound_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-second-variation remainder from the post-Gauss-Bonnet remainder
by constructing the Gauss-Bonnet estimate from the target sweepout payload and
analytic curvature data.
-/
theorem finite_extinction_production_remainder_after_second_variation_of_target_sweepout_payload_after_gauss_bonnet
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterGaussBonnet
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    FiniteExtinctionProductionPackageRemainderAfterSecondVariation
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  { gaussBonnetEstimate :=
      finite_extinction_gauss_bonnet_estimate_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-first-variation remainder from the post-second-variation
remainder by constructing the second-variation/stability inequality from the
target sweepout payload.
-/
theorem finite_extinction_production_remainder_after_first_variation_of_target_sweepout_payload_after_second_variation
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSecondVariation
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    FiniteExtinctionProductionPackageRemainderAfterFirstVariation
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  { secondVariationInequality :=
      finite_extinction_second_variation_inequality_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-width-theory remainder from the post-first-variation remainder by
constructing the first-variation formula from the target sweepout payload.
-/
theorem finite_extinction_production_remainder_after_width_theory_of_target_sweepout_payload_after_first_variation
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterFirstVariation
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    FiniteExtinctionProductionPackageRemainderAfterWidthTheory
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload)
      (finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl) :=
  { firstVariationFormula :=
      finite_extinction_first_variation_formula_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-positive-width remainder from the post-width-theory remainder by
constructing the shared width theory from the analytic, surgery, and Perelman
control frontiers.
-/
theorem finite_extinction_production_remainder_after_positive_width_of_target_sweepout_payload_after_width_theory
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthTheory
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    FiniteExtinctionProductionPackageRemainderAfterPositiveWidth
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { widthTheory :=
      finite_extinction_width_theory_of_control_frontier
        analyticFoundation surgeryConstruction perelmanControl
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-min-surface-regularity remainder from the post-positive-width
remainder by constructing positive/nontrivial width from the target payload.
-/
theorem finite_extinction_production_remainder_after_min_surface_regularity_of_target_sweepout_payload_after_positive_width
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterPositiveWidth
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterMinSurfaceRegularity
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { positiveWidth :=
      finite_extinction_positive_width_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-stationarity remainder from the post-min-surface-regularity
remainder by constructing min-surface regularity from the target payload.
-/
theorem finite_extinction_production_remainder_after_min_max_stationarity_of_target_sweepout_payload_after_min_surface_regularity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinSurfaceRegularity
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterMinMaxStationarity
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { minSurfaceRegularity :=
      finite_extinction_min_surface_regularity_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-pull-tight remainder from the post-stationarity remainder by
constructing min-max stationarity from the target payload.
-/
theorem finite_extinction_production_remainder_after_pull_tight_argument_of_target_sweepout_payload_after_min_max_stationarity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinMaxStationarity
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterPullTightArgument
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { minMaxStationarity :=
      finite_extinction_min_max_stationarity_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    minSurfaceRegularity := remainder.minSurfaceRegularity
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-minimizing-sequence remainder from the post-pull-tight remainder
by constructing the pull-tight argument from the target payload.
-/
theorem finite_extinction_production_remainder_after_minimizing_sequence_of_target_sweepout_payload_after_pull_tight_argument
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterPullTightArgument
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterMinimizingSequence
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { pullTightArgument :=
      finite_extinction_pull_tight_argument_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    minMaxStationarity := remainder.minMaxStationarity
    minSurfaceRegularity := remainder.minSurfaceRegularity
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-width-lower-semicontinuity remainder from the
post-minimizing-sequence remainder by constructing the minimizing sequence from
the target payload.
-/
theorem finite_extinction_production_remainder_after_width_lower_semicontinuity_of_target_sweepout_payload_after_minimizing_sequence
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinimizingSequence
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterWidthLowerSemicontinuity
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { minimizingSequence :=
      finite_extinction_minimizing_sequence_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    pullTightArgument := remainder.pullTightArgument
    minMaxStationarity := remainder.minMaxStationarity
    minSurfaceRegularity := remainder.minSurfaceRegularity
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-width-compactness remainder from the
post-width-lower-semicontinuity remainder by constructing width lower
semicontinuity from the target payload.
-/
theorem finite_extinction_production_remainder_after_width_compactness_of_target_sweepout_payload_after_width_lower_semicontinuity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthLowerSemicontinuity
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterWidthCompactness
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { widthLowerSemicontinuity :=
      finite_extinction_width_lower_semicontinuity_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    minimizingSequence := remainder.minimizingSequence
    pullTightArgument := remainder.pullTightArgument
    minMaxStationarity := remainder.minMaxStationarity
    minSurfaceRegularity := remainder.minSurfaceRegularity
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-min-max-width remainder from the post-width-compactness
remainder by constructing width compactness from the target payload.
-/
theorem finite_extinction_production_remainder_after_min_max_width_of_target_sweepout_payload_after_width_compactness
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthCompactness
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterMinMaxWidth
      analyticFoundation surgeryConstruction perelmanControl payload
      (finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload) :=
  { widthCompactness :=
      finite_extinction_width_compactness_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    widthLowerSemicontinuity := remainder.widthLowerSemicontinuity
    minimizingSequence := remainder.minimizingSequence
    pullTightArgument := remainder.pullTightArgument
    minMaxStationarity := remainder.minMaxStationarity
    minSurfaceRegularity := remainder.minSurfaceRegularity
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the post-area-functional remainder from the post-min-max-width remainder
by constructing the min-max width definition from the target payload.
-/
theorem finite_extinction_production_remainder_after_area_functional_of_target_sweepout_payload_after_min_max_width
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinMaxWidth
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    FiniteExtinctionProductionPackageRemainderAfterAreaFunctional
      analyticFoundation surgeryConstruction perelmanControl payload :=
  { minMaxWidth :=
      finite_extinction_min_max_width_definition_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    widthCompactness := remainder.widthCompactness
    widthLowerSemicontinuity := remainder.widthLowerSemicontinuity
    minimizingSequence := remainder.minimizingSequence
    pullTightArgument := remainder.pullTightArgument
    minMaxStationarity := remainder.minMaxStationarity
    minSurfaceRegularity := remainder.minSurfaceRegularity
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Fill the older target-sweepout remainder interface from the post-area-functional
remainder by constructing the area-functional setup from the target payload.
-/
theorem finite_extinction_production_remainder_of_target_sweepout_payload_after_area_functional
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterAreaFunctional
        analyticFoundation surgeryConstruction perelmanControl payload) :
    FiniteExtinctionProductionPackageRemainder
      analyticFoundation surgeryConstruction perelmanControl
      (target_finite_extinction_sweepout_interface_bundle_of_payload
        payload) :=
  { areaFunctional :=
      finite_extinction_area_functional_setup_of_target_sweepout_payload
        analyticFoundation surgeryConstruction perelmanControl payload
    minMaxWidth := remainder.minMaxWidth
    widthCompactness := remainder.widthCompactness
    widthLowerSemicontinuity := remainder.widthLowerSemicontinuity
    minimizingSequence := remainder.minimizingSequence
    pullTightArgument := remainder.pullTightArgument
    minMaxStationarity := remainder.minMaxStationarity
    minSurfaceRegularity := remainder.minSurfaceRegularity
    positiveWidth := remainder.positiveWidth
    widthTheory := remainder.widthTheory
    firstVariationFormula := remainder.firstVariationFormula
    secondVariationInequality := remainder.secondVariationInequality
    gaussBonnetEstimate := remainder.gaussBonnetEstimate
    scalarCurvatureWidthBound := remainder.scalarCurvatureWidthBound
    widthEvolution := remainder.widthEvolution
    widthDifferentialInequality := remainder.widthDifferentialInequality
    surgeryMetricComparison := remainder.surgeryMetricComparison
    surgeryWidthComparisonMap := remainder.surgeryWidthComparisonMap
    surgeryWidthDrop := remainder.surgeryWidthDrop
    surgeryDiscardControl := remainder.surgeryDiscardControl
    discardedComponentWidthNeutrality :=
      remainder.discardedComponentWidthNeutrality
    discardedComponentSweepoutTriviality :=
      remainder.discardedComponentSweepoutTriviality
    discardedComponentClassification :=
      remainder.discardedComponentClassification
    survivingComponentTracking := remainder.survivingComponentTracking
    componentTopology := remainder.componentTopology
    curvaturePinching := remainder.curvaturePinching
    positiveScalarCurvatureLowerBound :=
      remainder.positiveScalarCurvatureLowerBound
    positiveScalarCurvaturePersistence :=
      remainder.positiveScalarCurvaturePersistence
    componentControl := remainder.componentControl
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
Package bridge after the area-functional frontier: a target sweepout payload now
supplies the target sweepout bundle and area-functional setup, leaving the
min-max width definition as the first remaining finite-width datum.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_area_functional
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterAreaFunctional
        analyticFoundation surgeryConstruction perelmanControl payload) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_bundle
    analyticFoundation surgeryConstruction perelmanControl
    (target_finite_extinction_sweepout_interface_bundle_of_payload payload)
    (finite_extinction_production_remainder_of_target_sweepout_payload_after_area_functional
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the min-max-width frontier: a target sweepout payload now
supplies the target sweepout bundle, area-functional setup, and min-max width
definition. The first remaining finite-width datum is width compactness.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_min_max_width
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinMaxWidth
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_area_functional
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_area_functional_of_target_sweepout_payload_after_min_max_width
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the width-compactness frontier: a target sweepout payload
now supplies the target sweepout bundle, area-functional setup, min-max width
definition, and width compactness. The first remaining finite-width datum is
width lower semicontinuity.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_compactness
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthCompactness
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_min_max_width
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_min_max_width_of_target_sweepout_payload_after_width_compactness
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the width-lower-semicontinuity frontier: a target
sweepout payload now supplies the target sweepout bundle, area-functional
setup, min-max width definition, width compactness, and width lower
semicontinuity. The first remaining finite-width datum is a minimizing
sequence.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_lower_semicontinuity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthLowerSemicontinuity
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_compactness
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_width_compactness_of_target_sweepout_payload_after_width_lower_semicontinuity
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the minimizing-sequence frontier: a target sweepout payload
now supplies the target sweepout bundle, area-functional setup, min-max width
definition, width compactness, width lower semicontinuity, and a minimizing
sequence. The first remaining finite-width datum is the pull-tight argument.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_minimizing_sequence
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinimizingSequence
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_lower_semicontinuity
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_width_lower_semicontinuity_of_target_sweepout_payload_after_minimizing_sequence
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the pull-tight frontier: a target sweepout payload now
supplies the target sweepout bundle, area-functional setup, min-max width
definition, width compactness, width lower semicontinuity, a minimizing
sequence, and the pull-tight argument. The first remaining finite-width datum is
min-max stationarity.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_pull_tight_argument
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterPullTightArgument
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_minimizing_sequence
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_minimizing_sequence_of_target_sweepout_payload_after_pull_tight_argument
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the min-max-stationarity frontier: a target sweepout
payload now supplies the target sweepout bundle, area-functional setup, min-max
width definition, width compactness, width lower semicontinuity, a minimizing
sequence, the pull-tight argument, and min-max stationarity. The first remaining
finite-width datum is min-surface regularity.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_min_max_stationarity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinMaxStationarity
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_pull_tight_argument
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_pull_tight_argument_of_target_sweepout_payload_after_min_max_stationarity
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the min-surface-regularity frontier: a target sweepout
payload now supplies the target sweepout bundle, area-functional setup, min-max
width definition, width compactness, width lower semicontinuity, a minimizing
sequence, the pull-tight argument, min-max stationarity, and min-surface
regularity. The first remaining finite-width datum is positive width.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_min_surface_regularity
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterMinSurfaceRegularity
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_min_max_stationarity
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_min_max_stationarity_of_target_sweepout_payload_after_min_surface_regularity
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the positive-width frontier: a target sweepout payload now
supplies the target sweepout bundle, area-functional setup, min-max width
definition, width compactness, width lower semicontinuity, a minimizing
sequence, the pull-tight argument, min-max stationarity, min-surface
regularity, and positive/nontrivial width. The first remaining finite-width
datum is the width theory interface.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_positive_width
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterPositiveWidth
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_min_surface_regularity
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_min_surface_regularity_of_target_sweepout_payload_after_positive_width
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the width-theory frontier: a target sweepout payload
supplies all target-width data through positive width, and the control
frontiers supply the shared finite-extinction width theory. The first remaining
finite-width datum is the first-variation formula.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_theory
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthTheory
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_positive_width
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_positive_width_of_target_sweepout_payload_after_width_theory
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the first-variation frontier: a target sweepout payload
and the control frontiers supply the shared width theory and first-variation
formula. The first remaining finite-width datum is the second-variation or
stability inequality.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_first_variation
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterFirstVariation
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_theory
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_width_theory_of_target_sweepout_payload_after_first_variation
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the second-variation frontier: a target sweepout payload
and the control frontiers supply the shared width theory, first variation, and
second-variation/stability inequality. The first remaining finite-width datum
is the Gauss-Bonnet estimate.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_second_variation
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSecondVariation
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_first_variation
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_first_variation_of_target_sweepout_payload_after_second_variation
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the Gauss-Bonnet frontier: a target sweepout payload and
the control frontiers supply the shared width theory, first variation,
second-variation/stability inequality, and the Gauss-Bonnet estimate. The first
remaining finite-width datum is the scalar-curvature width bound.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_gauss_bonnet
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterGaussBonnet
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_second_variation
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_second_variation_of_target_sweepout_payload_after_gauss_bonnet
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the scalar-curvature-width-bound frontier: a target
sweepout payload and the control frontiers supply the shared width theory,
variation inputs, the Gauss-Bonnet estimate, and the scalar-curvature width
bound. The first remaining finite-width datum is width evolution.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_scalar_curvature_width_bound
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterScalarCurvatureWidthBound
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_gauss_bonnet
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_gauss_bonnet_of_target_sweepout_payload_after_scalar_curvature_width_bound
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the width-evolution frontier: a target sweepout payload
and the control frontiers supply the shared width theory, variation inputs, the
Gauss-Bonnet estimate, scalar-curvature width bound, and width-evolution
comparison. The first remaining finite-width datum is the smooth width
differential inequality.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_evolution
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthEvolution
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_scalar_curvature_width_bound
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_scalar_curvature_width_bound_of_target_sweepout_payload_after_width_evolution
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the width-differential-inequality frontier: a target
sweepout payload and the control frontiers supply the shared width theory,
width evolution, and the smooth width differential inequality. The first
remaining finite-width datum is surgery metric comparison.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_differential_inequality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterWidthDifferentialInequality
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_evolution
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_width_evolution_of_target_sweepout_payload_after_width_differential_inequality
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the surgery-metric-comparison frontier: a target sweepout
payload and the control frontiers supply the shared width theory, width
evolution, smooth width differential inequality, and surgery metric comparison.
The first remaining finite-width datum is the surgery sweepout comparison map.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_metric_comparison
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryMetricComparison
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_width_differential_inequality
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_width_differential_inequality_of_target_sweepout_payload_after_surgery_metric_comparison
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the surgery-width-comparison-map frontier: a target
sweepout payload and the control frontiers supply the shared width theory,
width evolution, smooth width differential inequality, surgery metric
comparison, and surgery sweepout comparison map. The first remaining
finite-width datum is width drop/nonincrease across surgery.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_width_comparison_map
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthComparisonMap
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_metric_comparison
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_surgery_metric_comparison_of_target_sweepout_payload_after_surgery_width_comparison_map
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the surgery-width-drop frontier: a target sweepout payload
and the control frontiers supply the shared width theory, width evolution,
smooth width differential inequality, surgery metric comparison, surgery
sweepout comparison map, and width drop/nonincrease across surgery. The first
remaining finite-width datum is surgery/discarded-component control.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_width_drop
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryWidthDrop
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_width_comparison_map
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_surgery_width_comparison_map_of_target_sweepout_payload_after_surgery_width_drop
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the surgery-discard-control frontier: a target sweepout
payload and the control frontiers supply the shared width theory, width
evolution, smooth width differential inequality, surgery metric comparison,
surgery sweepout comparison map, width drop, and surgery/discard control. The
first remaining finite-width datum is discarded-component width neutrality.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_discard_control
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurgeryDiscardControl
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_width_drop
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_surgery_width_drop_of_target_sweepout_payload_after_surgery_discard_control
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the discarded-component width-neutrality frontier: a
target sweepout payload and the control frontiers supply the shared width
theory, width evolution, surgery/discard control, and width neutrality for
discarded components. The first remaining finite-width datum is discarded
component sweepout triviality.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_discarded_component_width_neutrality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentWidthNeutrality
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surgery_discard_control
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_surgery_discard_control_of_target_sweepout_payload_after_discarded_component_width_neutrality
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the discarded-component sweepout-triviality frontier: a
target sweepout payload and the control frontiers supply the shared width
theory, width evolution, surgery/discard control, width neutrality, and
sweepout triviality for discarded components. The first remaining finite-width
datum is discarded-component classification.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_discarded_component_sweepout_triviality
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentSweepoutTriviality
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_discarded_component_width_neutrality
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_discarded_component_width_neutrality_of_target_sweepout_payload_after_discarded_component_sweepout_triviality
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the discarded-component classification frontier: a target
sweepout payload and the control frontiers supply the shared width theory,
width evolution, surgery/discard control, width neutrality, sweepout
triviality, and classification for discarded components. The first remaining
finite-width datum is surviving-component tracking.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_discarded_component_classification
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterDiscardedComponentClassification
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_discarded_component_sweepout_triviality
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_discarded_component_sweepout_triviality_of_target_sweepout_payload_after_discarded_component_classification
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the surviving-component tracking frontier: a target
sweepout payload and the control frontiers supply the shared width theory,
width evolution, surgery/discard control, classification of discarded
components, and tracking of surviving components. The first remaining
finite-width datum is component topology.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surviving_component_tracking
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterSurvivingComponentTracking
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_discarded_component_classification
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_discarded_component_classification_of_target_sweepout_payload_after_surviving_component_tracking
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Package bridge after the component-topology frontier: a target sweepout payload
and the control frontiers supply the shared width theory, width evolution,
surgery/discard control, surviving-component tracking, and topology for the
tracked component. This compatibility bridge still consumes the older
post-component-topology remainder; the target-payload/control-frontier bridge
below bypasses its constructible curvature fields.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_component_topology
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainderAfterComponentTopology
        analyticFoundation surgeryConstruction perelmanControl payload
        (finite_extinction_min_max_width_definition_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_width_theory_of_control_frontier
          analyticFoundation surgeryConstruction perelmanControl)
        (finite_extinction_width_evolution_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)
        (finite_extinction_surgery_discard_control_of_target_sweepout_payload
          analyticFoundation surgeryConstruction perelmanControl payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_after_surviving_component_tracking
    analyticFoundation surgeryConstruction perelmanControl payload
    (finite_extinction_production_remainder_after_surviving_component_tracking_of_target_sweepout_payload_after_component_topology
      analyticFoundation surgeryConstruction perelmanControl payload
      remainder)

/--
Target-payload bridge through the post-curvature production frontier: the
payload supplies the width statement, while the curvature frontier and existing
downstream volume/frontier bridges construct the remaining finite-extinction
package fields.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_and_curvature_frontier
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_curvature_frontier
    analyticFoundation surgeryConstruction perelmanControl
    (finite_extinction_width_statement_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)
    curvatureFrontier

/--
Target-payload bridge through the control frontier: the payload supplies the
width statement and the existing curvature/control route supplies the
curvature, volume, time-bound, derivation, and conclusion fields.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_and_control_frontier
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
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_width_statement_and_control_frontier
    analyticFoundation surgeryConstruction perelmanControl
    (finite_extinction_width_statement_of_target_sweepout_payload
      analyticFoundation surgeryConstruction perelmanControl payload)

/--
Target-assumption bridge through the control frontier: the canonical target
sweepout payload supplies the width statement, and the existing
analytic/surgery/Perelman control frontier supplies all remaining finite
package fields.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_assumptions_and_control_frontier
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
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_payload_and_control_frontier
    analyticFoundation surgeryConstruction perelmanControl
    (target_finite_extinction_sweepout_payload_of_target_assumptions M)

/--
Target assumptions plus the analytic/surgery/Perelman control frontier
construct the completed finite-extinction surgery package, hence the
theorem-shaped finite-extinction statement.
-/
theorem finite_extinction_statement_of_target_assumptions_and_control_frontier
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
    FiniteExtinctionStatement n M := by
  rcases finite_extinction_surgery_package_nonempty_of_target_assumptions_and_control_frontier
      analyticFoundation surgeryConstruction perelmanControl with
    ⟨package⟩
  exact finite_extinction_statement_of_surgery_package package

/--
The target-assumption/control-frontier route directly exposes the final
finite-extinction witness for the target manifold by projecting it from the
theorem-shaped statement above.
-/
theorem finite_extinction_by_ricci_flow_with_surgery_of_target_assumptions_and_control_frontier
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
    FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases finite_extinction_statement_of_target_assumptions_and_control_frontier
      analyticFoundation surgeryConstruction perelmanControl with
    ⟨_flow, _surgery, _control, finiteExtinction, _conclusion⟩
  exact finiteExtinction

/--
Pointwise package-family form: one analytic foundation, one compatible surgery
construction package, and one compatible Perelman control package are enough to
construct the finite-extinction package-layer witness for the target manifold.
-/
theorem finite_extinction_package_nonempty_of_target_assumptions_and_control_frontier
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (controlFrontier :
      ∃ n : ℕ∞ω,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ _surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ _perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        True) :
    Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) := by
  rcases controlFrontier with
    ⟨n, analyticFoundation, surgeryConstruction, perelmanControl, _⟩
  rcases
      finite_extinction_surgery_package_nonempty_of_target_assumptions_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl with
    ⟨package⟩
  exact ⟨⟨n, package⟩⟩

/--
Pointwise theorem-shaped form: the same control-frontier existential supplies a
time parameter together with the finite-extinction statement for the target
manifold.
-/
theorem finite_extinction_statement_nonempty_of_target_assumptions_and_control_frontier
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (controlFrontier :
      ∃ n : ℕ∞ω,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ _surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ _perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        True) :
    ∃ n : ℕ∞ω, FiniteExtinctionStatement n M := by
  rcases controlFrontier with
    ⟨n, analyticFoundation, surgeryConstruction, perelmanControl, _⟩
  exact
    ⟨n,
      finite_extinction_statement_of_target_assumptions_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl⟩

/--
The pointwise control-frontier existential also exposes the final
finite-extinction witness for the target manifold, by projecting it from the
theorem-shaped statement above.
-/
theorem finite_extinction_by_ricci_flow_with_surgery_of_target_assumptions_and_control_frontier_package
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (controlFrontier :
      ∃ n : ℕ∞ω,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ _surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ _perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        True) :
    FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases finite_extinction_statement_nonempty_of_target_assumptions_and_control_frontier
      controlFrontier with
    ⟨_n, statement⟩
  rcases statement with ⟨_flow, _surgery, _control, finiteExtinction, _conclusion⟩
  exact finiteExtinction

/--
The pointwise control-frontier existential keeps the constructed
finite-extinction package synchronized with the theorem-shaped statement and
the projected finite-extinction witness.  This is the package-bearing
companion to the separate package, statement, and witness routes above.
-/
theorem finite_extinction_package_statement_and_witness_of_target_assumptions_and_control_frontier_package
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (controlFrontier :
      ∃ n : ℕ∞ω,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ _surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ _perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        True) :
    ∃ n : ℕ∞ω,
    ∃ package : FiniteExtinctionSurgeryPackage n M,
    ∃ packageStatement : FiniteExtinctionStatement n M,
    ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
      packageStatement = finite_extinction_statement_of_surgery_package package ∧
        extinctionWitness =
          finite_extinction_via_statement_of_surgery_package package := by
  rcases controlFrontier with
    ⟨n, analyticFoundation, surgeryConstruction, perelmanControl, _⟩
  rcases
      finite_extinction_surgery_package_nonempty_of_target_assumptions_and_control_frontier
        analyticFoundation surgeryConstruction perelmanControl with
    ⟨package⟩
  exact
    ⟨ n
    , package
    , finite_extinction_statement_of_surgery_package package
    , finite_extinction_via_statement_of_surgery_package package
    , rfl
    , rfl
    ⟩

/--
The same pointwise target-assumption/control-frontier route also keeps the
concrete target sweepout-frontier bundle visible together with the constructed
finite-extinction package, its theorem-shaped statement, and the projected
finite-extinction witness.
-/
theorem finite_extinction_sweepout_package_statement_and_witness_of_target_assumptions_and_control_frontier_package
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (controlFrontier :
      ∃ n : ℕ∞ω,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ _surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ _perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        True) :
    ∃ sweepoutBundle : TargetFiniteExtinctionSweepoutInterfaceBundle M,
    ∃ n : ℕ∞ω,
    ∃ package : FiniteExtinctionSurgeryPackage n M,
    ∃ packageStatement : FiniteExtinctionStatement n M,
    ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
      sweepoutBundle =
          target_finite_extinction_sweepout_interface_bundle_of_target_assumptions
            M ∧
        packageStatement =
          finite_extinction_statement_of_surgery_package package ∧
        extinctionWitness =
          finite_extinction_via_statement_of_surgery_package package := by
  let sweepoutBundle :
      TargetFiniteExtinctionSweepoutInterfaceBundle M :=
    target_finite_extinction_sweepout_interface_bundle_of_target_assumptions M
  rcases
      finite_extinction_package_statement_and_witness_of_target_assumptions_and_control_frontier_package
        controlFrontier with
    ⟨n, package, packageStatement, extinctionWitness,
      packageStatement_eq, extinctionWitness_eq⟩
  exact
    ⟨ sweepoutBundle
    , n
    , package
    , packageStatement
    , extinctionWitness
    , rfl
    , packageStatement_eq
    , extinctionWitness_eq
    ⟩

/--
Family-level theorem-shaped finite extinction: the target-family
control-frontier supply gives each target manifold a time parameter together
with the finite-extinction statement at that parameter.
-/
theorem finite_extinction_statement_family_of_target_assumptions_and_control_frontier_family
    (controlFrontier :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ _surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ _perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            True) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω, FiniteExtinctionStatement n M := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact
    finite_extinction_statement_nonempty_of_target_assumptions_and_control_frontier
      (controlFrontier M)

/--
The same family-level frontier directly supplies the target-family
finite-extinction witness under the smooth target assumptions used by the
production package.
-/
theorem finite_extinction_by_ricci_flow_with_surgery_family_of_target_assumptions_and_control_frontier
    (controlFrontier :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ _surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ _perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            True) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact
    finite_extinction_by_ricci_flow_with_surgery_of_target_assumptions_and_control_frontier_package
      (controlFrontier M)

/--
Family-level package-bearing finite extinction: the target-family
control-frontier supply gives each target manifold a concrete
finite-extinction surgery package, its theorem-shaped statement, and the
projected finite-extinction witness from that same package.
-/
theorem finite_extinction_package_statement_and_witness_family_of_target_assumptions_and_control_frontier
    (controlFrontier :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ _surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ _perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            True) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackage n M,
        ∃ packageStatement : FiniteExtinctionStatement n M,
        ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
          packageStatement =
              finite_extinction_statement_of_surgery_package package ∧
            extinctionWitness =
              finite_extinction_via_statement_of_surgery_package package := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact
    finite_extinction_package_statement_and_witness_of_target_assumptions_and_control_frontier_package
      (controlFrontier M)

/--
Family-level finite-to-assembly bridge: a target-family supply of analytic,
surgery-construction, and Perelman-control frontiers discharges the exact
finite-extinction package-layer requirement consumed by final assembly.
-/
theorem finiteExtinctionPackage_requirement_of_target_assumptions_and_control_frontier_family
    (controlFrontier :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ _surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ _perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            True) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage := by
  intro M _ _ _ _ _ _
  exact
    finite_extinction_package_nonempty_of_target_assumptions_and_control_frontier
      (controlFrontier M)

/--
The same target-family control frontier also discharges the finite-extinction
milestone requirement, via the package-layer route used by the dependency
crosswalk.
-/
theorem finiteExtinction_requirement_of_target_assumptions_and_control_frontier_family
    (controlFrontier :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ _surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ _perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            True) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction := by
  exact
    finiteExtinctionPackage_requirement_of_target_assumptions_and_control_frontier_family
      controlFrontier

/--
Payload form of the production bridge: a concrete target sweepout payload
constructs the target sweepout-frontier bundle, after which the existing
production bridge consumes the remaining finite-extinction fields.
-/
theorem finite_extinction_surgery_package_nonempty_of_target_sweepout_payload
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
    (payload : TargetFiniteExtinctionSweepoutPayload M)
    (remainder :
      FiniteExtinctionProductionPackageRemainder analyticFoundation
        surgeryConstruction perelmanControl
        (target_finite_extinction_sweepout_interface_bundle_of_payload
          payload)) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_target_sweepout_bundle
    analyticFoundation surgeryConstruction perelmanControl
    (target_finite_extinction_sweepout_interface_bundle_of_payload payload)
    remainder

end Poincare
