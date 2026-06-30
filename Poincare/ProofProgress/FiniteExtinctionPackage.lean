import Poincare.CompletionTarget
import Poincare.DependencyCrosswalk

open scoped Manifold ContDiff

namespace Poincare

/--
The first finite-extinction subobligation is already theorem-resolved from the
target hypotheses: simply connectedness makes every based fundamental group
finite.
-/
theorem finite_extinction_fundamental_group_input_of_target
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] :
    HasFiniteExtinctionFundamentalGroupInput M :=
  finite_extinction_fundamental_group_input_of_simplyConnectedSpace

/--
The proved fundamental-group input also gives the finite `π₁` formulation used
by the finite-extinction interface.
-/
theorem finite_extinction_piOne_finite_of_target
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] (x : M) :
    Finite (HomotopyGroup.Pi 1 M x) :=
  finite_extinction_piOne_finite_of_fundamentalGroupInput
    finite_extinction_fundamental_group_input_of_target x

/--
After the fundamental-group input is solved, any full finite-extinction
subobligation statement must in particular supply the next constructorless
interface: sweepout existence for the proved fundamental-group input.
-/
theorem finite_extinction_sweepout_existence_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement :
      FiniteExtinctionSubobligationsStatement flow surgery control) :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target := by
  rcases finite_extinction_subobligations_of_statement statement with
    ⟨finiteFundamentalGroup, sweepout, _rest⟩
  have hfg :
      finiteFundamentalGroup =
        finite_extinction_fundamental_group_input_of_target := by
    apply Subsingleton.elim
  exact hfg ▸ sweepout

/--
Conditional bridge: a full finite-extinction sub-obligation payload, for the
exact flow supplied by the analytic package and the exact surgery/Perelman
packages over it, supplies the finite-extinction surgery package required by
the dependency crosswalk.
-/
theorem finite_extinction_surgery_package_nonempty_of_subobligations
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (subobligations :
      FiniteExtinctionSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) :
    Nonempty (FiniteExtinctionSurgeryPackage n M) := by
  rcases subobligations with
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
      survivingComponentTracking, componentTopology, pinching,
      positiveScalarCurvatureLowerBound, positiveScalarCurvaturePersistence,
      componentControl, volumeEvolutionFormula, surgeryVolumeNonincrease,
      scalarCurvatureDifferentialInequality, volumeDifferentialInequality,
      volumeDecayEstimate, timeBound, differentialInequalityIntegration,
      finiteTimeIntegration, surgeryTimeSummability, extinctionTimeContradiction,
      derivation, extinction, conclusionDerivation⟩
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
      extinctionCurvaturePinching := pinching
      extinctionPositiveScalarCurvatureLowerBound :=
        positiveScalarCurvatureLowerBound
      extinctionPositiveScalarCurvaturePersistence :=
        positiveScalarCurvaturePersistence
      extinctionComponentControl := componentControl
      extinctionVolumeEvolutionFormula := volumeEvolutionFormula
      extinctionSurgeryVolumeNonincrease := surgeryVolumeNonincrease
      extinctionScalarCurvatureDifferentialInequality :=
        scalarCurvatureDifferentialInequality
      extinctionVolumeDifferentialInequality := volumeDifferentialInequality
      extinctionVolumeDecayEstimate := volumeDecayEstimate
      extinctionTimeBound := timeBound
      extinctionDifferentialInequalityIntegration :=
        differentialInequalityIntegration
      extinctionFiniteTimeIntegration := finiteTimeIntegration
      extinctionSurgeryTimeSummability := surgeryTimeSummability
      extinctionExtinctionTimeContradiction := extinctionTimeContradiction
      extinctionDerivation := derivation
      finiteExtinction := extinction
      extinctionConclusionDerivation := conclusionDerivation }⟩

/--
The same shared analytic/surgery/Perelman package tuple and full
finite-extinction sub-obligation statement also exposes the theorem-shaped
finite-extinction payload: the constructed surgery package, its package
statement, the statement rebuilt through the sub-obligation route, the
derivation certificate, and the resulting finite-extinction witness.
-/
theorem finite_extinction_statement_payload_of_subobligations
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (subobligations :
      FiniteExtinctionSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) :
    ∃ _package : FiniteExtinctionSurgeryPackage n M,
    ∃ _packageStatement : FiniteExtinctionStatement n M,
    ∃ _viaSubobligationsStatement : FiniteExtinctionStatement n M,
    ∃ _derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
      FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases finite_extinction_surgery_package_nonempty_of_subobligations
      analyticFoundation surgeryConstruction perelmanControl
      subobligations with
    ⟨package⟩
  exact
    ⟨ package
    , finite_extinction_statement_of_surgery_package package
    , finite_extinction_statement_of_subobligations_statement subobligations
    , finite_extinction_derivation_of_subobligations_statement subobligations
    , finite_extinction_via_statement_of_surgery_package package
    ⟩

/--
Conditional bridge: the finite-extinction package-layer witness follows from
one analytic package, one surgery construction package, one Perelman-control
package, and the full finite-extinction sub-obligation payload for their shared
flow.
-/
theorem finite_extinction_package_nonempty_of_subobligations
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (h :
      ∃ n : ℕ∞ω,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        FiniteExtinctionSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control) :
    Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) := by
  rcases h with
    ⟨n, analyticFoundation, surgeryConstruction, perelmanControl,
      subobligations⟩
  rcases finite_extinction_surgery_package_nonempty_of_subobligations
      analyticFoundation surgeryConstruction perelmanControl
      subobligations with
    ⟨package⟩
  exact ⟨⟨n, package⟩⟩

/--
A target-family supply of analytic/surgery/Perelman packages and full
finite-extinction sub-obligation statements supplies the theorem-shaped
finite-extinction payload for each target: the flow, surgery, control,
constructed package, package statement, sub-obligation statement route,
derivation certificate, and extinction witness.
-/
theorem finite_extinction_statement_payload_family_of_subobligations_family
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
        ∃ _packageStatement : FiniteExtinctionStatement n M,
        ∃ _viaSubobligationsStatement : FiniteExtinctionStatement n M,
        ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
          FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _top _t2 _charted _simple _compact _manifold
  rcases h M with
    ⟨n, analyticFoundation, surgeryConstruction, perelmanControl,
      subobligations⟩
  rcases finite_extinction_statement_payload_of_subobligations
      analyticFoundation surgeryConstruction perelmanControl
      subobligations with
    ⟨package, packageStatement, viaSubobligationsStatement, derivation,
      finiteExtinction⟩
  exact
    ⟨ n
    , ricci_flow_data_of_analytic_foundation_package analyticFoundation
    , surgeryConstruction.withSurgery
    , perelmanControl.control
    , package
    , packageStatement
    , viaSubobligationsStatement
    , derivation
    , finiteExtinction
    ⟩

/--
Conditional bridge: a target-family supply of analytic/surgery/Perelman
packages plus the full finite-extinction sub-obligation payload discharges the
finite-extinction package-layer requirement in `DependencyCrosswalk`.
-/
theorem finiteExtinctionPackage_requirement_of_subobligations_family
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage := by
  intro M _ _ _ _ _ _
  exact finite_extinction_package_nonempty_of_subobligations (h M)

/--
The conditional family-level sub-obligation route lands on exactly the
package-layer requirement named in the dependency crosswalk.
-/
theorem finiteExtinctionPackage_requirement_of_subobligations_family_eq
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    finiteExtinctionPackage_requirement_of_subobligations_family h =
      (by
        intro M _ _ _ _ _ _
        exact finite_extinction_package_nonempty_of_subobligations (h M)) := by
  rfl

/--
The same sub-obligation family discharges the finite-extinction milestone
requirement, not just the package-layer requirement.  The crosswalk assigns the
finite-extinction milestone to the finite-extinction package layer, so the
package payload constructed above is already the required milestone payload.
-/
theorem finiteExtinction_requirement_of_subobligations_family
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction := by
  exact finiteExtinctionPackage_requirement_of_subobligations_family h

/--
The sub-obligation route to the finite-extinction milestone is definitionally
the package-layer route through the milestone/package-layer crosswalk.
-/
theorem finiteExtinction_requirement_of_subobligations_family_to_package_layer_eq
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    finiteExtinction_requirement_of_subobligations_family h =
      finiteExtinctionPackage_requirement_of_subobligations_family h := by
  rfl

/--
Smoothability installs the with-corners manifold evidence needed to consume the
finite-extinction sub-obligation family for an arbitrary compact simply
connected charted three-manifold.  The result keeps the constructed package and
the theorem-shaped extinction evidence visible at each target.
-/
theorem finite_extinction_statement_payload_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        ∃ _manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
        ∃ _packageStatement : FiniteExtinctionStatement n M,
        ∃ _viaSubobligationsStatement : FiniteExtinctionStatement n M,
        ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
          FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _top _t2 _charted _simple _compact
  let manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M :=
    smoothable_of_smoothability_package smoothabilityPackage M
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := manifoldEvidence
  rcases finite_extinction_statement_payload_family_of_subobligations_family
      h M with
    ⟨n, flow, surgery, control, package, packageStatement,
      viaSubobligationsStatement, derivation, finiteExtinction⟩
  exact
    ⟨ manifoldEvidence
    , n
    , flow
    , surgery
    , control
    , package
    , packageStatement
    , viaSubobligationsStatement
    , derivation
    , finiteExtinction
    ⟩

/--
The smoothability-plus-sub-obligation-family route supplies the finite
extinction input consumed by the universal finite-extinction boundary.
-/
theorem finite_extinction_input_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _top _t2 _charted _simple _compact
  rcases
      finite_extinction_statement_payload_of_smoothability_and_subobligations_family
        smoothabilityPackage h M with
    ⟨_manifoldEvidence, _n, _flow, _surgery, _control, _package,
      _packageStatement, _viaSubobligationsStatement, _derivation,
      finiteExtinction⟩
  exact finiteExtinction

/--
Smoothability plus the full finite-extinction sub-obligation family supplies
the named universal finite-extinction boundary used by the final completion
route.
-/
theorem universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    UniversalFiniteExtinctionStatement.{u} :=
  finite_extinction_input_of_smoothability_and_subobligations_family
    smoothabilityPackage h

/--
The universal finite-extinction boundary obtained from smoothability and the
sub-obligation family is exactly the finite-extinction input projected from the
same theorem-shaped payload.
-/
theorem universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control) :
    universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
        smoothabilityPackage h =
      finite_extinction_input_of_smoothability_and_subobligations_family
        smoothabilityPackage h := by
  apply Subsingleton.elim

/--
The smoothability-plus-sub-obligation-family route reaches the conditional
Poincare endpoint through the named universal finite-extinction boundary and
the post-extinction extraction theorem still explicit on the current main
interface.
-/
theorem poincare_conjecture_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_conjecture_of_universalFiniteExtinctionStatement
    (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h)
    extractSphere

/--
The smoothability/sub-obligation-family endpoint is exactly the universal
finite-extinction endpoint applied to the boundary produced above and the
explicit post-extinction extraction theorem.
-/
theorem poincare_conjecture_of_smoothability_and_subobligations_family_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere =
      poincare_conjecture_of_universalFiniteExtinctionStatement
        (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
          smoothabilityPackage h)
        extractSphere := by
  apply Subsingleton.elim

/--
The smoothability/sub-obligation-family route exposes the reserved endpoint
and all universe-indexed completion criteria through the universal
finite-extinction completion payload.
-/
theorem poincare_conjecture_payload_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  universalFiniteExtinctionStatement_completion_payload
    (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h)
    extractSphere

/--
The smoothability/sub-obligation-family completion payload is exactly the
universal finite-extinction completion payload for its named boundary.
-/
theorem poincare_conjecture_payload_of_smoothability_and_subobligations_family_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_payload_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere =
      universalFiniteExtinctionStatement_completion_payload
        (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
          smoothabilityPackage h)
        extractSphere := by
  apply Subsingleton.elim

/--
The smoothability/sub-obligation-family route directly proves the canonical
completion target, not only the project statement spelling, by feeding its
constructed universal finite-extinction statement into the canonical
completion boundary.
-/
theorem canonical_completion_target_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_universalFiniteExtinctionStatement
    (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h)
    extractSphere

/--
The canonical target route above is exactly the universal finite-extinction
canonical route for the named smoothability/sub-obligation-family boundary.
-/
theorem canonical_completion_target_of_smoothability_and_subobligations_family_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_completion_target_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere =
      canonical_completion_target_of_universalFiniteExtinctionStatement
        (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
          smoothabilityPackage h)
        extractSphere := by
  apply Subsingleton.elim

/--
The smoothability/sub-obligation-family route exposes the canonical completion
payload, with the canonical target spelling used by final certificate code.
-/
theorem canonical_completion_payload_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_universalFiniteExtinctionStatement
    (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h)
    extractSphere

/--
The canonical payload route above is exactly the universal finite-extinction
canonical payload for the named smoothability/sub-obligation-family boundary.
-/
theorem canonical_completion_payload_of_smoothability_and_subobligations_family_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_completion_payload_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere =
      canonical_completion_payload_of_universalFiniteExtinctionStatement
        (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
          smoothabilityPackage h)
        extractSphere := by
  apply Subsingleton.elim

/--
The smoothability/sub-obligation-family route discharges any universe-indexed
completion criterion through the canonical completion target route.
-/
theorem canonical_completion_criterion_of_smoothability_and_subobligations_family
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_universalFiniteExtinctionStatement
    witness
    (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h)
    extractSphere

/--
The canonical criterion route above is exactly the universal finite-extinction
canonical criterion for the named smoothability/sub-obligation-family boundary.
-/
theorem canonical_completion_criterion_of_smoothability_and_subobligations_family_eq
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_completion_criterion_of_smoothability_and_subobligations_family
        witness smoothabilityPackage h extractSphere =
      canonical_completion_criterion_of_universalFiniteExtinctionStatement
        witness
        (universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
          smoothabilityPackage h)
        extractSphere := by
  apply Subsingleton.elim

/--
The smoothability/sub-obligation-family route directly discharges any
universe-indexed completion criterion by extracting the criterion component
from the completion payload above.
-/
theorem completion_criterion_of_smoothability_and_subobligations_family
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_conjecture_payload_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The direct criterion theorem is exactly the criterion component extracted from
the smoothability/sub-obligation-family completion payload.
-/
theorem completion_criterion_of_smoothability_and_subobligations_family_eq
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    completion_criterion_of_smoothability_and_subobligations_family
        witness smoothabilityPackage h extractSphere =
      (by
        rcases
            poincare_conjecture_payload_of_smoothability_and_subobligations_family
              smoothabilityPackage h extractSphere with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The smoothability/sub-obligation-family route exposes all finite-extinction
evidence consumed by the current certificate boundary: the universal
finite-extinction statement, the conditional Poincare endpoint, the completion
payload, and the requested universe-indexed completion criterion.
-/
theorem certificate_payload_of_smoothability_and_subobligations_family
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _finiteExtinction : UniversalFiniteExtinctionStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
    ∃ _payload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
      CompletionCriterionAtUniverse witness :=
  ⟨ universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h
  , poincare_conjecture_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  , poincare_conjecture_payload_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  , completion_criterion_of_smoothability_and_subobligations_family
      witness smoothabilityPackage h extractSphere
  ⟩

/--
The certificate payload above is exactly the tuple of the named universal
finite-extinction boundary, endpoint, completion payload, and criterion
projection constructed from the same smoothability/sub-obligation data.
-/
theorem certificate_payload_of_smoothability_and_subobligations_family_eq
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    certificate_payload_of_smoothability_and_subobligations_family
        witness smoothabilityPackage h extractSphere =
      ⟨ universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
          smoothabilityPackage h
      , poincare_conjecture_of_smoothability_and_subobligations_family
          smoothabilityPackage h extractSphere
      , poincare_conjecture_payload_of_smoothability_and_subobligations_family
          smoothabilityPackage h extractSphere
      , completion_criterion_of_smoothability_and_subobligations_family
          witness smoothabilityPackage h extractSphere
      ⟩ := by
  apply Subsingleton.elim

/--
The same smoothability/sub-obligation-family route exposes the canonical
certificate-facing finite-extinction evidence: universal finite extinction,
the canonical completion target, the canonical completion payload, and a
requested canonical completion criterion.
-/
theorem canonical_certificate_payload_of_smoothability_and_subobligations_family
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _finiteExtinction : UniversalFiniteExtinctionStatement.{u},
    ∃ _target : canonicalCompletionTarget.{u},
    ∃ _payload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
      CompletionCriterionAtUniverse witness :=
  ⟨ universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h
  , canonical_completion_target_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  , canonical_completion_payload_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  , canonical_completion_criterion_of_smoothability_and_subobligations_family
      witness smoothabilityPackage h extractSphere
  ⟩

/--
The canonical certificate payload above is exactly the tuple of the named
universal finite-extinction boundary, canonical endpoint, canonical completion
payload, and canonical criterion projection constructed from the same data.
-/
theorem canonical_certificate_payload_of_smoothability_and_subobligations_family_eq
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_certificate_payload_of_smoothability_and_subobligations_family
        witness smoothabilityPackage h extractSphere =
      ⟨ universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
          smoothabilityPackage h
      , canonical_completion_target_of_smoothability_and_subobligations_family
          smoothabilityPackage h extractSphere
      , canonical_completion_payload_of_smoothability_and_subobligations_family
          smoothabilityPackage h extractSphere
      , canonical_completion_criterion_of_smoothability_and_subobligations_family
          witness smoothabilityPackage h extractSphere
      ⟩ := by
  apply Subsingleton.elim

/--
The smoothability/sub-obligation-family route supplies the public completion
payload and the canonical completion payload from the same universal
finite-extinction boundary.  This is the all-witness certificate-facing shape
needed by final assembly when it must keep both completion targets synchronized
without choosing a witness universe first.
-/
theorem public_and_canonical_certificate_payloads_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ finiteExtinction : UniversalFiniteExtinctionStatement.{u},
      finiteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
            smoothabilityPackage h ∧
        PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let finiteExtinction :=
    universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h
  exact
    ⟨ finiteExtinction
    , rfl
    , poincare_conjecture_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere
    , poincare_conjecture_payload_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere
    , canonical_completion_target_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere
    , canonical_completion_payload_of_smoothability_and_subobligations_family
        smoothabilityPackage h extractSphere
    , fun witness =>
        completion_criterion_of_smoothability_and_subobligations_family
          witness smoothabilityPackage h extractSphere
    ⟩

/--
Opened public/canonical certificate payloads for the
smoothability/sub-obligation-family route.  This names both completion targets,
both payload objects, and the shared all-witness completion-criteria family,
while retaining equalities back to the public and canonical constructors.
-/
theorem public_and_canonical_certificate_payloads_named_targets_and_criteria_of_smoothability_and_subobligations_family
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ finiteExtinction : UniversalFiniteExtinctionStatement.{u},
    ∃ publicTarget : PoincareConjectureStatement.{u},
    ∃ publicPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ canonicalTarget : canonicalCompletionTarget.{u},
    ∃ canonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ allCriteria :
      ∀ witness : Type u, CompletionCriterionAtUniverse witness,
      finiteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
            smoothabilityPackage h ∧
        publicTarget =
          poincare_conjecture_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        publicPayload =
          poincare_conjecture_payload_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        publicPayload = ⟨publicTarget, allCriteria⟩ ∧
        canonicalTarget =
          canonical_completion_target_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        canonicalPayload =
          canonical_completion_payload_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        canonicalPayload = ⟨canonicalTarget, allCriteria⟩ ∧
        allCriteria =
          (fun witness =>
            completion_criterion_of_smoothability_and_subobligations_family
              witness smoothabilityPackage h extractSphere) ∧
        (∀ witness : Type u,
          allCriteria witness =
            canonical_completion_criterion_of_smoothability_and_subobligations_family
              witness smoothabilityPackage h extractSphere) ∧
        PoincareConjectureStatement.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let finiteExtinction :=
    universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
      smoothabilityPackage h
  let publicTarget :=
    poincare_conjecture_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  let publicPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :=
    poincare_conjecture_payload_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  let canonicalTarget :=
    canonical_completion_target_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  let canonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :=
    canonical_completion_payload_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere
  let allCriteria :
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
    fun witness =>
      completion_criterion_of_smoothability_and_subobligations_family
        witness smoothabilityPackage h extractSphere
  exact
    ⟨ finiteExtinction
    , publicTarget
    , publicPayload
    , canonicalTarget
    , canonicalPayload
    , allCriteria
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , rfl
    , by
        intro witness
        apply Subsingleton.elim
    , publicTarget
    , canonicalTarget
    , allCriteria
    ⟩

/--
Witness-specialized opened public/canonical certificate payloads for the
smoothability/sub-obligation-family route.  This keeps the shared all-witness
criteria family and a named criterion for one witness universe synchronized
with both the public and canonical completion payload constructors.
-/
theorem public_and_canonical_certificate_payloads_named_targets_criteria_and_witnessCriterion_of_smoothability_and_subobligations_family
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ finiteExtinction : UniversalFiniteExtinctionStatement.{u},
    ∃ publicTarget : PoincareConjectureStatement.{u},
    ∃ publicPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ canonicalTarget : canonicalCompletionTarget.{u},
    ∃ canonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ allCriteria :
      ∀ witness : Type u, CompletionCriterionAtUniverse witness,
    ∃ witnessCriterion : CompletionCriterionAtUniverse witness,
      finiteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
            smoothabilityPackage h ∧
        publicTarget =
          poincare_conjecture_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        publicPayload =
          poincare_conjecture_payload_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        publicPayload = ⟨publicTarget, allCriteria⟩ ∧
        canonicalTarget =
          canonical_completion_target_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        canonicalPayload =
          canonical_completion_payload_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        canonicalPayload = ⟨canonicalTarget, allCriteria⟩ ∧
        allCriteria =
          (fun witness =>
            completion_criterion_of_smoothability_and_subobligations_family
              witness smoothabilityPackage h extractSphere) ∧
        allCriteria witness = witnessCriterion ∧
        witnessCriterion =
          canonical_completion_criterion_of_smoothability_and_subobligations_family
            witness smoothabilityPackage h extractSphere ∧
        PoincareConjectureStatement.{u} ∧
        canonicalCompletionTarget.{u} ∧
        CompletionCriterionAtUniverse witness := by
  rcases
    public_and_canonical_certificate_payloads_named_targets_and_criteria_of_smoothability_and_subobligations_family
      smoothabilityPackage h extractSphere with
    ⟨ finiteExtinction
    , publicTarget
    , publicPayload
    , canonicalTarget
    , canonicalPayload
    , allCriteria
    , hFiniteExtinction
    , hPublicTarget
    , hPublicPayload
    , hPublicPayloadPair
    , hCanonicalTarget
    , hCanonicalPayload
    , hCanonicalPayloadPair
    , hAllCriteria
    , hAllCriteriaWitness
    , poincareStatement
    , canonicalTargetWitness
    , _allCriteriaWitness
    ⟩
  let witnessCriterion : CompletionCriterionAtUniverse witness :=
    allCriteria witness
  exact
    ⟨ finiteExtinction
    , publicTarget
    , publicPayload
    , canonicalTarget
    , canonicalPayload
    , allCriteria
    , witnessCriterion
    , hFiniteExtinction
    , hPublicTarget
    , hPublicPayload
    , hPublicPayloadPair
    , hCanonicalTarget
    , hCanonicalPayload
    , hCanonicalPayloadPair
    , hAllCriteria
    , rfl
    , hAllCriteriaWitness witness
    , poincareStatement
    , canonicalTargetWitness
    , witnessCriterion
    ⟩

/--
Target-evaluated finite-extinction package data for the
smoothability/sub-obligation-family route, carried together with the public
and canonical certificate payloads.  This exposes the actual selected
finite-extinction surgery package at one manifold and keeps its statement and
Ricci-flow-with-surgery extinction witness synchronized with the package-layer
requirement consumed by final assembly.
-/
theorem finiteExtinctionPackage_requirement_target_package_statement_witness_and_certificate_payloads_of_smoothability_and_subobligations_family
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
            FiniteExtinctionSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ packageRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
    ∃ milestoneRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
    ∃ targetPackage : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M,
    ∃ targetStatement : FiniteExtinctionStatement targetPackage.1 M,
    ∃ targetWitness : FiniteExtinctionByRicciFlowWithSurgery M,
    ∃ finiteExtinction : UniversalFiniteExtinctionStatement.{u},
    ∃ publicTarget : PoincareConjectureStatement.{u},
    ∃ publicPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ canonicalTarget : canonicalCompletionTarget.{u},
    ∃ canonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ allCriteria :
      ∀ witness : Type u, CompletionCriterionAtUniverse witness,
    ∃ witnessCriterion : CompletionCriterionAtUniverse witness,
      packageRequirement =
          finiteExtinctionPackage_requirement_of_subobligations_family h ∧
        milestoneRequirement =
          finiteExtinction_requirement_of_subobligations_family h ∧
        packageRequirement M = ⟨targetPackage⟩ ∧
        targetStatement =
          finite_extinction_statement_of_surgery_package targetPackage.2 ∧
        targetWitness =
          finite_extinction_via_statement_of_surgery_package targetPackage.2 ∧
        finiteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_subobligations_family
            smoothabilityPackage h ∧
        publicTarget =
          poincare_conjecture_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        publicPayload =
          poincare_conjecture_payload_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        publicPayload = ⟨publicTarget, allCriteria⟩ ∧
        canonicalTarget =
          canonical_completion_target_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        canonicalPayload =
          canonical_completion_payload_of_smoothability_and_subobligations_family
            smoothabilityPackage h extractSphere ∧
        canonicalPayload = ⟨canonicalTarget, allCriteria⟩ ∧
        allCriteria =
          (fun witness =>
            completion_criterion_of_smoothability_and_subobligations_family
              witness smoothabilityPackage h extractSphere) ∧
        allCriteria witness = witnessCriterion ∧
        witnessCriterion =
          canonical_completion_criterion_of_smoothability_and_subobligations_family
            witness smoothabilityPackage h extractSphere ∧
        PoincareConjectureStatement.{u} ∧
        canonicalCompletionTarget.{u} ∧
        CompletionCriterionAtUniverse witness := by
  let packageRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage :=
    finiteExtinctionPackage_requirement_of_subobligations_family h
  let milestoneRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction :=
    finiteExtinction_requirement_of_subobligations_family h
  rcases packageRequirement M with ⟨targetPackage⟩
  let targetStatement : FiniteExtinctionStatement targetPackage.1 M :=
    finite_extinction_statement_of_surgery_package targetPackage.2
  let targetWitness : FiniteExtinctionByRicciFlowWithSurgery M :=
    finite_extinction_via_statement_of_surgery_package targetPackage.2
  rcases
    public_and_canonical_certificate_payloads_named_targets_criteria_and_witnessCriterion_of_smoothability_and_subobligations_family
      witness smoothabilityPackage h extractSphere with
    ⟨ finiteExtinction
    , publicTarget
    , publicPayload
    , canonicalTarget
    , canonicalPayload
    , allCriteria
    , witnessCriterion
    , hFiniteExtinction
    , hPublicTarget
    , hPublicPayload
    , hPublicPayloadPair
    , hCanonicalTarget
    , hCanonicalPayload
    , hCanonicalPayloadPair
    , hAllCriteria
    , hAllCriteriaWitness
    , hWitnessCriterion
    , poincareStatement
    , canonicalTargetWitness
    , witnessCriterionWitness
    ⟩
  exact
    ⟨ packageRequirement
    , milestoneRequirement
    , targetPackage
    , targetStatement
    , targetWitness
    , finiteExtinction
    , publicTarget
    , publicPayload
    , canonicalTarget
    , canonicalPayload
    , allCriteria
    , witnessCriterion
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , rfl
    , rfl
    , hFiniteExtinction
    , hPublicTarget
    , hPublicPayload
    , hPublicPayloadPair
    , hCanonicalTarget
    , hCanonicalPayload
    , hCanonicalPayloadPair
    , hAllCriteria
    , hAllCriteriaWitness
    , hWitnessCriterion
    , poincareStatement
    , canonicalTargetWitness
    , witnessCriterionWitness
    ⟩

end Poincare
