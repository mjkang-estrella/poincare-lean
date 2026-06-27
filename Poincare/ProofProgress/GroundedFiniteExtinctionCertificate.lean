/-
Grounded finite-extinction production certificate.

`FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate` stores arbitrary
`Prop` fields with proofs, so it is trivially instantiable and carries no
mathematical content (see INTEGRITY_ASSESSMENT.md).  This module defines the
grounded replacement: a certificate that existentially requires the actual
named analytic, surgery, control, width, and frontier packages.  The grounded
certificate cannot be discharged without supplying that data, and it refines
the legacy certificate through the existing production route.
-/

import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterVolumeDifferential

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
A content-bearing finite-extinction certificate: existence of the full named
production data — a `C¹` structure, an analytic foundation at some smoothness
level, a Ricci-flow-with-surgery construction, Perelman singularity control,
the width subobligations, and the curvature/volume/surgery-volume/scalar-
curvature/volume-differential frontier chain.  Unlike the legacy certificate,
none of these can be replaced by `True`.
-/
def GroundedFiniteExtinctionProductionCertificate
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop :=
  ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
  ∃ n : ℕ∞ω,
  ∃ analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
  ∃ surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
  ∃ perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
  ∃ _widthStatement :
      FiniteExtinctionWidthSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
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
    Nonempty
      (FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier)

/--
The full finite-extinction subobligation statement contains the width-stage
statement as its initial witness block.
-/
theorem finite_extinction_width_subobligations_statement_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    FiniteExtinctionWidthSubobligationsStatement flow surgery control := by
  rcases finite_extinction_subobligations_of_statement statement with
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
      survivingComponentTracking, componentTopology, _pinching,
      _positiveScalarCurvatureLowerBound, _positiveScalarCurvaturePersistence,
      _componentControl, _volumeEvolutionFormula, _surgeryVolumeNonincrease,
      _scalarCurvatureDifferentialInequality, _volumeDifferentialInequality,
      _volumeDecayEstimate, _timeBound, _differentialInequalityIntegration,
      _finiteTimeIntegration, _surgeryTimeSummability,
      _extinctionTimeContradiction, _derivation, _extinction,
      _conclusionDerivation⟩
  exact ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
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

/--
Analytic foundation, surgery construction, Perelman control, and the full
finite-extinction subobligation statement assemble the grounded production
certificate. This is the forward conversion from the older theorem-shaped
subobligation surface to the newer non-vacuous grounded certificate shape.
-/
theorem groundedFiniteExtinctionProductionCertificate_of_subobligations_statement
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
    (statement :
      FiniteExtinctionSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control) :
    GroundedFiniteExtinctionProductionCertificate M := by
  let widthStatement :=
    finite_extinction_width_subobligations_statement_of_subobligations_statement
      statement
  rcases finite_extinction_subobligations_of_statement statement with
    ⟨_finiteFundamentalGroup, _sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth,
      _widthTheory, _firstVariationFormula, _secondVariationInequality,
      _gaussBonnetEstimate, _scalarCurvatureWidthBound, _widthEvolution,
      _widthDifferentialInequality, _surgeryMetricComparison,
      _surgeryWidthComparisonMap, _surgeryWidthDrop, _surgeryDiscardControl,
      _discardedComponentWidthNeutrality, _discardedComponentSweepoutTriviality,
      _discardedComponentClassification, _survivingComponentTracking,
      _componentTopology, pinching, positiveScalarCurvatureLowerBound,
      positiveScalarCurvaturePersistence, componentControl,
      volumeEvolutionFormula, surgeryVolumeNonincrease,
      scalarCurvatureDifferentialInequality, volumeDifferentialInequality,
      _volumeDecayEstimate, _timeBound, _differentialInequalityIntegration,
      _finiteTimeIntegration, _surgeryTimeSummability,
      _extinctionTimeContradiction, _derivation, _extinction,
      _conclusionDerivation⟩
  let curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl :=
    { curvaturePinching := pinching
      positiveScalarCurvatureLowerBound := positiveScalarCurvatureLowerBound
      positiveScalarCurvaturePersistence := positiveScalarCurvaturePersistence
      componentControl := componentControl }
  let volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier :=
    { volumeEvolutionFormula := volumeEvolutionFormula }
  let surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier :=
    { surgeryVolumeNonincrease := surgeryVolumeNonincrease }
  let scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier :=
    { scalarCurvatureDifferentialInequality :=
        scalarCurvatureDifferentialInequality }
  let volumeDifferentialFrontier :
      FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier :=
    { volumeDifferentialInequality := volumeDifferentialInequality }
  exact ⟨(by infer_instance : IsManifold ThreeManifoldModelWithCorners 1 M),
    n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩

/--
A grounded certificate yields the finite-extinction conclusion for its
manifold, by building the legacy production certificate through the existing
volume-differential production route.  The converse direction is unprovable
precisely because the legacy certificate is vacuous.  (The legacy certificate
is `Type`-valued, so the grounded existential can only be eliminated into the
`Prop`-valued conclusion, not into the certificate itself.)
-/
theorem finiteExtinctionByRicciFlowWithSurgery_of_grounded
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    FiniteExtinctionByRicciFlowWithSurgery M := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    .of_production_certificate
      (finite_extinction_production_certificate_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier)

/-- A grounded certificate contains an actual finite-extinction surgery package. -/
theorem finite_extinction_surgery_package_nonempty_of_grounded_certificate
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) := by
  obtain ⟨_smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  exact ⟨⟨n, package⟩⟩

/--
A grounded certificate exposes the full finite-extinction surgery-package
payload: the package itself, its flow/surgery/control data, the theorem-shaped
package statement, the subobligation-derived statement and derivation, and the
final finite-extinction witness.
-/
theorem finite_extinction_statement_payload_of_grounded_certificate
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _packageStatement : @FiniteExtinctionStatement n M _ _ _ _ _ smooth,
      ∃ _subobligationsStatement :
        FiniteExtinctionSubobligationsStatement flow surgery control,
      ∃ _viaSubobligationsStatement :
        @FiniteExtinctionStatement n M _ _ _ _ _ smooth,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionByRicciFlowWithSurgery M := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  rcases finite_extinction_statement_payload_of_surgery_package package with
    ⟨flow, surgery, control, packageStatement, subobligationsStatement,
      viaSubobligationsStatement, derivation, finiteExtinction⟩
  exact
    ⟨n, smooth, package, flow, surgery, control, packageStatement,
      subobligationsStatement, viaSubobligationsStatement, derivation,
      finiteExtinction⟩

/--
A grounded certificate exposes the surgery/Perelman package layer together
with concrete geometric surgery controls.  This projects the construction
package, Perelman package, their theorem-shaped statements, and selected
neck/cap/post-surgery/time-finiteness evidence from the finite-extinction
surgery package built by the grounded frontier chain.
-/
theorem grounded_finite_extinction_surgery_perelman_geometric_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
        PerelmanSingularityControlPackage (n := n) (M := M) flow ∧
        RicciFlowWithSurgeryConstructionStatement flow ∧
        PerelmanSingularityControlStatement flow ∧
        HasSurgeryNeckDecomposition flow ∧
        HasSurgeryCapMetricInterpolation flow ∧
        HasPostSurgeryMetricControl flow ∧
        HasSurgeryTimeLocalFiniteness flow := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  exact
    ⟨n, smooth, package, ricci_flow_data_of_surgery_package package,
      surgery_construction_package_of_surgery_package package,
      perelman_control_package_of_surgery_package package,
      ricci_flow_with_surgery_construction_statement_of_surgery_package package,
      perelman_singularity_control_statement_of_surgery_package package,
      surgery_neck_decomposition_of_surgery_package package,
      surgery_cap_metric_interpolation_of_surgery_package package,
      post_surgery_metric_control_of_surgery_package package,
      surgery_time_local_finiteness_of_surgery_package package⟩

/--
A grounded certificate also exposes the Perelman control outputs used to
prevent collapse and classify singularity models: reduced-volume monotonicity,
kappa-noncollapsing, no-local-collapsing, canonical-neighborhood control, and
singularity-model classification.
-/
theorem grounded_finite_extinction_perelman_noncollapsing_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        HasPerelmanReducedVolumeMonotonicity flow ∧
        HasPerelmanKappaNoncollapsingQuantification flow ∧
        HasNoLocalCollapsingVolumeLowerBound flow ∧
        HasPerelmanNoLocalCollapsing flow ∧
        HasCanonicalNeighborhoodTheorem flow ∧
        HasSingularityModelClassification flow := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  exact
    ⟨n, smooth, package, ricci_flow_data_of_surgery_package package,
      reduced_volume_of_surgery_package package,
      kappa_noncollapsing_of_surgery_package package,
      no_local_collapsing_volume_lower_bound_of_surgery_package package,
      no_local_collapsing_of_surgery_package package,
      canonical_neighborhood_of_surgery_package package,
      singularity_model_classification_of_surgery_package package⟩

/--
A grounded certificate exposes the concrete source records behind the Perelman
noncollapsing and singularity-control interfaces, not just the interface
propositions.  These sources include reduced-volume monotonicity,
kappa-from-reduced-volume, collapsed-ball blowup, no-local-collapsing,
canonical-neighborhood, and singularity-model classification payloads.
-/
theorem grounded_finite_extinction_perelman_noncollapsing_source_evidence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        Nonempty (PerelmanReducedVolumeMonotonicityPayloadSource flow) ∧
        Nonempty (PerelmanKappaNoncollapsingFromReducedVolumePayloadSource flow) ∧
        Nonempty (PerelmanCollapsedBallBlowupPayloadSource flow) ∧
        Nonempty (PerelmanNoLocalCollapsingPayloadSource flow) ∧
        Nonempty (CanonicalNeighborhoodTheoremPayloadSource flow) ∧
        Nonempty (SingularityModelClassificationPayloadSource flow) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  exact
    ⟨n, smooth, package, ricci_flow_data_of_surgery_package package,
      (reduced_volume_of_surgery_package package).reducedVolumeMonotonicityPayload_source,
      (kappa_noncollapsing_of_surgery_package package).kappaNoncollapsingFromReducedVolume
        |>.kappaNoncollapsingFromReducedVolumePayload_source,
      (no_local_collapsing_volume_lower_bound_of_surgery_package package).collapsedBallBlowup
        |>.collapsedBallBlowupPayload_source,
      (no_local_collapsing_of_surgery_package package).noLocalCollapsingPayload_source,
      (canonical_neighborhood_of_surgery_package package).canonicalNeighborhoodTheoremPayload_source,
      (singularity_model_classification_of_surgery_package package).singularityModelClassificationPayload_source⟩

/--
A grounded certificate exposes the sweepout and min-max width source chain:
sweepout construction, continuity, area bound, nontriviality, width definition,
compactness, lower semicontinuity, minimizing sequence, pull-tight,
stationarity, regularity, and positive width.
-/
theorem grounded_finite_extinction_width_minmax_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
      ∃ sweepout :
        HasFiniteExtinctionSweepoutExistence M finiteFundamentalGroup,
      ∃ widthDefinition :
        HasFiniteExtinctionMinMaxWidthDefinition
          flow surgery control finiteFundamentalGroup sweepout,
        Nonempty (FiniteExtinctionSweepoutPayloadSource M finiteFundamentalGroup) ∧
        Nonempty
          (FiniteExtinctionSweepoutContinuityPayloadSource
            M finiteFundamentalGroup sweepout) ∧
        Nonempty
          (FiniteExtinctionSweepoutAreaBoundPayloadSource
            M finiteFundamentalGroup sweepout) ∧
        Nonempty
          (FiniteExtinctionSweepoutNontrivialityPayloadSource
            M finiteFundamentalGroup sweepout) ∧
        Nonempty
          (FiniteExtinctionMinMaxWidthDefinitionPayloadSource
            flow surgery control finiteFundamentalGroup sweepout) ∧
        Nonempty
          (FiniteExtinctionWidthCompactnessPayloadSource
            flow surgery control finiteFundamentalGroup sweepout widthDefinition) ∧
        Nonempty
          (FiniteExtinctionWidthLowerSemicontinuityPayloadSource
            flow surgery control finiteFundamentalGroup sweepout widthDefinition) ∧
        Nonempty
          (FiniteExtinctionMinimizingSequencePayloadSource
            flow surgery control finiteFundamentalGroup sweepout widthDefinition) ∧
        Nonempty
          (FiniteExtinctionPullTightPayloadSource
            flow surgery control finiteFundamentalGroup sweepout widthDefinition) ∧
        Nonempty
          (FiniteExtinctionMinMaxStationarityPayloadSource
            flow surgery control finiteFundamentalGroup sweepout widthDefinition) ∧
        Nonempty
          (FiniteExtinctionMinSurfaceRegularityPayloadSource
            flow surgery control finiteFundamentalGroup sweepout widthDefinition) ∧
        Nonempty
          (FiniteExtinctionPositiveWidthPayloadSource
            flow surgery control finiteFundamentalGroup sweepout widthDefinition) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, _curvatureFrontier, _volumeFrontier,
    _surgeryVolumeFrontier, _scalarCurvatureFrontier,
    _volumeDifferentialFrontier⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨finiteFundamentalGroup, sweepout, _sweepoutParameterSpace,
      sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
      _areaFunctional, widthDefinition, widthCompactness,
      widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
      minMaxStationarity, minSurfaceRegularity, positiveWidth, _widthTheory,
      _firstVariationFormula, _secondVariationInequality, _gaussBonnetEstimate,
      _scalarCurvatureWidthBound, _widthEvolution, _widthDifferentialInequality,
      _surgeryMetricComparison, _surgeryWidthComparisonMap, _surgeryWidthDrop,
      _surgeryDiscardControl, _discardedComponentWidthNeutrality,
      _discardedComponentSweepoutTriviality, _discardedComponentClassification,
      _survivingComponentTracking, _componentTopology⟩
  exact
    ⟨n, smooth, flow, surgery, control, finiteFundamentalGroup, sweepout,
      widthDefinition,
      sweepout.finiteExtinctionSweepoutPayload_source,
      sweepoutContinuity.finiteExtinctionSweepoutContinuityPayload_source,
      sweepoutAreaBound.finiteExtinctionSweepoutAreaBoundPayload_source,
      sweepoutNontriviality.finiteExtinctionSweepoutNontrivialityPayload_source,
      widthDefinition.finiteExtinctionMinMaxWidthDefinitionPayload_source,
      widthCompactness.finiteExtinctionWidthCompactnessPayload_source,
      widthLowerSemicontinuity.finiteExtinctionWidthLowerSemicontinuityPayload_source,
      minimizingSequence.finiteExtinctionMinimizingSequencePayload_source,
      pullTightArgument.finiteExtinctionPullTightPayload_source,
      minMaxStationarity.finiteExtinctionMinMaxStationarityPayload_source,
      minSurfaceRegularity.finiteExtinctionMinSurfaceRegularityPayload_source,
      positiveWidth.finiteExtinctionPositiveWidthPayload_source⟩

/--
A grounded certificate exposes the smooth width-variation source chain:
width theory, first variation, second variation, Gauss-Bonnet, scalar-curvature
width bound, width evolution, and the width differential inequality.
-/
theorem grounded_finite_extinction_width_variation_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
        Nonempty (FiniteExtinctionWidthTheoryPayloadSource flow surgery control) ∧
        Nonempty
          (FiniteExtinctionFirstVariationFormulaPayloadSource
            flow surgery control widthTheory) ∧
        Nonempty
          (FiniteExtinctionSecondVariationInequalityPayloadSource
            flow surgery control widthTheory) ∧
        Nonempty
          (FiniteExtinctionGaussBonnetEstimatePayloadSource
            flow surgery control widthTheory) ∧
        Nonempty
          (FiniteExtinctionScalarCurvatureWidthBoundPayloadSource
            flow surgery control widthTheory) ∧
        Nonempty
          (FiniteExtinctionWidthEvolutionPayloadSource
            flow surgery control widthTheory) ∧
        Nonempty
          (FiniteExtinctionWidthDifferentialInequalityPayloadSource
            flow surgery control widthTheory) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, _curvatureFrontier, _volumeFrontier,
    _surgeryVolumeFrontier, _scalarCurvatureFrontier,
    _volumeDifferentialFrontier⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨_finiteFundamentalGroup, _sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth, widthTheory,
      firstVariationFormula, secondVariationInequality, gaussBonnetEstimate,
      scalarCurvatureWidthBound, widthEvolution, widthDifferentialInequality,
      _surgeryMetricComparison, _surgeryWidthComparisonMap, _surgeryWidthDrop,
      _surgeryDiscardControl, _discardedComponentWidthNeutrality,
      _discardedComponentSweepoutTriviality, _discardedComponentClassification,
      _survivingComponentTracking, _componentTopology⟩
  exact
    ⟨n, smooth, flow, surgery, control, widthTheory,
      widthTheory.finiteExtinctionWidthTheoryPayload_source,
      firstVariationFormula.finiteExtinctionFirstVariationFormulaPayload_source,
      secondVariationInequality.finiteExtinctionSecondVariationInequalityPayload_source,
      gaussBonnetEstimate.finiteExtinctionGaussBonnetEstimatePayload_source,
      scalarCurvatureWidthBound.finiteExtinctionScalarCurvatureWidthBoundPayload_source,
      widthEvolution.finiteExtinctionWidthEvolutionPayload_source,
      widthDifferentialInequality.finiteExtinctionWidthDifferentialInequalityPayload_source⟩

/--
A grounded certificate exposes the surgery-width and discarded-component source
chain: metric comparison, sweepout comparison map, width drop, discard control,
discarded-component neutrality/triviality/classification, surviving-component
tracking, and component topology.
-/
theorem grounded_finite_extinction_surgery_width_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
      ∃ widthEvolution :
        HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
      ∃ discardControl :
        HasFiniteExtinctionSurgeryDiscardControl
          flow surgery control widthTheory widthEvolution,
        Nonempty
          (FiniteExtinctionSurgeryMetricComparisonPayloadSource
            flow surgery control widthTheory widthEvolution) ∧
        Nonempty
          (FiniteExtinctionSurgeryWidthComparisonMapPayloadSource
            flow surgery control widthTheory widthEvolution) ∧
        Nonempty
          (FiniteExtinctionSurgeryWidthDropPayloadSource
            flow surgery control widthTheory widthEvolution) ∧
        Nonempty
          (FiniteExtinctionSurgeryDiscardControlPayloadSource
            flow surgery control widthTheory widthEvolution) ∧
        Nonempty
          (FiniteExtinctionDiscardedComponentWidthNeutralityPayloadSource
            flow surgery control widthTheory widthEvolution discardControl) ∧
        Nonempty
          (FiniteExtinctionDiscardedComponentSweepoutTrivialityPayloadSource
            flow surgery control widthTheory widthEvolution discardControl) ∧
        Nonempty
          (FiniteExtinctionDiscardedComponentClassificationPayloadSource
            flow surgery control widthTheory widthEvolution discardControl) ∧
        Nonempty
          (FiniteExtinctionSurvivingComponentTrackingPayloadSource
            flow surgery control widthTheory widthEvolution discardControl) ∧
        Nonempty
          (FiniteExtinctionComponentTopologyPayloadSource
            flow surgery control widthTheory widthEvolution discardControl) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, _curvatureFrontier, _volumeFrontier,
    _surgeryVolumeFrontier, _scalarCurvatureFrontier,
    _volumeDifferentialFrontier⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨_finiteFundamentalGroup, _sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth, widthTheory,
      _firstVariationFormula, _secondVariationInequality, _gaussBonnetEstimate,
      _scalarCurvatureWidthBound, widthEvolution, _widthDifferentialInequality,
      surgeryMetricComparison, surgeryWidthComparisonMap, surgeryWidthDrop,
      surgeryDiscardControl, discardedComponentWidthNeutrality,
      discardedComponentSweepoutTriviality, discardedComponentClassification,
      survivingComponentTracking, componentTopology⟩
  exact
    ⟨n, smooth, flow, surgery, control, widthTheory, widthEvolution,
      surgeryDiscardControl,
      surgeryMetricComparison.finiteExtinctionSurgeryMetricComparisonPayload_source,
      surgeryWidthComparisonMap.finiteExtinctionSurgeryWidthComparisonMapPayload_source,
      surgeryWidthDrop.finiteExtinctionSurgeryWidthDropPayload_source,
      surgeryDiscardControl.finiteExtinctionSurgeryDiscardControlPayload_source,
      discardedComponentWidthNeutrality.finiteExtinctionDiscardedComponentWidthNeutralityPayload_source,
      discardedComponentSweepoutTriviality.finiteExtinctionDiscardedComponentSweepoutTrivialityPayload_source,
      discardedComponentClassification.finiteExtinctionDiscardedComponentClassificationPayload_source,
      survivingComponentTracking.finiteExtinctionSurvivingComponentTrackingPayload_source,
      componentTopology.finiteExtinctionComponentTopologyPayload_source⟩

/--
A grounded certificate exposes the nested reduced-volume source chain behind
Perelman's monotonicity input: definition, derivative formula, rigidity,
positive lower bound, limit rigidity, nonincreasing control, and the final
monotonicity source record.
-/
theorem grounded_finite_extinction_reduced_volume_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        Nonempty (PerelmanReducedVolumeDefinitionPayloadSource flow) ∧
        Nonempty (PerelmanReducedVolumeDerivativeFormulaPayloadSource flow) ∧
        Nonempty (PerelmanReducedVolumeRigidityPayloadSource flow) ∧
        Nonempty (PerelmanReducedVolumePositiveLowerBoundPayloadSource flow) ∧
        Nonempty (PerelmanReducedVolumeLimitRigidityPayloadSource flow) ∧
        Nonempty (PerelmanReducedVolumeNonincreasingPayloadSource flow) ∧
        Nonempty (PerelmanReducedVolumeMonotonicityPayloadSource flow) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  rcases (reduced_volume_of_surgery_package package).reducedVolumeMonotonicityPayload_source with
    ⟨monotonicitySource⟩
  let nonincreasingSource :=
    monotonicitySource.reducedVolumeNonincreasingSource
  let limitRigiditySource :=
    nonincreasingSource.reducedVolumeLimitRigiditySource
  let positiveLowerBoundSource :=
    limitRigiditySource.reducedVolumePositiveLowerBoundSource
  let rigiditySource :=
    positiveLowerBoundSource.reducedVolumeRigiditySource
  let derivativeFormulaSource :=
    rigiditySource.reducedVolumeDerivativeFormulaSource
  let definitionSource :=
    derivativeFormulaSource.reducedVolumeDefinitionSource
  exact
    ⟨n, smooth, package, ricci_flow_data_of_surgery_package package,
      ⟨definitionSource⟩, ⟨derivativeFormulaSource⟩, ⟨rigiditySource⟩,
      ⟨positiveLowerBoundSource⟩, ⟨limitRigiditySource⟩,
      ⟨nonincreasingSource⟩, ⟨monotonicitySource⟩⟩

/--
A grounded certificate exposes the no-local-collapsing source chain from
kappa noncollapsing via reduced volume, through the contradiction setup and
collapsed-ball blowup, to the final no-local-collapsing source record.
-/
theorem grounded_finite_extinction_no_local_collapsing_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        Nonempty (PerelmanReducedVolumeNonincreasingPayloadSource flow) ∧
        Nonempty (PerelmanKappaNoncollapsingFromReducedVolumePayloadSource flow) ∧
        Nonempty (PerelmanNoLocalCollapsingContradictionSetupPayloadSource flow) ∧
        Nonempty (PerelmanCollapsedBallBlowupPayloadSource flow) ∧
        Nonempty (PerelmanNoLocalCollapsingPayloadSource flow) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  rcases (no_local_collapsing_of_surgery_package package).noLocalCollapsingPayload_source with
    ⟨noLocalSource⟩
  let contradictionSetupSource :=
    noLocalSource.contradictionSetupSource
  let kappaSource :=
    contradictionSetupSource.kappaNoncollapsingFromReducedVolumeSource
  let nonincreasingSource :=
    kappaSource.reducedVolumeNonincreasingSource
  rcases (collapsed_ball_blowup_of_surgery_package package).collapsedBallBlowupPayload_source with
    ⟨collapsedBallBlowupSource⟩
  exact
    ⟨n, smooth, package, ricci_flow_data_of_surgery_package package,
      ⟨nonincreasingSource⟩, ⟨kappaSource⟩, ⟨contradictionSetupSource⟩,
      ⟨collapsedBallBlowupSource⟩, ⟨noLocalSource⟩⟩

/--
A grounded certificate exposes the canonical-neighborhood source chain from
collapsed-ball blowup and Hamilton compactness through ancient-kappa
compactness, scale control, stability, cross-scale persistence, neck/cap
dichotomy, classification, and the final canonical-neighborhood theorem
source record.
-/
theorem grounded_finite_extinction_canonical_neighborhood_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        Nonempty (PerelmanCollapsedBallBlowupPayloadSource flow) ∧
        Nonempty (HamiltonCompactnessPayloadSource flow) ∧
        Nonempty (AncientKappaSolutionCompactnessPayloadSource flow) ∧
        Nonempty (CanonicalNeighborhoodScaleControlPayloadSource flow) ∧
        Nonempty (CanonicalNeighborhoodStabilityPayloadSource flow) ∧
        Nonempty (CanonicalNeighborhoodPersistenceAcrossScalesPayloadSource flow) ∧
        Nonempty (CanonicalNeighborhoodNeckCapDichotomyPayloadSource flow) ∧
        Nonempty (CanonicalNeighborhoodClassificationPayloadSource flow) ∧
        Nonempty (CanonicalNeighborhoodTheoremPayloadSource flow) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  rcases (canonical_neighborhood_of_surgery_package package)
      |>.canonicalNeighborhoodTheoremPayload_source with
    ⟨theoremSource⟩
  let classificationSource :=
    theoremSource.classificationSource
  let neckCapSource :=
    classificationSource.neckCapSource
  let persistenceSource :=
    neckCapSource.persistenceSource
  let stabilitySource :=
    persistenceSource.stabilitySource
  let scaleControlSource :=
    stabilitySource.scaleControlSource
  let ancientCompactnessSource :=
    scaleControlSource.ancientCompactnessSource
  let hamiltonCompactnessSource :=
    ancientCompactnessSource.hamiltonCompactnessSource
  let collapsedBallBlowupSource :=
    hamiltonCompactnessSource.collapsedBallBlowupSource
  exact
    ⟨n, smooth, package, ricci_flow_data_of_surgery_package package,
      ⟨collapsedBallBlowupSource⟩, ⟨hamiltonCompactnessSource⟩,
      ⟨ancientCompactnessSource⟩, ⟨scaleControlSource⟩,
      ⟨stabilitySource⟩, ⟨persistenceSource⟩, ⟨neckCapSource⟩,
      ⟨classificationSource⟩, ⟨theoremSource⟩⟩

/--
A grounded certificate exposes the singularity-model source chain from the
final classification source through asymptotic soliton analysis, nonnegative
curvature-operator control, kappa-solution structure theory, curvature
normalization, pointed rescaling, ancient-kappa limit extraction, Hamilton
compactness, and collapsed-ball blowup.
-/
theorem grounded_finite_extinction_singularity_model_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ _package : @FiniteExtinctionSurgeryPackage n M _ _ _ _ _ smooth,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        Nonempty (PerelmanCollapsedBallBlowupPayloadSource flow) ∧
        Nonempty (HamiltonCompactnessPayloadSource flow) ∧
        Nonempty (AncientKappaSolutionLimitExtractionPayloadSource flow) ∧
        Nonempty (KappaSolutionPointedRescalingPayloadSource flow) ∧
        Nonempty (KappaSolutionCurvatureNormalizationPayloadSource flow) ∧
        Nonempty (KappaSolutionStructureTheoryPayloadSource flow) ∧
        Nonempty (KappaSolutionNonnegativeCurvatureOperatorPayloadSource flow) ∧
        Nonempty (KappaSolutionAsymptoticSolitonPayloadSource flow) ∧
        Nonempty (SingularityModelClassificationPayloadSource flow) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  rcases (singularity_model_classification_of_surgery_package package)
      |>.singularityModelClassificationPayload_source with
    ⟨singularityModelSource⟩
  let asymptoticSolitonSource :=
    singularityModelSource.asymptoticSolitonSource
  let nonnegativeCurvatureOperatorSource :=
    asymptoticSolitonSource.nonnegativeCurvatureOperatorSource
  let structureTheorySource :=
    nonnegativeCurvatureOperatorSource.structureTheorySource
  let curvatureNormalizationSource :=
    structureTheorySource.curvatureNormalizationSource
  let pointedRescalingSource :=
    curvatureNormalizationSource.pointedRescalingSource
  let limitExtractionSource :=
    pointedRescalingSource.limitExtractionSource
  let hamiltonCompactnessSource :=
    limitExtractionSource.hamiltonCompactnessSource
  let collapsedBallBlowupSource :=
    hamiltonCompactnessSource.collapsedBallBlowupSource
  exact
    ⟨n, smooth, package, ricci_flow_data_of_surgery_package package,
      ⟨collapsedBallBlowupSource⟩, ⟨hamiltonCompactnessSource⟩,
      ⟨limitExtractionSource⟩, ⟨pointedRescalingSource⟩,
      ⟨curvatureNormalizationSource⟩, ⟨structureTheorySource⟩,
      ⟨nonnegativeCurvatureOperatorSource⟩, ⟨asymptoticSolitonSource⟩,
      ⟨singularityModelSource⟩⟩

/-- A grounded certificate contains a theorem-shaped finite-extinction statement. -/
theorem finite_extinction_statement_of_grounded_certificate
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        @FiniteExtinctionStatement n M _ _ _ _ _ smooth := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    ⟨n, smooth,
      finite_extinction_statement_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier⟩

/-- A grounded certificate projects the terminal time/decay/final conclusion bundle. -/
theorem grounded_finite_extinction_terminal_evidence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ curvatureFrontier :
        FiniteExtinctionProductionCurvatureFrontier
          analyticFoundation surgeryConstruction perelmanControl,
        HasFiniteExtinctionTimeBound
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
        HasFiniteExtinctionVolumeDecayEstimate
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
        FiniteExtinctionByRicciFlowWithSurgery M := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      curvatureFrontier,
      finite_extinction_time_bound_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_volume_decay_estimate_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier⟩

/--
A grounded certificate exposes the scalar-curvature and volume differential
inequalities before the terminal integration stage.  This keeps the analytic
input used by the extinction estimate available as named evidence instead of
only projecting the final finite-extinction conclusion.
-/
theorem grounded_finite_extinction_scalar_and_volume_differential_evidence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ curvatureFrontier :
        FiniteExtinctionProductionCurvatureFrontier
          analyticFoundation surgeryConstruction perelmanControl,
        HasFiniteExtinctionScalarCurvatureDifferentialInequality
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
        HasFiniteExtinctionVolumeDifferentialInequality
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    _widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, _volumeDifferentialFrontier⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      curvatureFrontier,
      finite_extinction_scalar_and_volume_differential_inequalities_of_scalar_curvature_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier⟩

/--
The grounded certificate also exposes the source records behind the volume
evolution, surgery-volume nonincrease, scalar-curvature differential
inequality, and volume differential inequality interfaces.
-/
theorem grounded_finite_extinction_volume_differential_source_evidence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
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
      ∃ _volumeDifferentialFrontier :
        FiniteExtinctionProductionVolumeDifferentialFrontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier,
        Nonempty
          (FiniteExtinctionVolumeEvolutionFormulaSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl) ∧
        Nonempty
          (FiniteExtinctionSurgeryVolumeNonincreaseSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl) ∧
        Nonempty
          (FiniteExtinctionScalarCurvatureDifferentialInequalitySource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl) ∧
        Nonempty
          (FiniteExtinctionVolumeDifferentialInequalitySource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    _widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      volumeFrontier.volumeEvolutionFormula
        |>.finiteExtinctionVolumeEvolutionFormula_source,
      surgeryVolumeFrontier.surgeryVolumeNonincrease
        |>.finiteExtinctionSurgeryVolumeNonincrease_source,
      scalarCurvatureFrontier.scalarCurvatureDifferentialInequality
        |>.finiteExtinctionScalarCurvatureDifferentialInequality_source,
      volumeDifferentialFrontier.volumeDifferentialInequality
        |>.finiteExtinctionVolumeDifferentialInequality_source⟩

/--
A grounded certificate exposes the common lower source inputs used by both the
terminal time-bound source and the volume-decay source.
-/
theorem grounded_finite_extinction_terminal_time_decay_input_source_chain
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
      ∃ componentControl :
        HasFiniteExtinctionComponentControl flow surgery control pinching,
      ∃ _timeBound :
        HasFiniteExtinctionTimeBound flow surgery control pinching
          componentControl,
      ∃ _volumeDecayEstimate :
        HasFiniteExtinctionVolumeDecayEstimate flow surgery control pinching
          componentControl,
      ∃ timeBoundSource :
        FiniteExtinctionTimeBoundSource flow surgery control pinching
          componentControl,
      ∃ volumeDecaySource :
        FiniteExtinctionVolumeDecayEstimateSource flow surgery control pinching
          componentControl,
      ∃ volumeEvolutionFormula :
        HasFiniteExtinctionVolumeEvolutionFormula flow surgery control pinching
          componentControl,
      ∃ surgeryVolumeNonincrease :
        HasFiniteExtinctionSurgeryVolumeNonincrease flow surgery control pinching
          componentControl,
      ∃ scalarCurvatureDifferentialInequality :
        HasFiniteExtinctionScalarCurvatureDifferentialInequality
          flow surgery control pinching componentControl,
      ∃ volumeDifferentialInequality :
        HasFiniteExtinctionVolumeDifferentialInequality
          flow surgery control pinching componentControl,
        timeBoundSource.volumeEvolutionFormula = volumeEvolutionFormula ∧
        timeBoundSource.surgeryVolumeNonincrease = surgeryVolumeNonincrease ∧
        timeBoundSource.scalarCurvatureDifferentialInequality =
          scalarCurvatureDifferentialInequality ∧
        timeBoundSource.volumeDifferentialInequality =
          volumeDifferentialInequality ∧
        volumeDecaySource.volumeEvolutionFormula = volumeEvolutionFormula ∧
        volumeDecaySource.surgeryVolumeNonincrease = surgeryVolumeNonincrease ∧
        volumeDecaySource.scalarCurvatureDifferentialInequality =
          scalarCurvatureDifferentialInequality ∧
        volumeDecaySource.volumeDifferentialInequality =
          volumeDifferentialInequality := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    _widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  let pinching := curvatureFrontier.curvaturePinching
  let componentControl := curvatureFrontier.componentControl
  let volumeEvolutionFormula := volumeFrontier.volumeEvolutionFormula
  let surgeryVolumeNonincrease := surgeryVolumeFrontier.surgeryVolumeNonincrease
  let scalarCurvatureDifferentialInequality :=
    scalarCurvatureFrontier.scalarCurvatureDifferentialInequality
  let volumeDifferentialInequality :=
    volumeDifferentialFrontier.volumeDifferentialInequality
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let volumeDecayEstimate :=
    finite_extinction_volume_decay_estimate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let timeBoundSource :
      FiniteExtinctionTimeBoundSource flow surgery control pinching
        componentControl :=
    { volumeEvolutionFormula := volumeEvolutionFormula
      surgeryVolumeNonincrease := surgeryVolumeNonincrease
      scalarCurvatureDifferentialInequality :=
        scalarCurvatureDifferentialInequality
      volumeDifferentialInequality := volumeDifferentialInequality }
  let volumeDecaySource :
      FiniteExtinctionVolumeDecayEstimateSource flow surgery control pinching
        componentControl :=
    { volumeEvolutionFormula := volumeEvolutionFormula
      surgeryVolumeNonincrease := surgeryVolumeNonincrease
      scalarCurvatureDifferentialInequality :=
        scalarCurvatureDifferentialInequality
      volumeDifferentialInequality := volumeDifferentialInequality }
  exact
    ⟨n, smooth, flow, surgery, control, pinching, componentControl,
      timeBound, volumeDecayEstimate, timeBoundSource, volumeDecaySource,
      volumeEvolutionFormula, surgeryVolumeNonincrease,
      scalarCurvatureDifferentialInequality, volumeDifferentialInequality,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
A grounded certificate's terminal time-bound and volume-decay source fields are
exactly the volume-evolution, surgery-volume, scalar-curvature, and
volume-differential inputs carried by its frontier chain.
-/
theorem grounded_finite_extinction_terminal_source_fields_are_frontier_inputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
      ∃ componentControl :
        HasFiniteExtinctionComponentControl flow surgery control pinching,
      ∃ timeBound :
        HasFiniteExtinctionTimeBound flow surgery control pinching componentControl,
      ∃ volumeDecayEstimate :
        HasFiniteExtinctionVolumeDecayEstimate flow surgery control pinching componentControl,
      ∃ timeBoundSource :
        FiniteExtinctionTimeBoundSource flow surgery control pinching componentControl,
      ∃ volumeDecaySource :
        FiniteExtinctionVolumeDecayEstimateSource flow surgery control pinching componentControl,
      ∃ volumeEvolutionFormula :
        HasFiniteExtinctionVolumeEvolutionFormula flow surgery control pinching componentControl,
      ∃ surgeryVolumeNonincrease :
        HasFiniteExtinctionSurgeryVolumeNonincrease flow surgery control pinching componentControl,
      ∃ scalarCurvatureDifferentialInequality :
        HasFiniteExtinctionScalarCurvatureDifferentialInequality
          flow surgery control pinching componentControl,
      ∃ volumeDifferentialInequality :
        HasFiniteExtinctionVolumeDifferentialInequality
          flow surgery control pinching componentControl,
        timeBound.finiteExtinctionTimeBound_source = ⟨timeBoundSource⟩ ∧
        volumeDecayEstimate.finiteExtinctionVolumeDecayEstimate_source =
          ⟨volumeDecaySource⟩ ∧
        timeBoundSource.volumeEvolutionFormula = volumeEvolutionFormula ∧
        timeBoundSource.surgeryVolumeNonincrease = surgeryVolumeNonincrease ∧
        timeBoundSource.scalarCurvatureDifferentialInequality =
          scalarCurvatureDifferentialInequality ∧
        timeBoundSource.volumeDifferentialInequality =
          volumeDifferentialInequality ∧
        volumeDecaySource.volumeEvolutionFormula = volumeEvolutionFormula ∧
        volumeDecaySource.surgeryVolumeNonincrease = surgeryVolumeNonincrease ∧
        volumeDecaySource.scalarCurvatureDifferentialInequality =
          scalarCurvatureDifferentialInequality ∧
        volumeDecaySource.volumeDifferentialInequality =
          volumeDifferentialInequality := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    _widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  let pinching := curvatureFrontier.curvaturePinching
  let componentControl := curvatureFrontier.componentControl
  let volumeEvolutionFormula := volumeFrontier.volumeEvolutionFormula
  let surgeryVolumeNonincrease := surgeryVolumeFrontier.surgeryVolumeNonincrease
  let scalarCurvatureDifferentialInequality :=
    scalarCurvatureFrontier.scalarCurvatureDifferentialInequality
  let volumeDifferentialInequality :=
    volumeDifferentialFrontier.volumeDifferentialInequality
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let volumeDecayEstimate :=
    finite_extinction_volume_decay_estimate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let timeBoundSource :
      FiniteExtinctionTimeBoundSource flow surgery control pinching
        componentControl :=
    { volumeEvolutionFormula := volumeEvolutionFormula
      surgeryVolumeNonincrease := surgeryVolumeNonincrease
      scalarCurvatureDifferentialInequality :=
        scalarCurvatureDifferentialInequality
      volumeDifferentialInequality := volumeDifferentialInequality }
  let volumeDecaySource :
      FiniteExtinctionVolumeDecayEstimateSource flow surgery control pinching
        componentControl :=
    { volumeEvolutionFormula := volumeEvolutionFormula
      surgeryVolumeNonincrease := surgeryVolumeNonincrease
      scalarCurvatureDifferentialInequality :=
        scalarCurvatureDifferentialInequality
      volumeDifferentialInequality := volumeDifferentialInequality }
  exact
    ⟨n, smooth, flow, surgery, control, pinching, componentControl,
      timeBound, volumeDecayEstimate, timeBoundSource, volumeDecaySource,
      volumeEvolutionFormula, surgeryVolumeNonincrease,
      scalarCurvatureDifferentialInequality, volumeDifferentialInequality,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
A grounded certificate carries the full terminal derivation chain, not only the
final finite-extinction proposition: the volume-decay estimate is integrated to
a finite time bound, surgery-time losses are summable, the non-extinction
alternative is contradicted, and the conclusion-derivation certificate is
formed from the same named frontier data.
-/
theorem grounded_finite_extinction_conclusion_derivation_evidence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ _widthStatement :
        FiniteExtinctionWidthSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
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
        HasFiniteExtinctionVolumeDecayEstimate
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
        HasFiniteExtinctionDifferentialInequalityIntegration
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
          timeBound ∧
        HasFiniteExtinctionFiniteTimeIntegration
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
          timeBound ∧
        HasFiniteExtinctionSurgeryTimeSummability
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
          timeBound ∧
        HasFiniteExtinctionExtinctionTimeContradiction
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
          timeBound ∧
        ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
          HasFiniteExtinctionConclusionDerivation
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching curvatureFrontier.componentControl
            timeBound derivation finiteExtinction := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
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
  exact
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, timeBound, derivation,
      finite_extinction_volume_decay_estimate_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finite_extinction_differential_inequality_integration_of_volume_differential_frontier
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
      finite_extinction_extinction_time_contradiction_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier,
      finiteExtinction,
      finite_extinction_conclusion_derivation_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier⟩

/--
A grounded certificate assembles the fixed-flow finite-extinction conclusion
statement from the same width, curvature, time-bound, derivation, and terminal
conclusion-derivation inputs carried by the volume-differential frontier.
-/
theorem grounded_finite_extinction_fixed_flow_conclusion_statement
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
      ∃ _conclusionStatement :
        FiniteExtinctionConclusionStatement flow surgery control
          finiteExtinction,
      ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
      ∃ componentControl :
        HasFiniteExtinctionComponentControl flow surgery control pinching,
      ∃ timeBound :
        HasFiniteExtinctionTimeBound flow surgery control pinching
          componentControl,
      ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
        HasFiniteExtinctionConclusionDerivation
          flow surgery control pinching componentControl timeBound derivation
          finiteExtinction := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  let pinching := curvatureFrontier.curvaturePinching
  let componentControl := curvatureFrontier.componentControl
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨finiteFundamentalGroup, sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth, widthTheory,
      _firstVariationFormula, _secondVariationInequality, _gaussBonnetEstimate,
      _scalarCurvatureWidthBound, widthEvolution, _widthDifferentialInequality,
      _surgeryMetricComparison, _surgeryWidthComparisonMap, _surgeryWidthDrop,
      surgeryDiscardControl, _discardedComponentWidthNeutrality,
      _discardedComponentSweepoutTriviality, _discardedComponentClassification,
      _survivingComponentTracking, _componentTopology⟩
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
  let conclusionDerivation :=
    finite_extinction_conclusion_derivation_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let conclusionStatement :
      FiniteExtinctionConclusionStatement flow surgery control
        finiteExtinction :=
    finite_extinction_conclusion_statement_of_components flow surgery control
      finiteExtinction finiteFundamentalGroup sweepout widthTheory
      widthEvolution surgeryDiscardControl pinching componentControl timeBound
      derivation conclusionDerivation
  exact
    ⟨n, smooth, flow, surgery, control, finiteExtinction, conclusionStatement,
      pinching, componentControl, timeBound, derivation, conclusionDerivation⟩

/--
A grounded certificate also exposes the source records behind the terminal
finite-extinction derivation chain: time bound, volume decay, both integration
steps, surgery-time summability, extinction-time contradiction, and the final
conclusion derivation source.
-/
theorem grounded_finite_extinction_terminal_derivation_source_evidence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
      ∃ componentControl :
        HasFiniteExtinctionComponentControl flow surgery control pinching,
      ∃ timeBound :
        HasFiniteExtinctionTimeBound flow surgery control pinching
          componentControl,
      ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
      ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
        Nonempty
          (FiniteExtinctionTimeBoundSource
            flow surgery control pinching componentControl) ∧
        Nonempty
          (FiniteExtinctionVolumeDecayEstimateSource
            flow surgery control pinching componentControl) ∧
        Nonempty
          (FiniteExtinctionDifferentialInequalityIntegrationSource
            flow surgery control pinching componentControl timeBound) ∧
        Nonempty
          (FiniteExtinctionFiniteTimeIntegrationSource
            flow surgery control pinching componentControl timeBound) ∧
        Nonempty
          (FiniteExtinctionSurgeryTimeSummabilitySource
            flow surgery control pinching componentControl timeBound) ∧
        Nonempty
          (FiniteExtinctionExtinctionTimeContradictionSource
            flow surgery control pinching componentControl timeBound) ∧
        Nonempty
          (FiniteExtinctionConclusionDerivationSource
            flow surgery control pinching componentControl timeBound
            derivation finiteExtinction) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  let pinching := curvatureFrontier.curvaturePinching
  let componentControl := curvatureFrontier.componentControl
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
    ⟨n, smooth, flow, surgery, control, pinching, componentControl,
      timeBound, derivation, finiteExtinction,
      timeBound.finiteExtinctionTimeBound_source,
      volumeDecay.finiteExtinctionVolumeDecayEstimate_source,
      differentialIntegration.finiteExtinctionDifferentialInequalityIntegration_source,
      finiteTimeIntegration.finiteExtinctionFiniteTimeIntegration_source,
      surgeryTimeSummability.finiteExtinctionSurgeryTimeSummability_source,
      extinctionTimeContradiction.finiteExtinctionExtinctionTimeContradiction_source,
      conclusionDerivation.finiteExtinctionConclusionDerivation_source⟩

/--
A grounded certificate constructs the fixed-flow finite-extinction statement
and exposes the terminal source records used to derive it from the
volume-differential frontier.
-/
theorem grounded_finite_extinction_statement_terminal_source_bundle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
        @FiniteExtinctionStatement n M _ _ _ _ _ smooth ∧
        FiniteExtinctionConclusionStatement flow surgery control
          finiteExtinction ∧
        ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
        ∃ componentControl :
          HasFiniteExtinctionComponentControl flow surgery control pinching,
        ∃ timeBound :
          HasFiniteExtinctionTimeBound flow surgery control pinching
            componentControl,
        ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
          Nonempty
            (FiniteExtinctionTimeBoundSource
              flow surgery control pinching componentControl) ∧
          Nonempty
            (FiniteExtinctionVolumeDecayEstimateSource
              flow surgery control pinching componentControl) ∧
          Nonempty
            (FiniteExtinctionDifferentialInequalityIntegrationSource
              flow surgery control pinching componentControl timeBound) ∧
          Nonempty
            (FiniteExtinctionFiniteTimeIntegrationSource
              flow surgery control pinching componentControl timeBound) ∧
          Nonempty
            (FiniteExtinctionSurgeryTimeSummabilitySource
              flow surgery control pinching componentControl timeBound) ∧
          Nonempty
            (FiniteExtinctionExtinctionTimeContradictionSource
              flow surgery control pinching componentControl timeBound) ∧
          Nonempty
            (FiniteExtinctionConclusionDerivationSource
              flow surgery control pinching componentControl timeBound
              derivation finiteExtinction) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  let pinching := curvatureFrontier.curvaturePinching
  let componentControl := curvatureFrontier.componentControl
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨finiteFundamentalGroup, sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth, widthTheory,
      _firstVariationFormula, _secondVariationInequality, _gaussBonnetEstimate,
      _scalarCurvatureWidthBound, widthEvolution, _widthDifferentialInequality,
      _surgeryMetricComparison, _surgeryWidthComparisonMap, _surgeryWidthDrop,
      surgeryDiscardControl, _discardedComponentWidthNeutrality,
      _discardedComponentSweepoutTriviality, _discardedComponentClassification,
      _survivingComponentTracking, _componentTopology⟩
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
  let conclusionDerivation :=
    finite_extinction_conclusion_derivation_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let conclusionStatement :
      FiniteExtinctionConclusionStatement flow surgery control
        finiteExtinction :=
    finite_extinction_conclusion_statement_of_components flow surgery control
      finiteExtinction finiteFundamentalGroup sweepout widthTheory
      widthEvolution surgeryDiscardControl pinching componentControl timeBound
      derivation conclusionDerivation
  let finiteExtinctionStatement :
      @FiniteExtinctionStatement n M _ _ _ _ _ smooth :=
    ⟨flow, surgery, control, finiteExtinction, conclusionStatement⟩
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
  exact
    ⟨n, smooth, flow, surgery, control, finiteExtinction,
      finiteExtinctionStatement, conclusionStatement, pinching,
      componentControl, timeBound, derivation,
      timeBound.finiteExtinctionTimeBound_source,
      volumeDecay.finiteExtinctionVolumeDecayEstimate_source,
      differentialIntegration.finiteExtinctionDifferentialInequalityIntegration_source,
      finiteTimeIntegration.finiteExtinctionFiniteTimeIntegration_source,
      surgeryTimeSummability.finiteExtinctionSurgeryTimeSummability_source,
      extinctionTimeContradiction.finiteExtinctionExtinctionTimeContradiction_source,
      conclusionDerivation.finiteExtinctionConclusionDerivation_source⟩

/--
A grounded certificate reconstructs a theorem-shaped finite-extinction
statement from the same terminal witness whose conclusion derivation carries a
source record.  The displayed statement proof is the literal existential stack
built from the exposed flow, surgery, control, finite-extinction witness, and
conclusion statement.
-/
theorem grounded_finite_extinction_statement_terminal_witness_coherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
      ∃ conclusionStatement :
        FiniteExtinctionConclusionStatement flow surgery control
          finiteExtinction,
      ∃ statement : @FiniteExtinctionStatement n M _ _ _ _ _ smooth,
      ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
      ∃ componentControl :
        HasFiniteExtinctionComponentControl flow surgery control pinching,
      ∃ timeBound :
        HasFiniteExtinctionTimeBound flow surgery control pinching
          componentControl,
      ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
      ∃ _conclusionDerivation :
        HasFiniteExtinctionConclusionDerivation
          flow surgery control pinching componentControl timeBound derivation
          finiteExtinction,
        statement =
          ⟨flow, surgery, control, finiteExtinction, conclusionStatement⟩ ∧
        Nonempty
          (FiniteExtinctionConclusionDerivationSource
            flow surgery control pinching componentControl timeBound
            derivation finiteExtinction) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let flow := ricci_flow_data_of_analytic_foundation_package analyticFoundation
  let surgery := surgeryConstruction.withSurgery
  let control := perelmanControl.control
  let pinching := curvatureFrontier.curvaturePinching
  let componentControl := curvatureFrontier.componentControl
  rcases finite_extinction_width_subobligations_of_statement widthStatement with
    ⟨finiteFundamentalGroup, sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth, widthTheory,
      _firstVariationFormula, _secondVariationInequality, _gaussBonnetEstimate,
      _scalarCurvatureWidthBound, widthEvolution, _widthDifferentialInequality,
      _surgeryMetricComparison, _surgeryWidthComparisonMap, _surgeryWidthDrop,
      surgeryDiscardControl, _discardedComponentWidthNeutrality,
      _discardedComponentSweepoutTriviality, _discardedComponentClassification,
      _survivingComponentTracking, _componentTopology⟩
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
  let conclusionDerivation :=
    finite_extinction_conclusion_derivation_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let conclusionStatement :
      FiniteExtinctionConclusionStatement flow surgery control
        finiteExtinction :=
    finite_extinction_conclusion_statement_of_components flow surgery control
      finiteExtinction finiteFundamentalGroup sweepout widthTheory
      widthEvolution surgeryDiscardControl pinching componentControl timeBound
      derivation conclusionDerivation
  let statement : @FiniteExtinctionStatement n M _ _ _ _ _ smooth :=
    ⟨flow, surgery, control, finiteExtinction, conclusionStatement⟩
  exact
    ⟨n, smooth, flow, surgery, control, finiteExtinction,
      conclusionStatement, statement, pinching, componentControl, timeBound,
      derivation, conclusionDerivation, rfl,
      conclusionDerivation.finiteExtinctionConclusionDerivation_source⟩

/--
A grounded certificate exposes the terminal conclusion-derivation source whose
stored production certificate is exactly the certificate used to define the
finite-extinction witness.
-/
theorem grounded_finite_extinction_terminal_source_certificate_coherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ _widthStatement :
        FiniteExtinctionWidthSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
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
      ∃ _volumeDifferentialFrontier :
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
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl,
      ∃ derivation :
        HasFiniteExtinctionDerivation
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
      ∃ source :
        FiniteExtinctionConclusionDerivationSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl timeBound derivation
          finiteExtinction,
        source.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          source.conclusionCertificate = finiteExtinction := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let derivation :=
    finite_extinction_derivation_of_width_statement
      analyticFoundation surgeryConstruction perelmanControl widthStatement
  let productionCertificate :=
    finite_extinction_production_certificate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let finiteExtinction :=
    FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
      productionCertificate
  let source :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching
        curvatureFrontier.componentControl timeBound derivation
        finiteExtinction :=
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
  exact
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation, source,
      rfl, source.conclusionEq⟩

/--
A grounded certificate exposes the concrete witness fields stored in the
finite-extinction production certificate: the flow, surgery/control, width,
curvature, time-bound, and derivation entries are the named grounded frontier
payloads, and the terminal time-bound and derivation entries still carry their
source records.
-/
theorem grounded_finite_extinction_production_certificate_witness_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ widthStatement :
        FiniteExtinctionWidthSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
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
      ∃ timeBound :
        HasFiniteExtinctionTimeBound
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl,
      ∃ derivation :
        HasFiniteExtinctionDerivation
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
        productionCertificate =
          finite_extinction_production_certificate_of_volume_differential_frontier
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement curvatureFrontier volumeFrontier
            surgeryVolumeFrontier scalarCurvatureFrontier
            volumeDifferentialFrontier ∧
        productionCertificate.flowEvidence =
          Nonempty (RicciFlowData ThreeManifoldModelWithCorners n M) ∧
        productionCertificate.surgeryEvidence =
          HasRicciFlowWithSurgery n M ∧
        productionCertificate.controlEvidence =
          HasPerelmanSingularityControl (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation) ∧
        productionCertificate.widthEvidence =
          FiniteExtinctionWidthSubobligationsStatement
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control ∧
        productionCertificate.curvatureEvidence =
          HasFiniteExtinctionCurvaturePinching
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control ∧
        productionCertificate.timeBoundEvidence =
          HasFiniteExtinctionTimeBound
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl ∧
        productionCertificate.derivationEvidence =
          HasFiniteExtinctionDerivation
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control ∧
        timeBound =
          finite_extinction_time_bound_of_volume_differential_frontier
            analyticFoundation surgeryConstruction perelmanControl
            curvatureFrontier volumeFrontier surgeryVolumeFrontier
            scalarCurvatureFrontier volumeDifferentialFrontier ∧
        derivation =
          finite_extinction_derivation_of_width_statement
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement ∧
        Nonempty
          (FiniteExtinctionTimeBoundSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl) ∧
        Nonempty
          (FiniteExtinctionDerivationSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let productionCertificate :=
    finite_extinction_production_certificate_of_volume_differential_frontier
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
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, timeBound, derivation, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, timeBound.finiteExtinctionTimeBound_source,
      derivation.finiteExtinctionDerivation_source⟩

/--
A grounded certificate reconstructs the two named finite-extinction production
remainder interfaces after the volume-differential and scalar-curvature
frontiers. This packages the terminal conclusion derivation back into the
frontier-remainder surfaces used by the production chain.
-/
theorem grounded_finite_extinction_production_remainder_evidence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ widthStatement :
        FiniteExtinctionWidthSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
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
        FiniteExtinctionProductionPackageRemainderAfterVolumeDifferential
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier widthStatement volumeFrontier
          surgeryVolumeFrontier scalarCurvatureFrontier
          volumeDifferentialFrontier ∧
        FiniteExtinctionProductionPackageRemainderAfterScalarCurvature
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let volumeDifferentialRemainder :=
    finite_extinction_production_remainder_after_volume_differential_of_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  exact
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      volumeDifferentialRemainder,
      finite_extinction_production_remainder_after_scalar_curvature_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
        volumeDifferentialRemainder⟩

/--
The grounded universal finite-extinction statement: every compact simply
connected topological 3-manifold carries a grounded certificate.  This is the
honest restatement of the Ricci-flow pillar — unlike
`UniversalFiniteExtinctionStatement`, it is not a tautology.
-/
def GroundedUniversalFiniteExtinctionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      GroundedFiniteExtinctionProductionCertificate M

/--
The grounded pillar implies the legacy pillar, so the existing assembly route
to the Poincare statement remains available from grounded data.
-/
theorem universalFiniteExtinctionStatement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} :=
  fun M _ _ _ _ _ =>
    finiteExtinctionByRicciFlowWithSurgery_of_grounded (grounded M)

/-- A grounded universal finite-extinction pillar supplies the finite-extinction package layer. -/
theorem finiteExtinctionPackage_requirement_of_grounded_universal
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage := by
  intro M _top _t2 _charted _simple _compact _smooth
  exact finite_extinction_surgery_package_nonempty_of_grounded_certificate
    (grounded M)

/--
A grounded universal finite-extinction pillar supplies an actual indexed
surgery package for each smooth compact simply connected target, not only the
legacy proposition.
-/
theorem finite_extinction_surgery_package_nonempty_of_grounded_universal
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) :=
  finite_extinction_surgery_package_nonempty_of_grounded_certificate
    (grounded M)

/--
A grounded universal finite-extinction pillar supplies a theorem-shaped
finite-extinction statement for each compact simply connected target.
-/
theorem finite_extinction_statement_of_grounded_universal
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        @FiniteExtinctionStatement n M _ _ _ _ _ smooth :=
  finite_extinction_statement_of_grounded_certificate
    (grounded M)

/--
The grounded universal pillar supplies the terminal time, volume-decay, and
finite-extinction conclusion bundle for each compact simply connected target.
-/
theorem grounded_universal_finite_extinction_terminal_evidence
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ curvatureFrontier :
        FiniteExtinctionProductionCurvatureFrontier
          analyticFoundation surgeryConstruction perelmanControl,
        HasFiniteExtinctionTimeBound
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
        HasFiniteExtinctionVolumeDecayEstimate
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
        FiniteExtinctionByRicciFlowWithSurgery M :=
  grounded_finite_extinction_terminal_evidence
    (grounded M)

/--
For a smooth compact simply connected target, the grounded universal pillar
packages the three concrete finite-extinction outputs used by later assembly:
an indexed surgery package, a theorem-shaped extinction statement, and terminal
time/volume evidence.
-/
theorem grounded_universal_finite_extinction_output_bundle
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
      (∃ n : ℕ∞ω,
        ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
      (∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ analyticFoundation :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ perelmanControl :
          PerelmanSingularityControlPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ curvatureFrontier :
          FiniteExtinctionProductionCurvatureFrontier
            analyticFoundation surgeryConstruction perelmanControl,
          HasFiniteExtinctionTimeBound
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
          HasFiniteExtinctionVolumeDecayEstimate
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
          FiniteExtinctionByRicciFlowWithSurgery M) :=
  ⟨finite_extinction_surgery_package_nonempty_of_grounded_universal grounded M,
    finite_extinction_statement_of_grounded_universal grounded M,
    grounded_universal_finite_extinction_terminal_evidence grounded M⟩

/--
The grounded universal pillar supplies a single downstream payload combining the
statement layer, the production certificate, the finite-extinction witness, the
terminal source/coherence record, and the universal output bundle.  This is a
real proof assembly from the existing grounded endpoints rather than an alias for
any one of them.
-/
theorem grounded_universal_finite_extinction_downstream_payload
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    (∃ n : ℕ∞ω,
      ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
      (∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ analyticFoundation :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ perelmanControl :
          PerelmanSingularityControlPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ widthStatement :
          FiniteExtinctionWidthSubobligationsStatement
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
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
        ∃ _timeBound :
          HasFiniteExtinctionTimeBound
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl,
        ∃ _derivation :
          HasFiniteExtinctionDerivation
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
          productionCertificate =
            finite_extinction_production_certificate_of_volume_differential_frontier
              analyticFoundation surgeryConstruction perelmanControl
              widthStatement curvatureFrontier volumeFrontier
              surgeryVolumeFrontier scalarCurvatureFrontier
              volumeDifferentialFrontier ∧
          Nonempty
            (FiniteExtinctionTimeBoundSource
              (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl) ∧
          Nonempty
            (FiniteExtinctionDerivationSource
              (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)) ∧
      (∃ n : ℕ∞ω,
        ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
          @FiniteExtinctionStatement n M _ _ _ _ _ smooth ∧
          FiniteExtinctionConclusionStatement flow surgery control
            finiteExtinction) ∧
      (∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ analyticFoundation :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ perelmanControl :
          PerelmanSingularityControlPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ _widthStatement :
          FiniteExtinctionWidthSubobligationsStatement
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
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
        ∃ _volumeDifferentialFrontier :
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
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl,
        ∃ derivation :
          HasFiniteExtinctionDerivation
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
        ∃ source :
          FiniteExtinctionConclusionDerivationSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl timeBound derivation
            finiteExtinction,
          source.conclusionCertificate = productionCertificate ∧
          FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
            source.conclusionCertificate = finiteExtinction) ∧
      (Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
        (∃ n : ℕ∞ω,
          ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
            @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
        (∃ n : ℕ∞ω,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
          ∃ curvatureFrontier :
            FiniteExtinctionProductionCurvatureFrontier
              analyticFoundation surgeryConstruction perelmanControl,
            HasFiniteExtinctionTimeBound
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            HasFiniteExtinctionVolumeDecayEstimate
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            FiniteExtinctionByRicciFlowWithSurgery M)) := by
  let groundedCertificate := grounded M
  rcases finite_extinction_statement_of_grounded_universal grounded M with
    ⟨statementN, statementSmooth, statement⟩
  rcases grounded_finite_extinction_production_certificate_witness_payload
      groundedCertificate with
    ⟨productionN, productionSmooth, analyticFoundation, surgeryConstruction,
      perelmanControl, widthStatement, curvatureFrontier, volumeFrontier,
      surgeryVolumeFrontier, scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, timeBound, derivation, productionEq, _flowEvidence,
      _surgeryEvidence, _controlEvidence, _widthEvidence, _curvatureEvidence,
      _timeBoundEvidence, _derivationEvidence, _timeBoundEq, _derivationEq,
      timeBoundSource, derivationSource⟩
  rcases grounded_finite_extinction_statement_terminal_source_bundle
      groundedCertificate with
    ⟨terminalN, terminalSmooth, flow, surgery, control, finiteExtinction,
      terminalStatement, conclusionStatement, _pinching, _componentControl,
      _terminalTimeBound, _terminalDerivation, _timeBoundSource,
      _volumeDecaySource, _differentialIntegrationSource,
      _finiteTimeIntegrationSource, _surgeryTimeSummabilitySource,
      _extinctionTimeContradictionSource, _conclusionDerivationSource⟩
  rcases grounded_finite_extinction_terminal_source_certificate_coherence
      groundedCertificate with
    ⟨coherenceN, coherenceSmooth, coherenceAnalyticFoundation,
      coherenceSurgeryConstruction, coherencePerelmanControl,
      coherenceWidthStatement, coherenceCurvatureFrontier,
      coherenceVolumeFrontier, coherenceSurgeryVolumeFrontier,
      coherenceScalarCurvatureFrontier, coherenceVolumeDifferentialFrontier,
      coherenceProductionCertificate, coherenceFiniteExtinction,
      coherenceTimeBound, coherenceDerivation, coherenceSource,
      coherenceCertificateEq, coherenceConclusionEq⟩
  rcases grounded_universal_finite_extinction_output_bundle grounded M with
    ⟨packageOutput, statementOutput, terminalOutput⟩
  exact
    ⟨⟨statementN, statementSmooth, statement⟩,
      ⟨productionN, productionSmooth, analyticFoundation, surgeryConstruction,
        perelmanControl, widthStatement, curvatureFrontier, volumeFrontier,
        surgeryVolumeFrontier, scalarCurvatureFrontier,
        volumeDifferentialFrontier, productionCertificate, timeBound,
        derivation, productionEq, timeBoundSource, derivationSource⟩,
      ⟨terminalN, terminalSmooth, flow, surgery, control, finiteExtinction,
        terminalStatement, conclusionStatement⟩,
      ⟨coherenceN, coherenceSmooth, coherenceAnalyticFoundation,
        coherenceSurgeryConstruction, coherencePerelmanControl,
        coherenceWidthStatement, coherenceCurvatureFrontier,
        coherenceVolumeFrontier, coherenceSurgeryVolumeFrontier,
        coherenceScalarCurvatureFrontier, coherenceVolumeDifferentialFrontier,
        coherenceProductionCertificate, coherenceFiniteExtinction,
        coherenceTimeBound, coherenceDerivation, coherenceSource,
        coherenceCertificateEq, coherenceConclusionEq⟩,
      ⟨packageOutput, statementOutput, terminalOutput⟩⟩

/--
The grounded universal pillar can be consumed as one endpoint that exposes an
actual indexed surgery package, the global package-layer requirement, the
target-level statement/terminal output, and the production/coherence payloads
needed by downstream assembly.
-/
theorem grounded_universal_finite_extinction_package_requirement_payload_coherence
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ _packageWitness : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M,
      Nonempty (FiniteExtinctionSurgeryPackage _packageWitness.1 M) ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
      (∃ n : ℕ∞ω,
        ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
      (∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ analyticFoundation :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation),
        ∃ perelmanControl :
          PerelmanSingularityControlPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation),
        ∃ curvatureFrontier :
          FiniteExtinctionProductionCurvatureFrontier
            analyticFoundation surgeryConstruction perelmanControl,
          HasFiniteExtinctionTimeBound
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl ∧
          HasFiniteExtinctionVolumeDecayEstimate
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl ∧
          FiniteExtinctionByRicciFlowWithSurgery M) ∧
      (∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ analyticFoundation :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ perelmanControl :
          PerelmanSingularityControlPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ widthStatement :
          FiniteExtinctionWidthSubobligationsStatement
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
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
        ∃ _timeBound :
          HasFiniteExtinctionTimeBound
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl,
        ∃ _derivation :
          HasFiniteExtinctionDerivation
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
          productionCertificate =
            finite_extinction_production_certificate_of_volume_differential_frontier
              analyticFoundation surgeryConstruction perelmanControl
              widthStatement curvatureFrontier volumeFrontier
              surgeryVolumeFrontier scalarCurvatureFrontier
              volumeDifferentialFrontier ∧
          Nonempty
            (FiniteExtinctionTimeBoundSource
              (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl) ∧
          Nonempty
            (FiniteExtinctionDerivationSource
              (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control)) ∧
      (∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ analyticFoundation :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ perelmanControl :
          PerelmanSingularityControlPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ _widthStatement :
          FiniteExtinctionWidthSubobligationsStatement
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
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
        ∃ _volumeDifferentialFrontier :
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
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl,
        ∃ derivation :
          HasFiniteExtinctionDerivation
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
        ∃ source :
          FiniteExtinctionConclusionDerivationSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl timeBound derivation
            finiteExtinction,
          source.conclusionCertificate = productionCertificate ∧
          FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
            source.conclusionCertificate = finiteExtinction) := by
  rcases grounded_universal_finite_extinction_output_bundle grounded M with
    ⟨packageOutput, statementOutput, terminalOutput⟩
  rcases packageOutput with ⟨packageWitness⟩
  rcases grounded_universal_finite_extinction_downstream_payload grounded M with
    ⟨_downstreamStatement, productionLayer, _terminalLayer, coherenceLayer,
      _downstreamOutput⟩
  exact
    ⟨packageWitness,
      ⟨packageWitness.2⟩,
      finiteExtinctionPackage_requirement_of_grounded_universal grounded,
      ⟨packageWitness⟩, statementOutput, terminalOutput, productionLayer,
      coherenceLayer⟩

/--
The grounded universal pillar can be consumed as one full certificate endpoint:
the legacy universal statement, the package-layer requirement, the universal
output bundle, the downstream production/source payload, and the package
requirement/coherence payload are all recovered from the same grounded input.
The proof destructures the existing output, downstream, and coherence payloads
before reassembling them, so this is a genuine source theorem rather than a
ledger alias.
-/
theorem grounded_universal_finite_extinction_full_certificate_bundle
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
      (∃ n : ℕ∞ω,
        ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
      (∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ analyticFoundation :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ perelmanControl :
          PerelmanSingularityControlPackage (n := n) (M := M)
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        ∃ curvatureFrontier :
          FiniteExtinctionProductionCurvatureFrontier
            analyticFoundation surgeryConstruction perelmanControl,
          HasFiniteExtinctionTimeBound
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
          HasFiniteExtinctionVolumeDecayEstimate
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching curvatureFrontier.componentControl ∧
          FiniteExtinctionByRicciFlowWithSurgery M) := by
  rcases grounded_universal_finite_extinction_output_bundle grounded M with
    ⟨packageOutput, statementOutput, terminalOutput⟩
  exact
    ⟨universalFiniteExtinctionStatement_of_grounded grounded,
      finiteExtinctionPackage_requirement_of_grounded_universal grounded,
      packageOutput,
      statementOutput,
      terminalOutput⟩

/--
**Step 3697 source.** The grounded universal finite-extinction pillar now
exposes one package witness together with the universal statement, package
requirement, theorem-shaped statement output, and terminal extinction evidence.

Reference source: the proof destructures
`grounded_universal_finite_extinction_full_certificate_bundle` for the legacy
universal statement, package-layer requirement, theorem-shaped statement, and
terminal time/volume extinction evidence.  It also destructures
`grounded_universal_finite_extinction_package_requirement_payload_coherence` to
recover an indexed finite-extinction surgery package witness and its pointwise
nonempty proof.  The result is a stronger downstream endpoint than either
source theorem alone.
-/
theorem grounded_universal_finite_extinction_witness_statement_terminal_bundle
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      ∃ packageWitness : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M,
        Nonempty (FiniteExtinctionSurgeryPackage packageWitness.1 M) ∧
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
        (∃ n : ℕ∞ω,
          ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
            @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
        (∃ n : ℕ∞ω,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
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
          ∃ curvatureFrontier :
            FiniteExtinctionProductionCurvatureFrontier
              analyticFoundation surgeryConstruction perelmanControl,
            HasFiniteExtinctionTimeBound
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            HasFiniteExtinctionVolumeDecayEstimate
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            FiniteExtinctionByRicciFlowWithSurgery M) := by
  rcases
      grounded_universal_finite_extinction_full_certificate_bundle
        grounded M with
    ⟨universalStatement, packageRequirement, packageOutput,
      statementOutput, terminalOutput⟩
  rcases
      grounded_universal_finite_extinction_package_requirement_payload_coherence
        grounded M with
    ⟨packageWitness, packageWitnessNonempty, _packageRequirement,
      _packageOutput, _statementOutput, _terminalOutput,
      _productionLayer, _coherenceLayer⟩
  exact
    ⟨universalStatement, packageRequirement, packageWitness,
      packageWitnessNonempty, packageOutput, statementOutput, terminalOutput⟩

/--
**Step 3703 source.** The grounded universal finite-extinction pillar now
keeps the downstream production and coherence payloads attached to the same
terminal witness bundle.

Reference source: this proof destructs
`grounded_universal_finite_extinction_witness_statement_terminal_bundle` to
recover the universal statement, package-layer requirement, indexed surgery
package witness, theorem-shaped finite-extinction statement, and terminal
time/volume extinction evidence.  It also destructs
`grounded_universal_finite_extinction_package_requirement_payload_coherence`
to carry the production-layer payload and conclusion-coherence payload from the
same grounded input.  The endpoint therefore records the witness, statement,
terminal evidence, production source, and coherence source together.
-/
theorem grounded_universal_finite_extinction_terminal_witness_production_coherence_bundle
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      ∃ packageWitness : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M,
        Nonempty (FiniteExtinctionSurgeryPackage packageWitness.1 M) ∧
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
        (∃ n : ℕ∞ω,
          ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
            @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
        (∃ n : ℕ∞ω,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
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
          ∃ curvatureFrontier :
            FiniteExtinctionProductionCurvatureFrontier
              analyticFoundation surgeryConstruction perelmanControl,
            HasFiniteExtinctionTimeBound
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            HasFiniteExtinctionVolumeDecayEstimate
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            FiniteExtinctionByRicciFlowWithSurgery M) ∧
        (∃ n : ℕ∞ω,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
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
          ∃ widthStatement :
            FiniteExtinctionWidthSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control,
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
          ∃ _timeBound :
            HasFiniteExtinctionTimeBound
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl,
          ∃ _derivation :
            HasFiniteExtinctionDerivation
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control,
            productionCertificate =
              finite_extinction_production_certificate_of_volume_differential_frontier
                analyticFoundation surgeryConstruction perelmanControl
                widthStatement curvatureFrontier volumeFrontier
                surgeryVolumeFrontier scalarCurvatureFrontier
                volumeDifferentialFrontier ∧
            Nonempty
              (FiniteExtinctionTimeBoundSource
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
                surgeryConstruction.withSurgery perelmanControl.control
                curvatureFrontier.curvaturePinching
                curvatureFrontier.componentControl) ∧
            Nonempty
              (FiniteExtinctionDerivationSource
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
                surgeryConstruction.withSurgery perelmanControl.control)) ∧
        (∃ n : ℕ∞ω,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
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
          ∃ _widthStatement :
            FiniteExtinctionWidthSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control,
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
          ∃ _volumeDifferentialFrontier :
            FiniteExtinctionProductionVolumeDifferentialFrontier
              analyticFoundation surgeryConstruction perelmanControl
              curvatureFrontier volumeFrontier surgeryVolumeFrontier
              scalarCurvatureFrontier,
          ∃ productionCertificate :
            FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M,
          ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
          ∃ timeBound :
            HasFiniteExtinctionTimeBound
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl,
          ∃ derivation :
            HasFiniteExtinctionDerivation
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control,
          ∃ source :
            FiniteExtinctionConclusionDerivationSource
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl timeBound derivation
              finiteExtinction,
            source.conclusionCertificate = productionCertificate ∧
            FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
              source.conclusionCertificate = finiteExtinction) := by
  rcases
      grounded_universal_finite_extinction_witness_statement_terminal_bundle
        grounded M with
    ⟨universalStatement, packageRequirement, packageWitness,
      packageWitnessNonempty, packageOutput, statementOutput, terminalOutput⟩
  rcases
      grounded_universal_finite_extinction_package_requirement_payload_coherence
        grounded M with
    ⟨_coherencePackageWitness, _coherencePackageWitnessNonempty,
      _coherencePackageRequirement, _coherencePackageOutput,
      _coherenceStatementOutput, _coherenceTerminalOutput,
      productionLayer, coherenceLayer⟩
  exact
    ⟨universalStatement, packageRequirement, packageWitness,
      packageWitnessNonempty, packageOutput, statementOutput, terminalOutput,
      productionLayer, coherenceLayer⟩

/--
**Step 3709 source.** A grounded finite-extinction certificate carries one
canonical production certificate, terminal finite-extinction witness, and
conclusion source record, with explicit equalities tying all three back to the
same volume-differential frontier payload.

Reference source: the proof destructs the grounded certificate, builds the
canonical time-bound, derivation, production certificate, terminal witness, and
conclusion source from the exposed frontier chain, and records the equality
contracts that downstream assembly can reuse without re-opening the grounded
existential.
-/
theorem grounded_finite_extinction_production_terminal_equality_contract
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ widthStatement :
        FiniteExtinctionWidthSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
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
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl,
      ∃ derivation :
        HasFiniteExtinctionDerivation
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
      ∃ source :
        FiniteExtinctionConclusionDerivationSource
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control
          curvatureFrontier.curvaturePinching
          curvatureFrontier.componentControl timeBound derivation
          finiteExtinction,
        productionCertificate =
          finite_extinction_production_certificate_of_volume_differential_frontier
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement curvatureFrontier volumeFrontier
            surgeryVolumeFrontier scalarCurvatureFrontier
            volumeDifferentialFrontier ∧
        finiteExtinction =
          FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
            productionCertificate ∧
        timeBound =
          finite_extinction_time_bound_of_volume_differential_frontier
            analyticFoundation surgeryConstruction perelmanControl
            curvatureFrontier volumeFrontier surgeryVolumeFrontier
            scalarCurvatureFrontier volumeDifferentialFrontier ∧
        derivation =
          finite_extinction_derivation_of_width_statement
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement ∧
        source.conclusionCertificate = productionCertificate ∧
        FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
          source.conclusionCertificate = finiteExtinction ∧
        Nonempty
          (FiniteExtinctionTimeBoundSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl) ∧
        Nonempty
          (FiniteExtinctionDerivationSource
            (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let timeBound :=
    finite_extinction_time_bound_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let derivation :=
    finite_extinction_derivation_of_width_statement
      analyticFoundation surgeryConstruction perelmanControl widthStatement
  let productionCertificate :=
    finite_extinction_production_certificate_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  let finiteExtinction :=
    FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
      productionCertificate
  let source :
      FiniteExtinctionConclusionDerivationSource
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control
        curvatureFrontier.curvaturePinching
        curvatureFrontier.componentControl timeBound derivation
        finiteExtinction :=
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
  exact
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation, source,
      rfl, rfl, rfl, rfl, rfl, source.conclusionEq,
      timeBound.finiteExtinctionTimeBound_source,
      derivation.finiteExtinctionDerivation_source⟩

/-- Theorem contract for `grounded_finite_extinction_production_terminal_equality_contract`. -/
theorem grounded_finite_extinction_production_terminal_equality_contract_eq :
    @Poincare.grounded_finite_extinction_production_terminal_equality_contract =
      @Poincare.grounded_finite_extinction_production_terminal_equality_contract :=
  rfl

/--
A grounded universal finite-extinction pillar supplies a single target route
that keeps the package witness, theorem-shaped statement output, terminal
time/volume output, and the canonical production/conclusion-source equality
chain together.  The proof deliberately composes the universal witness bundle
with the target-level production terminal equality contract, so downstream
assembly can cite one endpoint instead of re-opening both grounded existential
payloads independently.
-/
theorem grounded_universal_finite_extinction_terminal_package_equality_route
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      ∃ packageWitness : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M,
        Nonempty (FiniteExtinctionSurgeryPackage packageWitness.1 M) ∧
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) ∧
        (∃ n : ℕ∞ω,
          ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
            @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
        (∃ n : ℕ∞ω,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
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
          ∃ curvatureFrontier :
            FiniteExtinctionProductionCurvatureFrontier
              analyticFoundation surgeryConstruction perelmanControl,
            HasFiniteExtinctionTimeBound
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            HasFiniteExtinctionVolumeDecayEstimate
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl ∧
            FiniteExtinctionByRicciFlowWithSurgery M) ∧
        ∃ n : ℕ∞ω,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
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
          ∃ widthStatement :
            FiniteExtinctionWidthSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control,
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
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl,
          ∃ derivation :
            HasFiniteExtinctionDerivation
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control,
          ∃ source :
            FiniteExtinctionConclusionDerivationSource
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control
              curvatureFrontier.curvaturePinching
              curvatureFrontier.componentControl timeBound derivation
              finiteExtinction,
            productionCertificate =
              finite_extinction_production_certificate_of_volume_differential_frontier
                analyticFoundation surgeryConstruction perelmanControl
                widthStatement curvatureFrontier volumeFrontier
                surgeryVolumeFrontier scalarCurvatureFrontier
                volumeDifferentialFrontier ∧
            finiteExtinction =
              FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
                productionCertificate ∧
            timeBound =
              finite_extinction_time_bound_of_volume_differential_frontier
                analyticFoundation surgeryConstruction perelmanControl
                curvatureFrontier volumeFrontier surgeryVolumeFrontier
                scalarCurvatureFrontier volumeDifferentialFrontier ∧
            derivation =
              finite_extinction_derivation_of_width_statement
                analyticFoundation surgeryConstruction perelmanControl
                widthStatement ∧
            source.conclusionCertificate = productionCertificate ∧
            FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
              source.conclusionCertificate = finiteExtinction ∧
            Nonempty
              (FiniteExtinctionTimeBoundSource
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
                surgeryConstruction.withSurgery perelmanControl.control
                curvatureFrontier.curvaturePinching
                curvatureFrontier.componentControl) ∧
            Nonempty
              (FiniteExtinctionDerivationSource
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
                surgeryConstruction.withSurgery perelmanControl.control) := by
  rcases
      grounded_universal_finite_extinction_terminal_witness_production_coherence_bundle
        grounded M with
    ⟨universalStatement, packageRequirement, packageWitness,
      packageWitnessNonempty, packageOutput, statementOutput, terminalOutput,
      _productionLayer, _coherenceLayer⟩
  rcases grounded_finite_extinction_production_terminal_equality_contract
      (grounded M) with
    ⟨n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier,
      surgeryVolumeFrontier, scalarCurvatureFrontier,
      volumeDifferentialFrontier, productionCertificate, finiteExtinction,
      timeBound, derivation, source, productionEq, finiteExtinctionEq,
      timeBoundEq, derivationEq, sourceCertificateEq, sourceConclusionEq,
      timeBoundSource, derivationSource⟩
  exact
    ⟨universalStatement, packageRequirement, packageWitness,
      packageWitnessNonempty, packageOutput, statementOutput, terminalOutput,
      n, smooth, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation, source,
      productionEq, finiteExtinctionEq, timeBoundEq, derivationEq,
      sourceCertificateEq, sourceConclusionEq, timeBoundSource,
      derivationSource⟩

/--
The terminal equality route has a smaller consumer-facing projection: from the
same grounded universal pillar, downstream assembly can cite the universal
finite-extinction statement, the dependency-layer package requirement, the
pointwise theorem-shaped statement, and the canonical production/source
equalities without destructing the indexed package witness.
-/
theorem grounded_universal_finite_extinction_statement_terminal_equality_payload
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      (∃ n : ℕ∞ω,
        ∃ smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          @FiniteExtinctionStatement n M _ _ _ _ _ smooth) ∧
      ∃ n : ℕ∞ω,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
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
        ∃ widthStatement :
          FiniteExtinctionWidthSubobligationsStatement
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
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
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl,
        ∃ derivation :
          HasFiniteExtinctionDerivation
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control,
        ∃ source :
          FiniteExtinctionConclusionDerivationSource
            (ricci_flow_data_of_analytic_foundation_package
              analyticFoundation)
            surgeryConstruction.withSurgery perelmanControl.control
            curvatureFrontier.curvaturePinching
            curvatureFrontier.componentControl timeBound derivation
            finiteExtinction,
          productionCertificate =
            finite_extinction_production_certificate_of_volume_differential_frontier
              analyticFoundation surgeryConstruction perelmanControl
              widthStatement curvatureFrontier volumeFrontier
              surgeryVolumeFrontier scalarCurvatureFrontier
              volumeDifferentialFrontier ∧
          finiteExtinction =
            FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
              productionCertificate ∧
          source.conclusionCertificate = productionCertificate ∧
          FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
            source.conclusionCertificate = finiteExtinction := by
  rcases
      grounded_universal_finite_extinction_terminal_package_equality_route
        grounded M with
    ⟨universalStatement, packageRequirement, _packageWitness,
      _packageWitnessNonempty, _packageOutput, statementOutput,
      _terminalOutput, n, smooth, analyticFoundation, surgeryConstruction,
      perelmanControl, widthStatement, curvatureFrontier, volumeFrontier,
      surgeryVolumeFrontier, scalarCurvatureFrontier,
      volumeDifferentialFrontier, productionCertificate, finiteExtinction,
      timeBound, derivation, source, productionEq, finiteExtinctionEq,
      _timeBoundEq, _derivationEq, sourceCertificateEq,
      sourceConclusionEq, _timeBoundSource, _derivationSource⟩
  exact
    ⟨universalStatement, packageRequirement, statementOutput, n, smooth,
      analyticFoundation, surgeryConstruction, perelmanControl, widthStatement,
      curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, volumeDifferentialFrontier,
      productionCertificate, finiteExtinction, timeBound, derivation, source,
      productionEq, finiteExtinctionEq, sourceCertificateEq,
      sourceConclusionEq⟩

/--
Theorem contract for
`grounded_universal_finite_extinction_statement_terminal_equality_payload`.
-/
theorem grounded_universal_finite_extinction_statement_terminal_equality_payload_eq :
    @Poincare.grounded_universal_finite_extinction_statement_terminal_equality_payload =
      @Poincare.grounded_universal_finite_extinction_statement_terminal_equality_payload :=
  rfl

/--
Theorem contract for
`grounded_universal_finite_extinction_terminal_package_equality_route`.
-/
theorem grounded_universal_finite_extinction_terminal_package_equality_route_eq :
    @Poincare.grounded_universal_finite_extinction_terminal_package_equality_route =
      @Poincare.grounded_universal_finite_extinction_terminal_package_equality_route :=
  rfl

end Poincare
