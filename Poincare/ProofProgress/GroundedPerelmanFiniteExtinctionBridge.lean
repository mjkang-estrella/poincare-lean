import Poincare.ProofProgress.GroundedFiniteExtinctionCertificate
import Poincare.ProofProgress.GroundedPerelmanSingularityControl

/-!
# Grounded Perelman finite-extinction bridge

This module strengthens the grounded finite-extinction certificate by retaining
`GroundedPerelmanSingularityControl` instead of only the legacy Perelman
package. Every width and frontier field uses the complete package projected
from that same nonvacuous source.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Poincare

universe u

/-- The finite-extinction production chain with its grounded Perelman source
retained through every downstream width and frontier dependency. -/
def GroundedPerelmanFiniteExtinctionProductionCertificate
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
  ∃ groundedPerelmanControl :
      GroundedPerelmanSingularityControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
  ∃ _widthStatement :
      FiniteExtinctionWidthSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery
        groundedPerelmanControl.toPerelmanSingularityControlPackage.control,
  ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction
        groundedPerelmanControl.toPerelmanSingularityControlPackage,
  ∃ volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction
        groundedPerelmanControl.toPerelmanSingularityControlPackage
        curvatureFrontier,
  ∃ surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction
        groundedPerelmanControl.toPerelmanSingularityControlPackage
        curvatureFrontier volumeFrontier,
  ∃ scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction
        groundedPerelmanControl.toPerelmanSingularityControlPackage
        curvatureFrontier volumeFrontier surgeryVolumeFrontier,
    Nonempty
      (FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction
        groundedPerelmanControl.toPerelmanSingularityControlPackage
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier)

/-- Forget the retained nonvacuous Perelman source while preserving the exact
projected package used by every finite-extinction frontier. -/
theorem groundedFiniteExtinctionProductionCertificate_of_groundedPerelman
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedPerelmanFiniteExtinctionProductionCertificate M) :
    GroundedFiniteExtinctionProductionCertificate M := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction,
    groundedPerelmanControl, widthStatement, curvatureFrontier, volumeFrontier,
    surgeryVolumeFrontier, scalarCurvatureFrontier,
    ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    ⟨smooth, n, analyticFoundation, surgeryConstruction,
      groundedPerelmanControl.toPerelmanSingularityControlPackage,
      widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
      scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩

/-- The strengthened certificate reaches the existing finite-extinction
conclusion through its grounded-certificate projection. -/
theorem finiteExtinctionByRicciFlowWithSurgery_of_groundedPerelman
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedPerelmanFiniteExtinctionProductionCertificate M) :
    FiniteExtinctionByRicciFlowWithSurgery M :=
  finiteExtinctionByRicciFlowWithSurgery_of_grounded
    (groundedFiniteExtinctionProductionCertificate_of_groundedPerelman
      grounded)

/-- A full finite-extinction subobligation statement supplies the strengthened
certificate when its Perelman control comes from a retained grounded source.
The construction follows the same width/frontier extraction used by
`groundedFiniteExtinctionProductionCertificate_of_subobligations_statement`,
but stores `groundedPerelmanControl` instead of discarding it. -/
theorem groundedPerelmanFiniteExtinctionProductionCertificate_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
    (surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (groundedPerelmanControl :
      GroundedPerelmanSingularityControl
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation))
    (statement :
      FiniteExtinctionSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery
        groundedPerelmanControl.toPerelmanSingularityControlPackage.control) :
    GroundedPerelmanFiniteExtinctionProductionCertificate M := by
  let perelmanControl :=
    groundedPerelmanControl.toPerelmanSingularityControlPackage
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
  exact
    ⟨inferInstance, n, analyticFoundation, surgeryConstruction,
      groundedPerelmanControl, widthStatement, curvatureFrontier,
      volumeFrontier, surgeryVolumeFrontier, scalarCurvatureFrontier,
      ⟨volumeDifferentialFrontier⟩⟩

end Poincare
