import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinstein
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundary

/-!
# Subordinate-partition generic-inverse compact-history Poincare boundary

This module threads the finite subordinate coordinate proof of scalar Stokes
through the strongest combined analytic and moving-Cartan boundary.  Its
analytic field stores slice-wise partition/flux geometry, not
`ClosedLaplacianStokes`.  The verified finite-sum theorem constructs Stokes;
compactness constructs the uniform covariant-Ricci derivative bound; and the
generic-inverse provider constructs the moving transition packages.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- The strongest five-field producer boundary with scalar Stokes lowered to
finite subordinate Hausdorff coordinate geometry at each nonnegative flow
time. -/
structure
    FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  plCompatibleAffineConjugacy :
    FiniteNervePLCompatibleAffineConjugacy3 finiteNerveReduction
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
        genericInverseEndpointMovingPrimitiveInputs)

/-- Construct scalar Stokes from the finite partition/flux data and retain
the dependent smoothing and moving-Cartan providers definitionally. -/
noncomputable def
    FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.toJointCovRicciBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.genericInverseEndpointMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
          primitive) :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy := plCompatibleAffineConjugacy
    analytic :=
      fixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3_of_subordinatePartition
        analytic
    genericInverseEndpointMovingPrimitiveInputs := primitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The fully lowered boundary reaches the sphere conclusion. -/
theorem
    FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toJointCovRicciBoundary.sphereConclusion

/-- Universal existence of the subordinate-partition, generic-inverse,
compact-history boundary. -/
def
    UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the fully lowered boundary implies the
canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toJointCovRicciBoundary⟩

end Poincare
