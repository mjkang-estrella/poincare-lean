import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundary

/-!
# Generic-inverse endpoint Hausdorff reaction-decay Poincare boundary

This thin end-to-end adapter lowers the moving Cartan field of the strongest
current Hausdorff reaction-decay compact-history boundary.  Instead of an
already assembled pointwise transition package, it stores the five-field
generic-inverse endpoint primitive provider.  That provider generates the
positive endpoint radius, endpoint-domain bookkeeping, transition package,
and fixed-to-preferred centerwise continuity before delegating to the
verified boundary.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- The strongest current five-field producer boundary with the moving
fixed-chart endpoint comparison reduced to one generic-inverse manifold
identity at each center. -/
structure
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  plCompatibleAffineConjugacy :
    FiniteNervePLCompatibleAffineConjugacy3 finiteNerveReduction
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
        genericInverseEndpointMovingPrimitiveInputs)

/-- Assemble only the moving transition packages and delegate to the verified
Hausdorff reaction-decay pointwise boundary. -/
noncomputable def
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.toPointwiseBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.genericInverseEndpointMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let pointwise : FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M :=
    fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_genericInverseEndpointPrimitiveInputs
      primitive
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
          primitive) :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy := plCompatibleAffineConjugacy
    analytic := analytic
    pointwiseMovingPrimitiveInputs := pointwise
    compactHistoryFeedback := compactHistoryFeedback }

/-- The lowered moving-endpoint boundary reaches the sphere conclusion through
the verified Hausdorff reaction-decay boundary. -/
theorem
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toPointwiseBoundary.sphereConclusion

/-- Universal existence of the lowered generic-inverse endpoint boundary. -/
def
    UniversalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the lowered boundary implies the repository's
canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toPointwiseBoundary⟩

end Poincare
