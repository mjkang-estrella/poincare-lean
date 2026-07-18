import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciPositiveEinstein
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundary

/-!
# Joint-covariant-Ricci and generic-inverse endpoint Poincare boundary

This is the common strengthening of the current analytic and moving-Cartan
reductions.  The analytic field stores joint continuity of `|∇ Ric|²` on its
compact metric family, and the moving field stores only the generic-inverse
manifold endpoint identity at each fixed-chart center.  Compactness constructs
the former uniform bound; generic joint regularity constructs the latter
radius and domain bookkeeping.

The finite smoothing and compact-history values remain dependent on the exact
finite nerve and moving provider stored in this record.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- The combined strongest five-field producer boundary. -/
structure
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  plCompatibleAffineConjugacy :
    FiniteNervePLCompatibleAffineConjugacy3 finiteNerveReduction
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
        genericInverseEndpointMovingPrimitiveInputs)

/-- Convert only the compact analytic joint-continuity field.  The dependent
finite-smoothing and moving-Cartan data are copied definitionally. -/
noncomputable def
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.toGenericInverseEndpointBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.genericInverseEndpointMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
          primitive) :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy := plCompatibleAffineConjugacy
    analytic :=
      fixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3_of_jointCovRicci
        analytic
    genericInverseEndpointMovingPrimitiveInputs := primitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The combined lowered boundary reaches the sphere conclusion. -/
theorem
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toGenericInverseEndpointBoundary.sphereConclusion

/-- Universal existence of the combined lowered boundary. -/
def
    UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the combined lower-level boundary implies the
canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toGenericInverseEndpointBoundary⟩

end Poincare
