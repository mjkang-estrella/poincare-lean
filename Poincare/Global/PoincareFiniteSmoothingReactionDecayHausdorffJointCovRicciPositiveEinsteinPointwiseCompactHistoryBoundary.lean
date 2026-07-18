import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciPositiveEinstein
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundary

/-!
# Joint-covariant-Ricci compact-history Poincare boundary

This adapter places the compact-maximum covariant-Ricci reduction into the
strongest finite-smoothing, pointwise-moving, compact-history boundary.  Its
analytic field stores joint continuity of `|∇ Ric|²` on the compact metric
family rather than a selected global bound and a separate bound proof.

All dependent smoothing and Cartan fields are copied definitionally.  The
only conversion is the analytic compact-maximum construction.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- The strongest five-field boundary with covariant-Ricci control generated
from compact joint continuity. -/
structure
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3
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
  pointwiseMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
        pointwiseMovingPrimitiveInputs)

/-- Convert only the analytic joint-continuity field.  The dependent
smoothing and Cartan values are retained exactly. -/
noncomputable def
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.toHausdorffBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let pointwiseMovingPrimitiveInputs :
      FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.pointwiseMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
          pointwiseMovingPrimitiveInputs) :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy := plCompatibleAffineConjugacy
    analytic :=
      fixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3_of_jointCovRicci
        analytic
    pointwiseMovingPrimitiveInputs := pointwiseMovingPrimitiveInputs
    compactHistoryFeedback := compactHistoryFeedback }

/-- The joint-continuity boundary reaches the sphere through the verified
Hausdorff boundary. -/
theorem
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toHausdorffBoundary.sphereConclusion

/-- Universal existence of the lower-level joint-continuity boundary. -/
def
    UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal compact joint-covariant-Ricci producer implies the canonical
topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toHausdorffBoundary⟩

end Poincare
