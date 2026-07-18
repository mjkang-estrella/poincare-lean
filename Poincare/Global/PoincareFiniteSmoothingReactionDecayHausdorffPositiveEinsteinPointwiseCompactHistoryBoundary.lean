import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffPositiveEinstein
import Poincare.Global.PoincareFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundary

/-!
# Hausdorff reaction-decay compact-history Poincare boundary

This final thin adapter strengthens only the analytic field of the verified
reaction-decay positive-Einstein compact-history boundary.  Its analytic
producer stores scalar-density domination and scalar Laplacian Stokes, then
constructs the moving total-scalar derivative through the corrected
Hausdorff finite-atlas first-variation theorem.

The finite smoothing reduction, its dependent affine-conjugacy package, the
pointwise moving Cartan inputs, and compact-history feedback indexed by those
exact inputs are copied unchanged.  The sphere proof and universal-provider
implication are delegated to the already verified reaction-decay boundary.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- The five-field finite-smoothing/pointwise-Cartan/compact-history boundary
whose analytic field exposes the lower-level Hausdorff scalar-variation
inputs. -/
structure
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3
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
  pointwiseMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
        pointwiseMovingPrimitiveInputs)

/-- Convert only the Hausdorff analytic producer.  All finite-smoothing and
dependent Cartan fields are copied definitionally. -/
noncomputable def
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.toReactionDecayPositiveEinsteinBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let pointwiseMovingPrimitiveInputs :
      FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.pointwiseMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
          pointwiseMovingPrimitiveInputs) :=
    @FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy := plCompatibleAffineConjugacy
    analytic :=
      fixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3_of_hausdorff
        analytic
    pointwiseMovingPrimitiveInputs := pointwiseMovingPrimitiveInputs
    compactHistoryFeedback := compactHistoryFeedback }

/-- The lower-level Hausdorff boundary reaches the sphere conclusion through
the verified reaction-decay positive-Einstein boundary. -/
theorem
    FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toReactionDecayPositiveEinsteinBoundary.sphereConclusion

/-- Universal existence of the finite-smoothing, Hausdorff reaction-decay,
pointwise-moving, compact-history boundary. -/
def
    UniversalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal lower-level Hausdorff reaction producer maps to the verified
reaction-decay boundary and hence implies the canonical Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toReactionDecayPositiveEinsteinBoundary⟩

end Poincare
