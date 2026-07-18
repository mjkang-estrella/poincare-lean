import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayPositiveEinstein
import Poincare.Global.PoincareFiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundary

/-!
# Reaction-decay positive-Einstein compact-history Poincare boundary

This is a thin strongest-boundary adapter.  It replaces the finite-energy
analytic field of the established five-field boundary by reaction-decay
positive-Einstein data.  The reaction package proves finite total forward
traceless-Ricci energy, so its analytic field converts to the established
finite-energy contract after the smoothing fields install a smooth atlas.

The finite nerve, its PL-compatible affine conjugacy, the pointwise moving
Cartan inputs, and the compact-history feedback dependent on those exact
inputs are copied definitionally.  Sphere recognition and the universal
Poincare implication are delegated to the verified finite-energy boundary;
the long smoothing/Cartan/analytic composition proof is not repeated here.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- Pointwise specialization of the fixed-target reaction producer followed
by its proved conversion to the finite-traceless-energy contract.  This
helper is deliberately stated without an ambient charted-space instance, so
the smooth atlas quantified by the fixed-target contract is the unique atlas
used in the conversion. -/
noncomputable def
    fixedTargetNormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3_of_reactionDecay
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M) :
    FixedTargetNormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
      M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact data.toFiniteTracelessEnergyPositiveEinsteinAnalyticData3

/-- The strongest reaction-decay version of the verified five-field
finite-energy compact-history boundary.

Only `analytic` is strengthened.  In particular, the final feedback field is
indexed by the moving-input value constructed from this record's preceding
pointwise primitive field, so no unrelated Cartan package can be stored. -/
structure
    FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  plCompatibleAffineConjugacy :
    FiniteNervePLCompatibleAffineConjugacy3 finiteNerveReduction
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3.{u, v}
      M
  pointwiseMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
        pointwiseMovingPrimitiveInputs)

/-- Forget only the stronger reaction-decay producer, mapping it through its
proved finite-traceless-energy conversion.  All smoothing and dependent
Cartan fields are copied exactly. -/
noncomputable def
    FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.toFiniteTracelessEnergyBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let pointwiseMovingPrimitiveInputs :
      FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M :=
    @FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.pointwiseMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
          pointwiseMovingPrimitiveInputs) :=
    @FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy := plCompatibleAffineConjugacy
    analytic :=
      fixedTargetNormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3_of_reactionDecay
        analytic
    pointwiseMovingPrimitiveInputs := pointwiseMovingPrimitiveInputs
    compactHistoryFeedback := compactHistoryFeedback }

/-- The reaction-decay boundary reaches the sphere conclusion through the
verified finite-energy five-field boundary. -/
theorem
    FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toFiniteTracelessEnergyBoundary.sphereConclusion

/-- Universal existence of the strongest reaction-decay positive-Einstein,
pointwise-moving, compact-history boundary data. -/
def
    UniversalFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal reaction-decay producer maps to the verified finite-energy
universal boundary and hence implies the canonical Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toFiniteTracelessEnergyBoundary⟩

end Poincare
