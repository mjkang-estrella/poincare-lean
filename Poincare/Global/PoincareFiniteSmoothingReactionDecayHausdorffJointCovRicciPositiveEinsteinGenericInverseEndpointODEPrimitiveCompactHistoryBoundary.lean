import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundary

/-!
# ODE-primitive generic-inverse compact-history Poincare boundary

This end-to-end adapter lowers the moving endpoint field of the strongest
joint-covariant-Ricci Hausdorff reaction-decay boundary.  It stores the
target-chart ODE comparison provider instead of the already proved
generic-inverse endpoint identity.  ODE uniqueness constructs that identity;
all finite-smoothing, analytic, and dependent compact-history data pass
through unchanged.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- The strongest current joint-covariant-Ricci boundary with its moving
generic-inverse endpoint identity lowered to target-chart ODE comparison
data. -/
structure
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
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
  genericInverseEndpointODEMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        genericInverseEndpointODEMovingPrimitiveInputs)

/-- Use ODE uniqueness to construct only the moving generic-inverse endpoint
identity.  The finite nerve, affine conjugacy, joint-covariant-Ricci analytic
data, and compact-history feedback are copied definitionally. -/
noncomputable def
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.toGenericInverseEndpointBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let odePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.genericInverseEndpointODEMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M :=
    fixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3_of_odePrimitiveInputs
      odePrimitive
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
          primitive) :=
    @FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy := plCompatibleAffineConjugacy
    analytic := analytic
    genericInverseEndpointMovingPrimitiveInputs := primitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The ODE-primitive boundary reaches the sphere conclusion through the
verified strongest joint-covariant-Ricci Hausdorff boundary. -/
theorem
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toGenericInverseEndpointBoundary.sphereConclusion

/-- Universal existence of the ODE-primitive strongest compact-history
boundary. -/
def
    UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the ODE-primitive boundary implies the
repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toGenericInverseEndpointBoundary⟩

end Poincare
