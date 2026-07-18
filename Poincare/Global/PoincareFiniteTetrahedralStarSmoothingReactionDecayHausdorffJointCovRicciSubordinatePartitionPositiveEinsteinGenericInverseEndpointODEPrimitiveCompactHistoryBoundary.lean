import Poincare.Global.SmoothabilityFiniteTetrahedralStarReduction
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary

/-!
# Fully geometric tetrahedral-star compact-history Poincare boundary

This module combines the three strongest verified producer reductions in one
end-to-end boundary:

* developed charts and a finite tangent-compatible tetrahedral presentation
  replace the already constructed PL-compatible affine conjugacy;
* finite subordinate partitions and compactly supported coordinate fluxes
  replace scalar Laplacian Stokes on every nonnegative flow slice; and
* target-chart ODE comparison data replace the moving generic-inverse endpoint
  identity.

The finite atlas nerve is shared definitionally with the tetrahedral
presentation and its starwise tangent condition.  The subordinate-partition
analytic data, ODE primitives, and dependent compact-history feedback pass to
the existing doubly lowered boundary without alteration.  Only the affine
conjugacy is constructed here, using finite closed-star localization followed
by the verified affine-germ invertibility theorem.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityFiniteTetrahedralStarReduction

/-- The strongest current compact-history producer boundary with finite
smoothing, scalar Stokes, and the moving endpoint identity all lowered to
their geometric inputs. -/
structure
    FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  tetrahedralTransitionPresentation :
    FiniteTetrahedralPLTransitionPresentation3
      finiteNerveReduction.atlas finiteNerveReduction.transitions
  starwiseTangentCompatible :
    StarwiseTangentCompatible3 tetrahedralTransitionPresentation
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointODEMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        genericInverseEndpointODEMovingPrimitiveInputs)

/-- Construct the PL-compatible affine conjugacy from the developed
tetrahedral star.  The finite nerve, subordinate-partition analytic data, ODE
primitives, and dependent compact-history feedback are copied definitionally
to the already verified subordinate-partition and ODE-primitive boundary. -/
noncomputable def
    FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.toSubordinatePartitionODEPrimitiveBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let tetrahedralTransitionPresentation :
      FiniteTetrahedralPLTransitionPresentation3
        finiteNerveReduction.atlas finiteNerveReduction.transitions :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.tetrahedralTransitionPresentation
      M _ _ ambientChartedSpace _ _ data
  let starwiseTangentCompatible :
      StarwiseTangentCompatible3 tetrahedralTransitionPresentation :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.starwiseTangentCompatible
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let odePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.genericInverseEndpointODEMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
          odePrimitive) :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy :=
      finiteNervePLCompatibleAffineConjugacy3_of_tetrahedralStar
        finiteNerveReduction tetrahedralTransitionPresentation
        starwiseTangentCompatible
    analytic := analytic
    genericInverseEndpointODEMovingPrimitiveInputs := odePrimitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The fully geometric boundary reaches the sphere conclusion through the
verified subordinate-partition and ODE-primitive boundary. -/
theorem
    FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toSubordinatePartitionODEPrimitiveBoundary.sphereConclusion

/-- Universal existence of the fully geometric strongest compact-history
boundary. -/
def
    UniversalFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the fully geometric boundary implies the
repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toSubordinatePartitionODEPrimitiveBoundary⟩

end Poincare
