import Poincare.Global.SmoothabilityFiniteTetrahedralStarReduction
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary

/-!
# Tetrahedral-star, ODE-primitive compact-history Poincare boundary

This end-to-end adapter lowers the finite-smoothing field of the strongest
joint-covariant-Ricci, ODE-primitive, compact-history boundary.  Instead of
storing an already constructed PL-compatible affine conjugacy, it stores
developed vertex charts, a finite tetrahedral presentation of every corrected
nerve transition, and equality of the affine linear parts on tetrahedra
incident to each corrected compact-domain point.

Finite closed-star localization constructs an open incident-star
neighborhood.  Equality of the incident linear parts and the common
transition value then identify all affine formulas on that star.  The
verified affine-germ invertibility reduction turns those local affine maps
into the affine equivalences required by the downstream smoothing boundary.

The finite atlas nerve remains the dependency shared by the presentation and
its tangent condition.  Joint-covariant-Ricci analytic data, moving
target-chart ODE primitives, and dependent compact-history feedback pass
through definitionally.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityFiniteTetrahedralStarReduction

/-- The strongest current joint-covariant-Ricci, ODE-primitive,
compact-history boundary with its finite smoothing input lowered to a finite
tetrahedral presentation and the exact incident-star tangent condition. -/
structure
    FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
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
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointODEMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        genericInverseEndpointODEMovingPrimitiveInputs)

/-- Construct only the PL-compatible affine conjugacy from the developed
tetrahedral star data.  The finite nerve and every analytic, moving, and
history field are retained definitionally. -/
noncomputable def
    FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.toODEPrimitiveBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let tetrahedralTransitionPresentation :
      FiniteTetrahedralPLTransitionPresentation3
        finiteNerveReduction.atlas finiteNerveReduction.transitions :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.tetrahedralTransitionPresentation
      M _ _ ambientChartedSpace _ _ data
  let starwiseTangentCompatible :
      StarwiseTangentCompatible3 tetrahedralTransitionPresentation :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.starwiseTangentCompatible
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let odePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.genericInverseEndpointODEMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
          odePrimitive) :=
    @FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.compactHistoryFeedback
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

/-- The tetrahedral-star, ODE-primitive boundary reaches the sphere
conclusion through the verified strongest joint-covariant-Ricci boundary. -/
theorem
    FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toODEPrimitiveBoundary.sphereConclusion

/-- Universal existence of the tetrahedral-star, ODE-primitive strongest
compact-history boundary. -/
def
    UniversalFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the tetrahedral-star, ODE-primitive boundary
implies the repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toODEPrimitiveBoundary⟩

end Poincare
