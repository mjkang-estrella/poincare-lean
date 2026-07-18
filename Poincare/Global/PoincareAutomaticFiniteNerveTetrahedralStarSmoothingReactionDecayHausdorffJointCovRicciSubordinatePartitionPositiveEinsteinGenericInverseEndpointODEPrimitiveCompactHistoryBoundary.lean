import Poincare.Global.PoincareFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary

/-!
# Automatic finite-nerve, fully geometric Poincare boundary

The finite precompact atlas and its transition nerve are automatic on every
compact Hausdorff three-charted space.  They should therefore not be a field
of the universal Poincare producer boundary.

This module removes that field.  Its remaining smoothing input is a provider
which, for a selected finite atlas-nerve reduction, constructs developed
charts, a finite tetrahedral presentation of every corrected compact
transition, and matching affine linear parts on every incident star.  A
finite nerve is selected from the verified existence theorem using classical
choice; the provider is then evaluated at exactly that reduction.

The subordinate-partition analytic data and moving target-chart ODE inputs
are independent of this selection.  Compact-history feedback retains only
its genuine dependency on the ODE inputs.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityFiniteTetrahedralStarReduction

/-- A producer of the exact tetrahedral-star smoothing input for any selected
finite atlas-nerve reduction.  The finite nerve itself is not supplied by the
producer. -/
def FiniteTetrahedralStarPresentationProvider3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [CompactSpace M] : Prop :=
  ∀ reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M,
    ∃ input : FiniteTetrahedralPLTransitionPresentation3
        reduction.atlas reduction.transitions,
      StarwiseTangentCompatible3 input

/-- The fully geometric strongest boundary after deleting its automatic
finite atlas-nerve field.  Analytic data and ODE inputs do not depend on the
classically selected nerve; compact-history feedback depends only on the ODE
inputs, as required by its target type. -/
structure
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointODEMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        genericInverseEndpointODEMovingPrimitiveInputs)

/-- Select an automatically existing finite nerve, evaluate the tetrahedral
star provider at precisely that selection, and construct the fully lowered
five-field boundary.  Classical choice is used explicitly so no elimination
from the `Nonempty` existence proof into data is hidden in tactic code. -/
noncomputable def
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.toFiniteNerveBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
      M := by
  let finiteNerveReduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M :=
    Classical.choice
      (SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3
        (M := M))
  let tetrahedralStarWitness :=
    data.tetrahedralStarProvider finiteNerveReduction
  let tetrahedralTransitionPresentation :
      FiniteTetrahedralPLTransitionPresentation3
        finiteNerveReduction.atlas finiteNerveReduction.transitions :=
    Classical.choose tetrahedralStarWitness
  let starwiseTangentCompatible :
      StarwiseTangentCompatible3 tetrahedralTransitionPresentation :=
    Classical.choose_spec tetrahedralStarWitness
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let odePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.genericInverseEndpointODEMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
          odePrimitive) :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    tetrahedralTransitionPresentation := tetrahedralTransitionPresentation
    starwiseTangentCompatible := starwiseTangentCompatible
    analytic := analytic
    genericInverseEndpointODEMovingPrimitiveInputs := odePrimitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The boundary with no user-supplied finite nerve reaches the sphere
conclusion through the verified fully geometric finite-nerve boundary. -/
theorem
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toFiniteNerveBoundary.sphereConclusion

/-- Universal existence of the strongest fully geometric boundary after
removing its automatic finite-nerve field. -/
def
    UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the no-finite-nerve boundary implies the
repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (provider :
      UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toFiniteNerveBoundary⟩

end Poincare
