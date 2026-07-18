import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary

/-!
# Automatic finite-nerve Poincare boundary from positive-time ODE overlap

This theorem-bearing end boundary lowers the moving Cartan field of the
strongest automatic finite-nerve boundary one step further.  Instead of an
already assembled target-chart ODE primitive, it stores ordinary chart and
cutoff membership only at strictly positive times on a cutoff-subordinated
fixed-chart package.

The automatic finite nerve, tetrahedral-star smoothing, subordinate
partition, joint-covariant-Ricci analytic data, and compact-history feedback
are unchanged.  The feedback field is indexed directly by the old minimal
moving input applied to the converted ODE-primitive input.  Consequently its
dependent type is definitionally identical when this record is converted to
the verified predecessor boundary.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction
open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityFiniteTetrahedralStarReduction

/-- The strongest automatic finite-nerve boundary with the moving endpoint
reduced to its honest strictly-positive-time path-retention residual. -/
structure
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointODEMovingPositiveTimeOverlapInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3
      M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_positiveTimeOverlapInputs
          genericInverseEndpointODEMovingPositiveTimeOverlapInputs))

/-- Convert only the positive-time moving input.  Every smoothing/analytic
field and the definitionally indexed compact-history feedback are copied to
the verified automatic finite-nerve ODE-primitive boundary. -/
noncomputable def
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.toODEPrimitiveBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.{u, v}
        M) :
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
      M := by
  let tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.tetrahedralStarProvider
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let positiveTimeOverlap :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3
        M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.genericInverseEndpointODEMovingPositiveTimeOverlapInputs
      M _ _ ambientChartedSpace _ _ data
  let odePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
    fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_positiveTimeOverlapInputs
      positiveTimeOverlap
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
          odePrimitive) :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    tetrahedralStarProvider := tetrahedralStarProvider
    analytic := analytic
    genericInverseEndpointODEMovingPrimitiveInputs := odePrimitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The positive-time boundary reaches the sphere conclusion through the
verified strongest automatic finite-nerve boundary. -/
theorem
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toODEPrimitiveBoundary.sphereConclusion

/-- Universal existence of the automatic finite-nerve positive-time overlap
boundary. -/
def
    UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer of the positive-time overlap boundary implies the
repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3
    (provider :
      UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toODEPrimitiveBoundary⟩

end Poincare
