import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundary

/-!
# Automatic finite-nerve boundary from intrinsic scalar `C¹` control

This is the strongest current producer boundary with all four independent
lowerings present at once:

* compactness automatically selects the finite precompact atlas nerve;
* a tangent-compatible tetrahedral-star presentation constructs the required
  PL-compatible affine conjugacy;
* joint continuity of the actual scalar time derivative, together with joint
  `C³` metric entries, constructs the local chartwise scalar-density
  domination package;
* finite subordinate partitions construct scalar Laplacian Stokes, while
  target-chart ODE comparison constructs the moving endpoint identity.

The conversion below deliberately targets the established reaction-decay
pointwise compact-history boundary.  Its analytic field is obtained from the
intrinsic scalar-derivative endpoint, and its pointwise moving inputs are
obtained from the ODE primitives.  The compact-history feedback is then typed
against those exact converted inputs, rather than against an unrelated
provider.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityFiniteTetrahedralStarReduction

/-- The strongest fully lowered automatic-finite-nerve boundary.  Its
analytic producer contains neither a scalar-density domination record nor a
Stokes conclusion. -/
structure
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointODEMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        genericInverseEndpointODEMovingPrimitiveInputs)

/-- Select the automatic finite nerve, construct its affine conjugacy from
the tetrahedral-star presentation, lower the intrinsic analytic package, and
convert the ODE provider to the pointwise moving input expected by the
verified compact-history boundary. -/
noncomputable def
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.toReactionDecayPointwiseBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    FiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3.{u, v}
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
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let reactionDecayAnalytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M :=
    fixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3_of_jointScalarDerivativeCovRicciSubordinatePartition
      analytic
  let odePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.genericInverseEndpointODEMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let genericInversePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M :=
    fixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3_of_odePrimitiveInputs
      odePrimitive
  let pointwisePrimitive :
      FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M :=
    fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_genericInverseEndpointPrimitiveInputs
      genericInversePrimitive
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
          pointwisePrimitive) :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    finiteNerveReduction := finiteNerveReduction
    plCompatibleAffineConjugacy :=
      finiteNervePLCompatibleAffineConjugacy3_of_tetrahedralStar
        finiteNerveReduction tetrahedralTransitionPresentation
        starwiseTangentCompatible
    analytic := reactionDecayAnalytic
    pointwiseMovingPrimitiveInputs := pointwisePrimitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The fully lowered automatic-finite-nerve boundary reaches the sphere
conclusion through the verified reaction-decay pointwise boundary. -/
theorem
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toReactionDecayPointwiseBoundary.sphereConclusion

/-- Universal existence of the fully lowered automatic-finite-nerve
boundary. -/
def
    UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for the fully lowered boundary implies the
repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
    (provider :
      UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toReactionDecayPointwiseBoundary⟩

end Poincare
