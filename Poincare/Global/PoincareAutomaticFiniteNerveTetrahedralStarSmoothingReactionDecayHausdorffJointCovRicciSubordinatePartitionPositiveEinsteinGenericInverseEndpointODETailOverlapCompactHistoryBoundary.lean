import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary

/-!
# Automatic finite-nerve Poincare boundary from the ODE overlap tail

This end boundary replaces the moving target-chart ODE primitive by the exact
four overlap residuals remaining after the selector's automatic positive
initial good interval.  Finite-nerve selection, tetrahedral-star smoothing,
subordinate-partition analysis, and compact-history feedback are unchanged.

The dependent feedback field is indexed directly by the old minimal moving
input applied to the tail-to-ODE conversion, making its copy into the
verified predecessor boundary definitional.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction
open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityFiniteTetrahedralStarReduction

/-- The strongest automatic finite-nerve boundary with only the exact
post-initial-time overlap tail retained at the moving endpoint. -/
structure
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointODEMovingTailOverlapInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
          genericInverseEndpointODEMovingTailOverlapInputs))

/-- Convert only the tail moving input and copy every other field into the
verified automatic finite-nerve ODE-primitive boundary. -/
noncomputable def
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.toODEPrimitiveBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.{u, v}
        M) :
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.{u, v}
      M := by
  let tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.tetrahedralStarProvider
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let tailOverlap :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3 M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.genericInverseEndpointODEMovingTailOverlapInputs
      M _ _ ambientChartedSpace _ _ data
  let odePrimitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
    fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
      tailOverlap
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
          odePrimitive) :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    tetrahedralStarProvider := tetrahedralStarProvider
    analytic := analytic
    genericInverseEndpointODEMovingPrimitiveInputs := odePrimitive
    compactHistoryFeedback := compactHistoryFeedback }

/-- The fully lowered scalar-derivative analytic boundary paired with only the
post-initial-time moving overlap tail. -/
structure
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M
  analytic :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
      M
  genericInverseEndpointODEMovingTailOverlapInputs :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
        (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
          genericInverseEndpointODEMovingTailOverlapInputs))

/-- Construct the scalar-derivative tail boundary directly from Bochner norm
fields while retaining the original tail input. -/
noncomputable def
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.ofBochnerNormFields
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M)
    (reaction :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          letI : MeasurableSpace M := borel M
          letI : BorelSpace M := ⟨rfl⟩
          NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M)
    (compactTensorReferenceControl :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          letI : MeasurableSpace M := borel M
          letI : BorelSpace M := ⟨rfl⟩
          let reactionData :
            NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M :=
            reaction
          letI : TopologicalSpace reactionData.K := reactionData.topologicalSpaceK
          CompactReferenceMetricTensorFamilyData reactionData.K reactionData.metric)
    (hRicNorm₂ :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          letI : MeasurableSpace M := borel M
          letI : BorelSpace M := ⟨rfl⟩
          let reactionData :
            NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M :=
            reaction
          ∀ k : reactionData.K, ∀ x : M,
            ContMDiffAt (closedSmoothModelWithCorners 3)
              (modelWithCornersSelf ℝ ℝ) 2
              (fun y : M ↦ (reactionData.metric k).ricciNormSqAt y) x)
    (hRicSecond :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          letI : MeasurableSpace M := borel M
          letI : BorelSpace M := ⟨rfl⟩
          let reactionData :
            NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M :=
            reaction
          ∀ k : reactionData.K, ∀ x : M,
            CovTensor2DerivExtDifferentiableAt (reactionData.metric k)
              (ricciVariationField (reactionData.metric k)) x)
    (hLaplacianJointContinuous :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          letI : MeasurableSpace M := borel M
          letI : BorelSpace M := ⟨rfl⟩
          let reactionData :
            NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M :=
            reaction
          letI : TopologicalSpace reactionData.K := reactionData.topologicalSpaceK
          Continuous (fun p : reactionData.K × M ↦
            (reactionData.metric p.1).laplacianAt
              (fun y : M ↦ (reactionData.metric p.1).ricciNormSqAt y) p.2))
    (hRoughJointContinuous :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          letI : MeasurableSpace M := borel M
          letI : BorelSpace M := ⟨rfl⟩
          let reactionData :
            NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M :=
            reaction
          letI : TopologicalSpace reactionData.K := reactionData.topologicalSpaceK
          Continuous (fun p : reactionData.K × M ↦
            roughRicciLaplacianPairingAt (reactionData.metric p.1) p.2))
    (scalarSubordinateGeometry :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          letI : MeasurableSpace M := borel M
          letI : BorelSpace M := ⟨rfl⟩
          let reactionData :
            NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M :=
            reaction
          (t : Ici (0 : ℝ)) →
            FiniteSubordinateHausdorffLaplacianGeometry
              (reactionData.gt t.1)
              (fun y ↦ (reactionData.gt t.1).scalarAt y))
    (genericInverseEndpointODEMovingTailOverlapInputs :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3
        M)
    (compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
          (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
            genericInverseEndpointODEMovingTailOverlapInputs))) :
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.{u, v}
      M := by
  let positiveTimeBoundary :=
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFieldsAndTailOverlap
      tetrahedralStarProvider reaction compactTensorReferenceControl hRicNorm₂ hRicSecond
      hLaplacianJointContinuous hRoughJointContinuous scalarSubordinateGeometry
      genericInverseEndpointODEMovingTailOverlapInputs compactHistoryFeedback
  exact {
    tetrahedralStarProvider := tetrahedralStarProvider
    analytic :=
      @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.analytic
        M _ _ ambientChartedSpace _ _ positiveTimeBoundary
    genericInverseEndpointODEMovingTailOverlapInputs :=
      genericInverseEndpointODEMovingTailOverlapInputs
    compactHistoryFeedback := compactHistoryFeedback }

/-- Convert the tail input to positive-time overlap while preserving the stronger
scalar-derivative analytic record and the compact-history index definitionally. -/
noncomputable def
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.toPositiveTimeOverlapBoundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.{u, v}
        M) :
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.{u, v}
      M := by
  let tetrahedralStarProvider : FiniteTetrahedralStarPresentationProvider3 M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.tetrahedralStarProvider
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v} M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let tailOverlap :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3 M :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.genericInverseEndpointODEMovingTailOverlapInputs
      M _ _ ambientChartedSpace _ _ data
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        (fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
          (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
            tailOverlap)) :=
    @AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  exact {
    tetrahedralStarProvider := tetrahedralStarProvider
    analytic := analytic
    genericInverseEndpointODEMovingPositiveTimeOverlapInputs :=
      fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3_of_tailInputs
        tailOverlap
    compactHistoryFeedback := compactHistoryFeedback }

/-- The fully lowered tail boundary reaches the sphere conclusion through the
verified scalar-derivative positive-time boundary. -/
theorem
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toPositiveTimeOverlapBoundary.sphereConclusion

/-- The tail-overlap boundary reaches the sphere conclusion through the
verified strongest automatic finite-nerve boundary. -/
theorem
    AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  data.toODEPrimitiveBoundary.sphereConclusion

def
    UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer of the exact tail-overlap boundary implies the
repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3
    (provider :
      UniversalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  apply
    poincareConjectureStatement_of_universalAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact ⟨data.toODEPrimitiveBoundary⟩

end Poincare
