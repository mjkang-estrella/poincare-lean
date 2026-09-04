import Poincare.Global.MetricEntryThirdJetFormalRicciBound
import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein

/-!
# Positive Einstein data from compact formal metric profiles

The established componentwise Arzela--Ascoli constructors required every
scalar third-jet profile limit to be realized by a smooth Riemannian metric.
The formal Ricci algebra removes that unnecessary regularity demand.  Compact
profile closure now supplies the full covariant-Ricci derivative bound as soon
as the forward metrics retain one uniform positive lower comparison with a
genuine reference metric.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

namespace NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3

/-- Componentwise equicontinuity and pointwise compact containment of the
forward scalar third-jet profiles construct the positive-Einstein analytic
package under a uniform lower metric comparison.  No profile-limit
realization hypothesis is used. -/
noncomputable def ofComponentwiseAscoliFormalMetricThirdJetProfiles
    (reaction :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
        M)
    (compactTensorReferenceControl :
      letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      CompactReferenceMetricTensorFamilyData reaction.K reaction.metric)
    (hequicontinuous : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Equicontinuous (fun t : Ici (0 : ℝ) =>
        (metricEntryThirdJetProfile (reaction.gt t.1) slot :
          ClosedSmoothModel 3 → ℝ)))
    (hpointwiseCompact :
      ∀ (slot : MetricEntryThirdJetSlot 3 M) (z : ClosedSmoothModel 3),
        ∃ Q : Set ℝ, IsCompact Q ∧
          ∀ t : Ici (0 : ℝ),
            metricEntryThirdJetProfile (reaction.gt t.1) slot z ∈ Q)
    (gref : ClosedSmoothRiemannianMetric 3 M) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref
      (fun t : Ici (0 : ℝ) => reaction.gt t.1) c)
    (scalarSubordinateGeometry : ∀ t : Ici (0 : ℝ),
      FiniteSubordinateHausdorffLaplacianGeometry
        (reaction.gt t.1) (fun y => (reaction.gt t.1).scalarAt y)) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
      M := by
  let atlas : FiniteFixedAnchorCutoffOneChartCover 3 M :=
    Classical.choice (exists_finiteFixedAnchorCutoffOneChartCover
      (n := 3) (M := M))
  apply ofJointScalarDerivativeSubordinatePartitionOfUniformCovRicciBound
    reaction compactTensorReferenceControl
  · exact
      exists_uniformCovariantRicciDerivativeNormBound_of_componentwise_and_closedMetricLower
        (fun t : Ici (0 : ℝ) => reaction.gt t.1) atlas
        hequicontinuous hpointwiseCompact gref c hLower
  · exact scalarSubordinateGeometry

/-- Pointwise bounded scalar profile components supply the compact pointwise
sets in the preceding no-realization constructor. -/
noncomputable def ofComponentwiseBoundedAscoliFormalMetricThirdJetProfiles
    (reaction :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
        M)
    (compactTensorReferenceControl :
      letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      CompactReferenceMetricTensorFamilyData reaction.K reaction.metric)
    (hequicontinuous : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Equicontinuous (fun t : Ici (0 : ℝ) =>
        (metricEntryThirdJetProfile (reaction.gt t.1) slot :
          ClosedSmoothModel 3 → ℝ)))
    (hpointwiseBounded :
      ∀ (slot : MetricEntryThirdJetSlot 3 M) (z : ClosedSmoothModel 3),
        Bornology.IsBounded (Set.range
          (fun t : Ici (0 : ℝ) =>
            metricEntryThirdJetProfile (reaction.gt t.1) slot z)))
    (gref : ClosedSmoothRiemannianMetric 3 M) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref
      (fun t : Ici (0 : ℝ) => reaction.gt t.1) c)
    (scalarSubordinateGeometry : ∀ t : Ici (0 : ℝ),
      FiniteSubordinateHausdorffLaplacianGeometry
        (reaction.gt t.1) (fun y => (reaction.gt t.1).scalarAt y)) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
      M := by
  let atlas : FiniteFixedAnchorCutoffOneChartCover 3 M :=
    Classical.choice (exists_finiteFixedAnchorCutoffOneChartCover
      (n := 3) (M := M))
  apply ofJointScalarDerivativeSubordinatePartitionOfUniformCovRicciBound
    reaction compactTensorReferenceControl
  · exact
      exists_uniformCovariantRicciDerivativeNormBound_of_componentwise_bounded_and_closedMetricLower
        (fun t : Ici (0 : ℝ) => reaction.gt t.1) atlas
        hequicontinuous hpointwiseBounded gref c hLower
  · exact scalarSubordinateGeometry

end NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3
end Poincare
