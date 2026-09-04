import Poincare.Global.MetricEntryThirdJetProfileCompactness
import Poincare.Global.ClosedMetricThirdJetOrbitCompactness

/-!
# Metric-orbit compactness from componentwise Arzela--Ascoli data

Componentwise equicontinuity and pointwise compactness make the ambient
scalar third-jet profile closure compact.  If every profile limit is realized
by a closed smooth Riemannian metric, that compactness descends through the
profile embedding to the metric-orbit closure.

The realized-profile-limit premise is the genuine residual compactness and
regularity obligation.  Arzela--Ascoli compactness in the ambient profile
product does not show that a limiting profile remains smooth and positive.
-/

noncomputable section

open Bundle Filter Function Set Topology
open scoped Manifold ContDiff MeasureTheory Topology UniformConvergence

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M
local notation "S" => MetricEntryThirdJetSlot n M

/-- Componentwise Arzela--Ascoli hypotheses make the metric-orbit closure
compact once every ambient profile limit is realized by an actual metric.
The realized-profile-limit premise is the genuine residual compactness and
regularity obligation. -/
theorem isCompact_closedMetricThirdJetOrbitClosure_of_componentwise
    {I : Type v} (gt : I → G)
    (hequicontinuous : ∀ slot : S, Equicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)))
    (hpointwiseCompact : ∀ (slot : S) (z : E), ∃ Q : Set ℝ,
      IsCompact Q ∧
        ∀ t : I, metricEntryThirdJetProfile (gt t) slot z ∈ Q)
    (hLimitsRealized :
      closure
          (Set.range
            (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)) ⊆
        Set.range (metricEntryThirdJetProfile (n := n) (M := M))) :
    letI : TopologicalSpace G :=
      closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
    IsCompact (closure (Set.range gt)) := by
  apply isCompact_closedMetricThirdJetOrbitClosure_of_compact_profileClosure
    gt
  · exact
      isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise
        gt hequicontinuous hpointwiseCompact
  · exact hLimitsRealized

/-- Pointwise bounded scalar profile components provide the compact
pointwise sets in the preceding theorem.  Realization of every ambient
profile limit remains the genuine residual compactness and regularity
obligation. -/
theorem isCompact_closedMetricThirdJetOrbitClosure_of_componentwise_bounded
    {I : Type v} (gt : I → G)
    (hequicontinuous : ∀ slot : S, Equicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)))
    (hpointwiseBounded : ∀ (slot : S) (z : E),
      Bornology.IsBounded (Set.range
        (fun t : I ↦ metricEntryThirdJetProfile (gt t) slot z)))
    (hLimitsRealized :
      closure
          (Set.range
            (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)) ⊆
        Set.range (metricEntryThirdJetProfile (n := n) (M := M))) :
    letI : TopologicalSpace G :=
      closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
    IsCompact (closure (Set.range gt)) := by
  apply isCompact_closedMetricThirdJetOrbitClosure_of_compact_profileClosure
    gt
  · exact
      isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_bounded
        gt hequicontinuous hpointwiseBounded
  · exact hLimitsRealized

section DimensionThree

variable [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]

local notation "E3" => ClosedSmoothModel 3
local notation "G3" => ClosedSmoothRiemannianMetric 3 M
local notation "S3" => MetricEntryThirdJetSlot 3 M

/-- Componentwise Arzela--Ascoli data and realization of every profile limit
give a uniform full covariant-Ricci derivative bound in dimension three.
The realized-profile-limit premise remains the genuine residual compactness
and regularity obligation. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_componentwise
    {I : Type v} [Nonempty I] (gt : I → G3)
    (hequicontinuous : ∀ slot : S3, Equicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E3 → ℝ)))
    (hpointwiseCompact : ∀ (slot : S3) (z : E3), ∃ Q : Set ℝ,
      IsCompact Q ∧
        ∀ t : I, metricEntryThirdJetProfile (gt t) slot z ∈ Q)
    (hLimitsRealized :
      closure
          (Set.range
            (metricEntryThirdJetProfile (n := 3) (M := M) ∘ gt)) ⊆
        Set.range (metricEntryThirdJetProfile (n := 3) (M := M))) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D := by
  apply
    exists_uniformCovariantRicciDerivativeNormBound_of_compact_closedMetricThirdJetOrbitClosure
      gt
  exact isCompact_closedMetricThirdJetOrbitClosure_of_componentwise
    gt hequicontinuous hpointwiseCompact hLimitsRealized

/-- Componentwise equicontinuity, pointwise boundedness, and realization of
every profile limit give a uniform full covariant-Ricci derivative bound in
dimension three.  The realized-profile-limit premise remains the genuine
residual compactness and regularity obligation. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_componentwise_bounded
    {I : Type v} [Nonempty I] (gt : I → G3)
    (hequicontinuous : ∀ slot : S3, Equicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E3 → ℝ)))
    (hpointwiseBounded : ∀ (slot : S3) (z : E3),
      Bornology.IsBounded (Set.range
        (fun t : I ↦ metricEntryThirdJetProfile (gt t) slot z)))
    (hLimitsRealized :
      closure
          (Set.range
            (metricEntryThirdJetProfile (n := 3) (M := M) ∘ gt)) ⊆
        Set.range (metricEntryThirdJetProfile (n := 3) (M := M))) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D := by
  apply
    exists_uniformCovariantRicciDerivativeNormBound_of_compact_closedMetricThirdJetOrbitClosure
      gt
  exact isCompact_closedMetricThirdJetOrbitClosure_of_componentwise_bounded
    gt hequicontinuous hpointwiseBounded hLimitsRealized

end DimensionThree

end Poincare
