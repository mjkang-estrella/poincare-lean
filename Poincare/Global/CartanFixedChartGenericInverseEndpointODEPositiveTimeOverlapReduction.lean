import Poincare.Global.CartanFixedChartGenericInverseEndpointODEOverlapReduction

/-!
# Positive-time overlap data for the generic-inverse ODE comparison

The pointwise overlap reduction still records its four membership conditions
at time zero.  Three of those conditions already follow from the selector's
initial value and ordinary chart inverse laws.  The fourth follows after the
standard harmless subordination of the anchor slice to the fixed chart's
cutoff-one neighborhood.

This file carries out that subordination and lowers the provider boundary to
membership on `Ioc 0 C.time`.  Thus none of the four time-zero overlap facts
is retained as an input.
-/

noncomputable section

set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

open CartanSourceExponential
open CartanGenericSuccessorDataMovingPersistenceReduction

/-! ## Subordination to the fixed cutoff-one neighborhood -/

/-- The manifold points whose fixed-chart coordinates lie in the fixed
anchor's cutoff-one locus, restricted to the honest chart source. -/
def fixedAnchorCutoffOneNeighborhood (x₀ : M) : Set M :=
  (extChartAt I x₀).source ∩
    (extChartAt I x₀) ⁻¹' IsometryInstantiate.cutoffOneLocus x₀

/-- The fixed cutoff-one anchor neighborhood is open. -/
theorem isOpen_fixedAnchorCutoffOneNeighborhood (x₀ : M) :
    IsOpen (fixedAnchorCutoffOneNeighborhood x₀) := by
  exact (continuousOn_extChartAt x₀).isOpen_inter_preimage
    (isOpen_extChartAt_source x₀)
    (IsometryInstantiate.isOpen_cutoffOneLocus x₀)

/-- The fixed anchor itself lies in the fixed cutoff-one neighborhood. -/
theorem center_mem_fixedAnchorCutoffOneNeighborhood (x₀ : M) :
    x₀ ∈ fixedAnchorCutoffOneNeighborhood x₀ := by
  refine ⟨mem_extChartAt_source x₀, ?_⟩
  change extChartAt I x₀ x₀ ∈
    IsometryInstantiate.cutoffOneLocus x₀
  exact mem_of_mem_nhds
    (IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x₀)

/-- Restrict only the open anchor slice so every retained anchor starts in
the fixed-anchor cutoff-one locus.  All selector and endpoint data are
definitionally unchanged. -/
def restrictToFixedAnchorCutoffOne
    (C : FixedChartAnchorEndpointPackage g x₀) :
    FixedChartAnchorEndpointPackage g x₀ :=
  C.restrictToOpenAnchorSet
    (fixedAnchorCutoffOneNeighborhood x₀)
    (isOpen_fixedAnchorCutoffOneNeighborhood x₀)
    (center_mem_fixedAnchorCutoffOneNeighborhood x₀)

@[simp]
theorem restrictToFixedAnchorCutoffOne_selector
    (C : FixedChartAnchorEndpointPackage g x₀) :
    C.restrictToFixedAnchorCutoffOne.selector = C.selector :=
  rfl

@[simp]
theorem restrictToFixedAnchorCutoffOne_time
    (C : FixedChartAnchorEndpointPackage g x₀) :
    C.restrictToFixedAnchorCutoffOne.time = C.time :=
  rfl

@[simp]
theorem restrictToFixedAnchorCutoffOne_endpoint
    (C : FixedChartAnchorEndpointPackage g x₀) :
    C.restrictToFixedAnchorCutoffOne.endpoint = C.endpoint :=
  rfl

/-- Every retained anchor has fixed-chart coordinate in the fixed cutoff-one
locus. -/
theorem restrictToFixedAnchorCutoffOne_anchor_mem_cutoffOneLocus
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors) :
    extChartAt I x₀ x ∈ IsometryInstantiate.cutoffOneLocus x₀ := by
  have hxV := C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset
    (fixedAnchorCutoffOneNeighborhood x₀)
    (isOpen_fixedAnchorCutoffOneNeighborhood x₀)
    (center_mem_fixedAnchorCutoffOneNeighborhood x₀) hx
  exact hxV.2

/-- Fixed-cutoff subordination only shrinks the original anchor slice. -/
theorem restrictToFixedAnchorCutoffOne_rawLocalFamily_anchors_subset_original
    (C : FixedChartAnchorEndpointPackage g x₀) :
    C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors ⊆
      C.rawLocalFamily.anchors :=
  C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
    (fixedAnchorCutoffOneNeighborhood x₀)
    (isOpen_fixedAnchorCutoffOneNeighborhood x₀)
    (center_mem_fixedAnchorCutoffOneNeighborhood x₀)

/-! ## Strictly positive-time data -/

/-- Primitive domain admissibility together with the four honest overlap
memberships only at strictly positive comparison times. -/
structure GenericInverseEndpointODEPositiveTimeOverlapData
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E)
    (P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x) : Prop where
  selectorInitial_mem :
    (extChartAt I x₀ x, C.time⁻¹ • w) ∈
      closedBall (extChartAt I x₀ x₀, (0 : E))
        (C.selector.projectFirstVariational.initialRadius : ℝ)
  preferredTime_le : C.time ≤ P.time
  preferredVelocity_small :
    ‖C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)‖ <
      P.velocityRadius
  sourceChart_mem : ∀ t ∈ Ioc (0 : ℝ) C.time,
    (C.normalizedSelectorTrajectory x w t).1 ∈
      (extChartAt I x₀).target
  targetChart_mem : ∀ t ∈ Ioc (0 : ℝ) C.time,
    (extChartAt I x₀).symm (C.normalizedSelectorTrajectory x w t).1 ∈
      (extChartAt I x).source
  sourceCutoffOne_mem : ∀ t ∈ Ioc (0 : ℝ) C.time,
    (C.normalizedSelectorTrajectory x w t).1 ∈
      IsometryInstantiate.cutoffOneLocus x₀
  targetCutoffOne_mem : ∀ t ∈ Ioc (0 : ℝ) C.time,
    GeodesicTransport.chartTransition x₀ x
        (C.normalizedSelectorTrajectory x w t).1 ∈
      IsometryInstantiate.cutoffOneLocus x

namespace GenericInverseEndpointODEPositiveTimeOverlapData

/-- The source selector starts at the normalized requested fixed-chart
state, without first constructing an ODE primitive. -/
theorem selectorInitial
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPositiveTimeOverlapData x w P) :
    C.normalizedSelectorTrajectory x w 0 =
      (extChartAt I x₀ x, C.time⁻¹ • w) := by
  simpa [normalizedSelectorTrajectory] using
    (C.selector.projectFirstVariational.selector_data
      (extChartAt I x₀ x, C.time⁻¹ • w)
      data.selectorInitial_mem).1

/-- After fixed-cutoff subordination, all four missing time-zero facts are
automatic.  Hence strictly-positive-time membership upgrades to the full
pointwise overlap package. -/
def toPointwiseOverlapData
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEPositiveTimeOverlapData
      C.restrictToFixedAnchorCutoffOne x w P) :
    GenericInverseEndpointODEPointwiseOverlapData
      C.restrictToFixedAnchorCutoffOne x w P where
  selectorInitial_mem := data.selectorInitial_mem
  preferredTime_le := data.preferredTime_le
  preferredVelocity_small := data.preferredVelocity_small
  sourceChart_mem := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · subst t
      rw [data.selectorInitial]
      exact (extChartAt I x₀).map_source hx.1
    · exact data.sourceChart_mem t ⟨hpos, ht.2⟩
  targetChart_mem := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · subst t
      rw [data.selectorInitial, (extChartAt I x₀).left_inv hx.1]
      exact mem_extChartAt_source x
    · exact data.targetChart_mem t ⟨hpos, ht.2⟩
  sourceCutoffOne_mem := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · subst t
      rw [data.selectorInitial]
      exact C.restrictToFixedAnchorCutoffOne_anchor_mem_cutoffOneLocus hx
    · exact data.sourceCutoffOne_mem t ⟨hpos, ht.2⟩
  targetCutoffOne_mem := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · subst t
      have hanchor : extChartAt I x x ∈
          IsometryInstantiate.cutoffOneLocus x :=
        mem_of_mem_nhds
          (IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x)
      rw [data.selectorInitial]
      change extChartAt I x
          ((extChartAt I x₀).symm (extChartAt I x₀ x)) ∈
        IsometryInstantiate.cutoffOneLocus x
      rw [(extChartAt I x₀).left_inv hx.1]
      exact hanchor
    · exact data.targetCutoffOne_mem t ⟨hpos, ht.2⟩

end GenericInverseEndpointODEPositiveTimeOverlapData

/-! ## Provider reduction -/

def GenericInverseEndpointODEPositiveTimeOverlapProvider
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E),
    x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors →
    (extChartAt I x₀ x, w) ∈
      C.restrictToFixedAnchorCutoffOne.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
        Nonempty
          (GenericInverseEndpointODEPositiveTimeOverlapData
            C.restrictToFixedAnchorCutoffOne x w P)

theorem genericInverseEndpointODEPointwiseOverlapProvider_of_positiveTime
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hpositive : C.GenericInverseEndpointODEPositiveTimeOverlapProvider) :
    GenericInverseEndpointODEPointwiseOverlapProvider
      C.restrictToFixedAnchorCutoffOne := by
  intro x w hx hw htarget
  rcases hpositive x w hx hw htarget with ⟨P, ⟨data⟩⟩
  exact ⟨P, ⟨data.toPointwiseOverlapData hx⟩⟩

/-- Strictly-positive-time overlap data construct the actual-public-flow ODE
primitive provider on the subordinated package. -/
theorem genericInverseEndpointODEPrimitiveProvider_of_positiveTimeOverlap
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hpositive : C.GenericInverseEndpointODEPositiveTimeOverlapProvider) :
    GenericInverseEndpointODEPrimitiveProvider
      C.restrictToFixedAnchorCutoffOne :=
  genericInverseEndpointODEPrimitiveProvider_of_pointwiseOverlap
      C.restrictToFixedAnchorCutoffOne
      (C.genericInverseEndpointODEPointwiseOverlapProvider_of_positiveTime
        hpositive)

/-- Consequently the positive-time provider fills the existing target-chart
ODE comparison provider without assuming an endpoint equality. -/
theorem genericInverseEndpointODEComparisonProvider_of_positiveTimeOverlap
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hpositive : C.GenericInverseEndpointODEPositiveTimeOverlapProvider) :
    GenericInverseEndpointODEComparisonProvider
      C.restrictToFixedAnchorCutoffOne :=
  genericInverseEndpointODEComparisonProvider_of_primitive
      C.restrictToFixedAnchorCutoffOne
      (C.genericInverseEndpointODEPrimitiveProvider_of_positiveTimeOverlap
        hpositive)

theorem genericInverseEndpointAgreement_of_positiveTimeOverlap
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hpositive : C.GenericInverseEndpointODEPositiveTimeOverlapProvider) :
    C.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreement :=
  genericInverseEndpointAgreement_of_pointwiseOverlap
      C.restrictToFixedAnchorCutoffOne
      (C.genericInverseEndpointODEPointwiseOverlapProvider_of_positiveTime
        hpositive)

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport
end Poincare
