import Poincare.Global.CartanGenericSuccessorDataMovingPersistenceReduction

/-!
# Subordinating fixed-chart transition packages

A fixed-chart anchor-endpoint package already contains an open coordinate
slice about its center.  The moving-source reduction previously asked for a
new package subordinate to every prescribed neighborhood of that center.
This module proves that the extra quantifier is unnecessary.

Given an open manifold set `V` containing the center, restrict the coordinate
anchor slice to

`C.coordinateAnchors ∩ (chart.target ∩ chart.symm ⁻¹' V)`.

This set is open in the model space.  The selector, selected time, derivative,
endpoint partial homeomorphism, endpoint formula, inverse normal, transported
normal, and fixed-time endpoint are unchanged.  Only the anchor and joint
endpoint loci shrink.  Consequently joint continuity restricts by
`ContinuousOn.mono`, and all three positive-time endpoint-agreement fields
restrict using the old-anchor inclusion.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000
set_option linter.unusedSectionVars false

open Filter Function Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanFixedChartTransitionAgreementSubordination

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanSourceExponentialLocalFamilyTransport
open CartanGenericSuccessorDataMovingPersistenceReduction

end CartanFixedChartTransitionAgreementSubordination

namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

/-- The open coordinate-anchor slice obtained by retaining only anchors whose
inverse chart values lie in `V`.  Intersecting with the chart target is what
makes the inverse-chart preimage an ambient open model-space set. -/
def restrictedCoordinateAnchors
    (C : FixedChartAnchorEndpointPackage g x₀) (V : Set M) : Set E :=
  C.coordinateAnchors ∩
    ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' V)

/-- Restrict a fixed-chart package to an open manifold neighborhood of its
center, without changing any computational endpoint data. -/
def restrictToOpenAnchorSet
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    FixedChartAnchorEndpointPackage g x₀ where
  selector := C.selector
  time := C.time
  time_pos := C.time_pos
  derivative := C.derivative
  endpoint := C.endpoint
  time_protected := C.time_protected
  endpoint_hasStrictFDerivAt := C.endpoint_hasStrictFDerivAt
  endpoint_apply := C.endpoint_apply
  coordinateAnchors := C.restrictedCoordinateAnchors V
  isOpen_coordinateAnchors :=
    C.isOpen_coordinateAnchors.inter
      ((continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
        (isOpen_extChartAt_target x₀) hV)
  center_mem_coordinateAnchors := by
    refine ⟨C.center_mem_coordinateAnchors, ?_⟩
    have hxSource : x₀ ∈ (extChartAt I x₀).source :=
      mem_extChartAt_source x₀
    refine ⟨(extChartAt I x₀).map_source hxSource, ?_⟩
    change (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈ V
    simpa only [(extChartAt I x₀).left_inv hxSource] using hx₀V
  zero_mem_source := by
    intro z hz
    exact C.zero_mem_source z hz.1
  zero_stationary := by
    intro z hz
    exact C.zero_stationary z hz.1

@[simp]
theorem restrictToOpenAnchorSet_endpoint
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).endpoint = C.endpoint :=
  rfl

@[simp]
theorem restrictToOpenAnchorSet_selector
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).selector = C.selector :=
  rfl

@[simp]
theorem restrictToOpenAnchorSet_time
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).time = C.time :=
  rfl

/-- Every anchor retained by the restriction was already an anchor of the
original raw local family. -/
theorem restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).rawLocalFamily.anchors ⊆
      C.rawLocalFamily.anchors := by
  intro x hx
  change x ∈ anchorSet x₀ (C.restrictedCoordinateAnchors V) at hx
  change x ∈ anchorSet x₀ C.coordinateAnchors
  exact ⟨hx.1, hx.2.1⟩

/-- Every retained anchor lies in the requested open manifold set. -/
theorem restrictToOpenAnchorSet_rawLocalFamily_anchors_subset
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).rawLocalFamily.anchors ⊆ V := by
  intro x hx
  change x ∈ anchorSet x₀ (C.restrictedCoordinateAnchors V) at hx
  have hxV :
      (extChartAt I x₀).symm (extChartAt I x₀ x) ∈ V :=
    hx.2.2.2
  rwa [(extChartAt I x₀).left_inv hx.1] at hxV

/-- The restricted anchor locus is exactly the original locus intersected
with the requested open set. -/
theorem restrictToOpenAnchorSet_rawLocalFamily_anchors_eq
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).rawLocalFamily.anchors =
      C.rawLocalFamily.anchors ∩ V := by
  apply Set.Subset.antisymm
  · intro x hx
    exact
      ⟨C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
          V hV hx₀V hx,
        C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset
          V hV hx₀V hx⟩
  · intro x hx
    change x ∈ anchorSet x₀ (C.restrictedCoordinateAnchors V)
    have hxOld := hx.1
    change x ∈ anchorSet x₀ C.coordinateAnchors at hxOld
    have hxTarget : extChartAt I x₀ x ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hxOld.1
    refine ⟨hxOld.1, hxOld.2, hxTarget, ?_⟩
    change (extChartAt I x₀).symm (extChartAt I x₀ x) ∈ V
    simpa only [(extChartAt I x₀).left_inv hxOld.1] using hx.2

/-- Restriction only shrinks the joint endpoint locus. -/
theorem restrictToOpenAnchorSet_rawLocalFamily_sourceLocus_subset_original
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).rawLocalFamily.sourceLocus ⊆
      C.rawLocalFamily.sourceLocus := by
  intro q hq
  change q ∈ endpointLocus x₀ C.endpoint
    (C.restrictedCoordinateAnchors V) at hq
  change q ∈ endpointLocus x₀ C.endpoint C.coordinateAnchors
  exact
    ⟨C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
        V hV hx₀V hq.1,
      hq.2⟩

/-- Restricting the anchor slice preserves the raw inverse-normal formula
pointwise on the entire ambient product. -/
@[simp]
theorem restrictToOpenAnchorSet_rawLocalFamily_normal
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
    (q : M × M) :
    (C.restrictToOpenAnchorSet V hV hx₀V).rawLocalFamily.normal q =
      C.rawLocalFamily.normal q :=
  rfl

/-- The transported inverse-normal formula is likewise unchanged. -/
@[simp]
theorem restrictToOpenAnchorSet_transportedNormal
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
    (q : M × M) :
    (C.restrictToOpenAnchorSet V hV hx₀V).transportedNormal q =
      C.transportedNormal q :=
  rfl

/-- The selected positive-time endpoint formula is unchanged. -/
@[simp]
theorem restrictToOpenAnchorSet_fixedTimeEndpoint
    (C : FixedChartAnchorEndpointPackage g x₀)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
    (x : M) (w : E) :
    (C.restrictToOpenAnchorSet V hV hx₀V).fixedTimeEndpoint x w =
      C.fixedTimeEndpoint x w :=
  rfl

/-- A transition-agreement package restricts to the smaller coordinate-anchor
slice with the same radius and exactly the same endpoint formulas. -/
def TransitionAgreementPackage.restrictToOpenAnchorSet
    {C : FixedChartAnchorEndpointPackage g x₀}
    (P : C.TransitionAgreementPackage)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).TransitionAgreementPackage where
  radius := P.radius
  radius_pos := P.radius_pos
  jointContinuity := by
    have hmono := P.jointContinuity.mono
      (C.restrictToOpenAnchorSet_rawLocalFamily_sourceLocus_subset_original
        V hV hx₀V)
    simpa only [restrictToOpenAnchorSet_transportedNormal] using hmono
  fixedTimeEndpoint := by
    refine {
      point_mem_anchorChart := ?_
      vector_mem_genericExpSource := ?_
      endpoint_coordinate := ?_ }
    · intro x w hxAnchor hwSource hnorm
      have hxOld :=
        C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
          V hV hx₀V hxAnchor
      simpa only [restrictToOpenAnchorSet_endpoint,
        restrictToOpenAnchorSet_fixedTimeEndpoint] using
          P.fixedTimeEndpoint.point_mem_anchorChart
            x w hxOld hwSource hnorm
    · intro x w hxAnchor hwSource hnorm
      have hxOld :=
        C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
          V hV hx₀V hxAnchor
      exact
        P.fixedTimeEndpoint.vector_mem_genericExpSource
          x w hxOld (by simpa only [restrictToOpenAnchorSet_endpoint] using hwSource)
            hnorm
    · intro x w hxAnchor hwSource hnorm
      have hxOld :=
        C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
          V hV hx₀V hxAnchor
      simpa only [restrictToOpenAnchorSet_fixedTimeEndpoint] using
        P.fixedTimeEndpoint.endpoint_coordinate
          x w hxOld (by simpa only [restrictToOpenAnchorSet_endpoint] using hwSource)
            hnorm

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport

/-! ## Eliminating the subordination quantifier -/

namespace CartanFixedChartTransitionAgreementSubordination

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanSourceExponentialLocalFamilyTransport
open CartanGenericSuccessorDataMovingPersistenceReduction

/-- Pointwise existence of one proof-bearing fixed-chart transition package
at every center. -/
def PointwiseFixedChartTransitionAgreementPackage
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      Nonempty C.TransitionAgreementPackage

/-- Pointwise transition-package existence implies the formerly stronger
subordination contract: restrict the chosen coordinate slice inside an open
set contained in the prescribed neighborhood. -/
theorem subordinateFixedChartTransitionAgreement_of_pointwisePackage
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hpointwise : PointwiseFixedChartTransitionAgreementPackage g) :
    SubordinateFixedChartTransitionAgreement g := by
  intro x₀ U hU
  rcases hpointwise x₀ with ⟨C, ⟨P⟩⟩
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hx₀V⟩
  let C' := C.restrictToOpenAnchorSet V hVopen hx₀V
  let P' : C'.TransitionAgreementPackage :=
    P.restrictToOpenAnchorSet V hVopen hx₀V
  refine ⟨C', P', ?_⟩
  intro x hx
  apply hVU
  exact C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset
    V hVopen hx₀V hx

end CartanFixedChartTransitionAgreementSubordination
end Poincare
