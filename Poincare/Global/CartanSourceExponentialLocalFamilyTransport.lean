import Poincare.Global.CartanSourceExponentialLocalChartInverse

/-!
# Transporting a product inverse-function chart to a local source family

The fixed-chart geodesic construction naturally produces one product partial
homeomorphism

`(anchor coordinate, velocity) |-> (anchor coordinate, endpoint coordinate)`.

This file turns any such chart with a stationary zero-velocity slice into the
`CartanSourceExponential.LocalFamily` consumed by the Cartan continuation
assembly.  The inverse second projection is jointly continuous by construction.

A second constructor postcomposes that raw inverse velocity by a jointly
continuous anchor-dependent coordinate transport.  This is the exact place
where the concrete geodesic application inserts `chartTransitionDeriv x0 x`
to convert the fixed-chart velocity into the varying-anchor coordinates used
by the generic exponential.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanSourceExponentialLocalFamilyTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- Fixed-chart coordinates of an anchor/endpoint pair. -/
def coordinatePair (x₀ : M) (q : M × M) : E × E :=
  ((extChartAt I x₀) q.1, (extChartAt I x₀) q.2)

/-- The manifold anchors whose fixed-chart coordinates lie in `U`. -/
def anchorSet (x₀ : M) (U : Set E) : Set M :=
  (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' U

/-- The joint endpoint locus of a product anchor/endpoint partial
homeomorphism, restricted to the selected open anchor set. -/
def endpointLocus (x₀ : M)
    (P : OpenPartialHomeomorph (E × E) (E × E)) (U : Set E) :
    Set (M × M) :=
  Prod.fst ⁻¹' anchorSet x₀ U ∩
    (((extChartAt I x₀).source ×ˢ (extChartAt I x₀).source) ∩
      coordinatePair x₀ ⁻¹' P.target)

theorem isOpen_anchorSet (x₀ : M) {U : Set E} (hU : IsOpen U) :
    IsOpen (anchorSet x₀ U) := by
  exact isOpen_extChartAt_preimage' x₀ hU

theorem coordinatePair_continuousOn (x₀ : M) :
    ContinuousOn (coordinatePair x₀)
      ((extChartAt I x₀).source ×ˢ (extChartAt I x₀).source) := by
  have hfst : ContinuousOn (fun q : M × M => (extChartAt I x₀) q.1)
      ((extChartAt I x₀).source ×ˢ (extChartAt I x₀).source) :=
    (continuousOn_extChartAt x₀).comp continuous_fst.continuousOn
      (fun _q hq => hq.1)
  have hsnd : ContinuousOn (fun q : M × M => (extChartAt I x₀) q.2)
      ((extChartAt I x₀).source ×ˢ (extChartAt I x₀).source) :=
    (continuousOn_extChartAt x₀).comp continuous_snd.continuousOn
      (fun _q hq => hq.2)
  exact hfst.prodMk hsnd

theorem isOpen_endpointLocus (x₀ : M)
    (P : OpenPartialHomeomorph (E × E) (E × E))
    {U : Set E} (hU : IsOpen U) :
    IsOpen (endpointLocus x₀ P U) := by
  have hdomain : IsOpen
      ((extChartAt I x₀).source ×ˢ (extChartAt I x₀).source) :=
    (isOpen_extChartAt_source x₀).prod (isOpen_extChartAt_source x₀)
  have htarget : IsOpen
      (((extChartAt I x₀).source ×ˢ (extChartAt I x₀).source) ∩
        coordinatePair x₀ ⁻¹' P.target) :=
    (coordinatePair_continuousOn x₀).isOpen_inter_preimage
      hdomain P.open_target
  exact ((isOpen_anchorSet x₀ hU).preimage continuous_fst).inter htarget

/-- A product inverse-function chart with a stationary zero-velocity slice
gives a chart-local jointly continuous source normal family. -/
def localFamilyOfAnchorEndpoint
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (P : OpenPartialHomeomorph (E × E) (E × E))
    (U : Set E) (hU : IsOpen U)
    (hzeroSource : ∀ z ∈ U, (z, (0 : E)) ∈ P.source)
    (hstationary : ∀ z ∈ U, P (z, (0 : E)) = (z, z)) :
    CartanSourceExponential.LocalFamily g where
  anchors := anchorSet x₀ U
  isOpen_anchors := isOpen_anchorSet x₀ hU
  sourceLocus := endpointLocus x₀ P U
  isOpen_sourceLocus := isOpen_endpointLocus x₀ P hU
  sourceLocus_fst q hq := hq.1
  normal q := (P.symm (coordinatePair x₀ q)).2
  continuousOn_normal := by
    have hcoord : ContinuousOn (coordinatePair x₀)
        (endpointLocus x₀ P U) :=
      (coordinatePair_continuousOn x₀).mono (fun _q hq => hq.2.1)
    have hsymm : ContinuousOn
        (fun q : M × M => P.symm (coordinatePair x₀ q))
        (endpointLocus x₀ P U) :=
      P.continuousOn_symm.comp hcoord (fun _q hq => hq.2.2)
    exact hsymm.snd
  diagonal_mem x hx := by
    have hxSource : x ∈ (extChartAt I x₀).source := hx.1
    have hxZero : ((extChartAt I x₀) x, (0 : E)) ∈ P.source :=
      hzeroSource ((extChartAt I x₀) x) hx.2
    have hxTarget :
        ((extChartAt I x₀) x, (extChartAt I x₀) x) ∈ P.target := by
      rw [← hstationary ((extChartAt I x₀) x) hx.2]
      exact P.map_source hxZero
    exact ⟨hx, ⟨⟨hxSource, hxSource⟩, hxTarget⟩⟩
  normal_diagonal x hx := by
    have hxZero : ((extChartAt I x₀) x, (0 : E)) ∈ P.source :=
      hzeroSource ((extChartAt I x₀) x) hx.2
    have hstat := hstationary ((extChartAt I x₀) x) hx.2
    change (P.symm ((extChartAt I x₀) x, (extChartAt I x₀) x)).2 = 0
    rw [← hstat, P.left_inv hxZero]

/-- The fixed-chart inverse-function output together with one open anchor
slice on which zero velocity is in the product source and is stationary. -/
structure FixedChartAnchorEndpointPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) where
  selector : LocalRegularControlledContinuousAutonomousSelector
    (firstVariationalAugmentedField
      (CartanSourceExponentialLocalChartSelector.fixedChartGeodesicField g x₀))
    ((extChartAt I x₀ x₀, (0 : E)),
      ContinuousLinearMap.id ℝ (E × E))
  time : ℝ
  time_pos : 0 < time
  derivative : (E × E) →L[ℝ] E
  endpoint : OpenPartialHomeomorph (E × E) (E × E)
  time_protected : time ∈
    Ioo (-(selector.epsilon / 2)) (selector.epsilon / 2)
  endpoint_hasStrictFDerivAt : HasStrictFDerivAt
    (CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
      g x₀ selector time)
    derivative (extChartAt I x₀ x₀, (0 : E))
  endpoint_apply : (endpoint : (E × E) → (E × E)) =
    (fun q : E × E =>
      (q.1,
        CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
          g x₀ selector time q))
  coordinateAnchors : Set E
  isOpen_coordinateAnchors : IsOpen coordinateAnchors
  center_mem_coordinateAnchors : extChartAt I x₀ x₀ ∈ coordinateAnchors
  zero_mem_source : ∀ z ∈ coordinateAnchors,
    (z, (0 : E)) ∈ endpoint.source
  zero_stationary : ∀ z ∈ coordinateAnchors,
    endpoint (z, (0 : E)) = (z, z)

namespace FixedChartAnchorEndpointPackage

/-- The raw manifold local family obtained before transporting the fixed-chart
inverse velocity to each varying anchor chart. -/
def rawLocalFamily
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀) :
    CartanSourceExponential.LocalFamily g :=
  localFamilyOfAnchorEndpoint g x₀ C.endpoint C.coordinateAnchors
    C.isOpen_coordinateAnchors C.zero_mem_source C.zero_stationary

/-- The center anchor belongs to the raw local family. -/
theorem center_mem_rawLocalFamily_anchors
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀) :
    x₀ ∈ C.rawLocalFamily.anchors := by
  exact ⟨mem_extChartAt_source x₀, C.center_mem_coordinateAnchors⟩

end FixedChartAnchorEndpointPackage

/-- Every prescribed neighborhood of the central fixed-chart state admits a
product inverse-function package whose selector remains protected inside that
neighborhood. -/
theorem exists_fixedChartAnchorEndpointPackage_with_projected_protectedInnerBall_subset
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {U : Set (E × E)}
    (hU : U ∈ nhds (extChartAt I x₀ x₀, (0 : E))) :
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius ⊆ U := by
  rcases
      CartanSourceExponentialLocalChartSelector.exists_fixedChart_anchorEndpointOpenPartialHomeomorph_with_projected_protectedInnerBall_subset
        g x₀ hU with
    ⟨H, hprotected, T, hT, D, P, hTprotected, hjoint, hPapply,
      hcenterSource, _hcenterTarget⟩
  have hTfull : T ∈ Icc (-H.epsilon) H.epsilon := by
    constructor <;> linarith [hTprotected.1, hTprotected.2, H.epsilon_pos]
  have hanchor :=
    CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint_anchor_eventuallyEq_id
      g x₀ H hTfull
  have hstationary : ∀ᶠ z in nhds (extChartAt I x₀ x₀),
      P (z, (0 : E)) = (z, z) := by
    filter_upwards [hanchor] with z hz
    calc
      P (z, (0 : E)) =
          (z,
            CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
              g x₀ H T (z, (0 : E))) := congrFun hPapply (z, (0 : E))
      _ = (z, z) := by simpa only [id_eq] using congrArg (fun w => (z, w)) hz
  have hopenSourceSlice : IsOpen {z : E | (z, (0 : E)) ∈ P.source} :=
    P.open_source.preimage (continuous_id.prodMk continuous_const)
  have hsourceNhd : {z : E | (z, (0 : E)) ∈ P.source} ∈
      nhds (extChartAt I x₀ x₀) :=
    hopenSourceSlice.mem_nhds hcenterSource
  have hgood : ∀ᶠ z in nhds (extChartAt I x₀ x₀),
      (z, (0 : E)) ∈ P.source ∧ P (z, (0 : E)) = (z, z) := by
    filter_upwards [hsourceNhd, hstationary] with z hzSource hzStationary
    exact ⟨hzSource, hzStationary⟩
  rcases _root_.mem_nhds_iff.mp hgood with ⟨U, hUsub, hUopen, hcenterU⟩
  let C : FixedChartAnchorEndpointPackage g x₀ :=
    { selector := H
      time := T
      time_pos := hT
      derivative := D
      endpoint := P
      time_protected := hTprotected
      endpoint_hasStrictFDerivAt := hjoint
      endpoint_apply := hPapply
      coordinateAnchors := U
      isOpen_coordinateAnchors := hUopen
      center_mem_coordinateAnchors := hcenterU
      zero_mem_source := fun z hz => (hUsub hz).1
      zero_stationary := fun z hz => (hUsub hz).2 }
  exact ⟨C, hprotected⟩

/-- Every fixed manifold chart produces a product inverse-function package
with an honest open stationary anchor slice, hence a raw manifold
`LocalFamily`.  This is the universal-neighborhood specialization of the
protected-range constructor. -/
theorem exists_fixedChartAnchorEndpointPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    Nonempty (FixedChartAnchorEndpointPackage g x₀) := by
  rcases
      exists_fixedChartAnchorEndpointPackage_with_projected_protectedInnerBall_subset
        g x₀ (U := Set.univ) Filter.univ_mem with
    ⟨C, _hprotected⟩
  exact ⟨C⟩

/-- Choose the fixed package so every protected selector position remains in
the fixed source chart and its cutoff-one locus. -/
theorem exists_fixedChartAnchorEndpointPackage_with_fixedSourceChartCutoff_protectedInnerBall
    [T2Space M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀ := by
  have hfixed :
      (extChartAt I x₀).target ∩ IsometryInstantiate.cutoffOneLocus x₀ ∈
        nhds (extChartAt I x₀ x₀) :=
    inter_mem (extChartAt_target_mem_nhds x₀)
      (IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x₀)
  have hpre : Prod.fst ⁻¹'
      ((extChartAt I x₀).target ∩ IsometryInstantiate.cutoffOneLocus x₀) ∈
        nhds (extChartAt I x₀ x₀, (0 : E)) :=
    continuous_fst.continuousAt.preimage_mem_nhds hfixed
  rcases
      exists_fixedChartAnchorEndpointPackage_with_projected_protectedInnerBall_subset
        g x₀ hpre with
    ⟨C, hC⟩
  exact ⟨C, fun q hq => hC hq⟩

/-- Postcompose a local normal vector by a jointly continuous
anchor-dependent coordinate transport.  The open loci are unchanged. -/
def postcomposeNormal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : CartanSourceExponential.LocalFamily g)
    (transport : M × E → E)
    (htransport : ContinuousOn
      (fun q : M × M => transport (q.1, A.normal q)) A.sourceLocus)
    (hzero : ∀ x ∈ A.anchors, transport (x, (0 : E)) = 0) :
    CartanSourceExponential.LocalFamily g where
  anchors := A.anchors
  isOpen_anchors := A.isOpen_anchors
  sourceLocus := A.sourceLocus
  isOpen_sourceLocus := A.isOpen_sourceLocus
  sourceLocus_fst := A.sourceLocus_fst
  normal q := transport (q.1, A.normal q)
  continuousOn_normal := htransport
  diagonal_mem := A.diagonal_mem
  normal_diagonal x hx := by
    rw [A.normal_diagonal x hx, hzero x hx]

@[simp]
theorem postcomposeNormal_anchors
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : CartanSourceExponential.LocalFamily g)
    (transport : M × E → E)
    (htransport : ContinuousOn
      (fun q : M × M => transport (q.1, A.normal q)) A.sourceLocus)
    (hzero : ∀ x ∈ A.anchors, transport (x, (0 : E)) = 0) :
    (postcomposeNormal A transport htransport hzero).anchors = A.anchors :=
  rfl

@[simp]
theorem postcomposeNormal_sourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : CartanSourceExponential.LocalFamily g)
    (transport : M × E → E)
    (htransport : ContinuousOn
      (fun q : M × M => transport (q.1, A.normal q)) A.sourceLocus)
    (hzero : ∀ x ∈ A.anchors, transport (x, (0 : E)) = 0) :
    (postcomposeNormal A transport htransport hzero).sourceLocus =
      A.sourceLocus :=
  rfl

@[simp]
theorem postcomposeNormal_normal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : CartanSourceExponential.LocalFamily g)
    (transport : M × E → E)
    (htransport : ContinuousOn
      (fun q : M × M => transport (q.1, A.normal q)) A.sourceLocus)
    (hzero : ∀ x ∈ A.anchors, transport (x, (0 : E)) = 0)
    (q : M × M) :
    (postcomposeNormal A transport htransport hzero).normal q =
      transport (q.1, A.normal q) :=
  rfl

end CartanSourceExponentialLocalFamilyTransport
end Poincare
