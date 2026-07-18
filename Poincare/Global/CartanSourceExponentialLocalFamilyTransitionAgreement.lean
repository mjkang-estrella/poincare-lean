import Poincare.Global.CartanSourceExponentialLocalFamilyTransport

/-!
# Varying-anchor transport for a chart-local source exponential

The product inverse-function theorem is constructed in one fixed chart.  Its
inverse second coordinate is consequently a velocity in that fixed chart.
The generic source exponential at a varying anchor `x`, however, uses the
preferred chart at `x`.  The correct change of velocity coordinates is

`chartTransitionDeriv x₀ x (extChartAt I x₀ x)`.

This file performs that postcomposition and isolates the two genuinely joint
inputs that are not supplied by the pointwise preferred-chart API:

* continuity of the transported inverse velocity on the joint endpoint locus;
* agreement, at the one positive time selected by the fixed-chart package,
  with the public exponential based at the varying anchor.

The endpoint premise is stated before taking the inverse of the product
partial homeomorphism.  The consumer below proves that it gives exactly
`LocalFamily.GenericEndpointAgreement`; no generic-normal equality is assumed.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Function Set
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

/-- Convert a fixed-`x₀` chart velocity to the preferred coordinates at the
varying anchor. -/
def fixedToAnchorVelocity (x₀ : M) (q : M × E) : E :=
  GeodesicTransport.chartTransitionDeriv x₀ q.1
    (extChartAt I x₀ q.1) q.2

@[simp]
theorem fixedToAnchorVelocity_zero (x₀ x : M) :
    fixedToAnchorVelocity x₀ (x, (0 : E)) = 0 := by
  change
    GeodesicTransport.chartTransitionDeriv x₀ x
      (extChartAt I x₀ x) (0 : E) = 0
  exact
    (GeodesicTransport.chartTransitionDeriv x₀ x
      (extChartAt I x₀ x)).map_zero

/-- For a fixed varying anchor, velocity transport is continuous.  Thus the
only continuity not supplied pointwise is dependence of the transition
operator on the preferred-chart anchor itself. -/
theorem continuous_fixedToAnchorVelocity_fixedAnchor (x₀ x : M) :
    Continuous (fun w : E => fixedToAnchorVelocity x₀ (x, w)) := by
  exact
    (GeodesicTransport.chartTransitionDeriv x₀ x
      (extChartAt I x₀ x)).continuous

/-- At the fixed-chart center, the coordinate transport is the identity. -/
@[simp]
theorem fixedToAnchorVelocity_self (x : M) (w : E) :
    fixedToAnchorVelocity x (x, w) = w := by
  have htransition :
      GeodesicTransport.chartTransition (n := 3) x x
        =ᶠ[nhds (extChartAt I x x)] id := by
    filter_upwards [extChartAt_target_mem_nhds x] with z hz
    simpa [GeodesicTransport.chartTransition] using
      (extChartAt I x).right_inv hz
  change
    fderiv ℝ (GeodesicTransport.chartTransition (n := 3) x x)
      (extChartAt I x x) w = w
  rw [htransition.fderiv_eq]
  simp

namespace FixedChartAnchorEndpointPackage

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

@[simp]
theorem rawLocalFamily_normal
    (C : FixedChartAnchorEndpointPackage g x₀) (q : M × M) :
    C.rawLocalFamily.normal q =
      (C.endpoint.symm (coordinatePair x₀ q)).2 :=
  rfl

/-- The fixed-chart inverse velocity after conversion to the preferred chart
at the varying anchor. -/
def transportedNormal
    (C : FixedChartAnchorEndpointPackage g x₀) (q : M × M) : E :=
  fixedToAnchorVelocity x₀ (q.1, C.rawLocalFamily.normal q)

/-- The exact joint-continuity obligation for the transported inverse.  This
is deliberately weaker than continuity of the preferred chart or of its
transition derivative on an ambient product: only the composite actually
stored in the local family is required. -/
def TransitionVelocityJointContinuity
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ContinuousOn C.transportedNormal C.rawLocalFamily.sourceLocus

/-- Postcompose the raw inverse velocity with the fixed-to-varying-anchor
chart transition. -/
def transportedLocalFamily
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hjoint : C.TransitionVelocityJointContinuity) :
    CartanSourceExponential.LocalFamily g :=
  postcomposeNormal C.rawLocalFamily (fixedToAnchorVelocity x₀)
    hjoint (fun x _hx => fixedToAnchorVelocity_zero x₀ x)

@[simp]
theorem transportedLocalFamily_anchors
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hjoint : C.TransitionVelocityJointContinuity) :
    (C.transportedLocalFamily hjoint).anchors = C.rawLocalFamily.anchors :=
  rfl

@[simp]
theorem transportedLocalFamily_sourceLocus
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hjoint : C.TransitionVelocityJointContinuity) :
    (C.transportedLocalFamily hjoint).sourceLocus =
      C.rawLocalFamily.sourceLocus :=
  rfl

@[simp]
theorem transportedLocalFamily_normal
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hjoint : C.TransitionVelocityJointContinuity) (q : M × M) :
    (C.transportedLocalFamily hjoint).normal q = C.transportedNormal q :=
  rfl

/-- The manifold endpoint represented by the fixed-chart selector at its
already selected positive time. -/
def fixedTimeEndpoint
    (C : FixedChartAnchorEndpointPackage g x₀) (x : M) (w : E) : M :=
  (extChartAt I x₀).symm
    (CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
      g x₀ C.selector C.time (extChartAt I x₀ x, w))

/-- On the product target, the inverse first coordinate is the supplied
anchor coordinate. -/
theorem endpoint_symm_coordinatePair_fst
    (C : FixedChartAnchorEndpointPackage g x₀) {q : M × M}
    (hq : q ∈ C.rawLocalFamily.sourceLocus) :
    (C.endpoint.symm (coordinatePair x₀ q)).1 = extChartAt I x₀ q.1 := by
  let r : E × E := C.endpoint.symm (coordinatePair x₀ q)
  have hrTarget : coordinatePair x₀ q ∈ C.endpoint.target := hq.2.2
  have hright : C.endpoint r = coordinatePair x₀ q :=
    C.endpoint.right_inv hrTarget
  have happly : C.endpoint r =
      (r.1,
        CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
          g x₀ C.selector C.time r) :=
    congrFun C.endpoint_apply r
  have hpair :
      (r.1,
        CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
          g x₀ C.selector C.time r) = coordinatePair x₀ q :=
    happly.symm.trans hright
  simpa [r, coordinatePair] using congrArg Prod.fst hpair

/-- A raw inverse point is in the product source, with the expected anchor
coordinate as its first component. -/
theorem anchor_rawNormal_mem_endpoint_source
    (C : FixedChartAnchorEndpointPackage g x₀) {q : M × M}
    (hq : q ∈ C.rawLocalFamily.sourceLocus) :
    (extChartAt I x₀ q.1, C.rawLocalFamily.normal q) ∈ C.endpoint.source := by
  have hr : C.endpoint.symm (coordinatePair x₀ q) ∈ C.endpoint.source :=
    C.endpoint.symm.map_source hq.2.2
  have hfst := C.endpoint_symm_coordinatePair_fst hq
  have hpair :
      (extChartAt I x₀ q.1, C.rawLocalFamily.normal q) =
        C.endpoint.symm (coordinatePair x₀ q) := by
    apply Prod.ext
    · exact hfst.symm
    · rfl
  rw [hpair]
  exact hr

/-- Applying the normalized selector to the inverse velocity recovers the
fixed-chart coordinate of the supplied endpoint. -/
theorem normalizedSelectorEndpoint_rawNormal
    (C : FixedChartAnchorEndpointPackage g x₀) {q : M × M}
    (hq : q ∈ C.rawLocalFamily.sourceLocus) :
    CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
        g x₀ C.selector C.time
        (extChartAt I x₀ q.1, C.rawLocalFamily.normal q) =
      extChartAt I x₀ q.2 := by
  let r : E × E := C.endpoint.symm (coordinatePair x₀ q)
  have hrTarget : coordinatePair x₀ q ∈ C.endpoint.target := hq.2.2
  have hright : C.endpoint r = coordinatePair x₀ q :=
    C.endpoint.right_inv hrTarget
  have happly : C.endpoint r =
      (r.1,
        CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
          g x₀ C.selector C.time r) :=
    congrFun C.endpoint_apply r
  have hpair :
      (r.1,
        CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint
          g x₀ C.selector C.time r) = coordinatePair x₀ q :=
    happly.symm.trans hright
  have hsnd := congrArg Prod.snd hpair
  have hfst : r.1 = extChartAt I x₀ q.1 := by
    simpa [r] using C.endpoint_symm_coordinatePair_fst hq
  have hinput :
      (extChartAt I x₀ q.1, C.rawLocalFamily.normal q) = r := by
    apply Prod.ext
    · exact hfst.symm
    · rfl
  rw [hinput]
  simpa [coordinatePair] using hsnd

/-- Consequently the selected positive-time manifold endpoint is exactly the
endpoint supplied to the product inverse. -/
theorem fixedTimeEndpoint_rawNormal
    (C : FixedChartAnchorEndpointPackage g x₀) {q : M × M}
    (hq : q ∈ C.rawLocalFamily.sourceLocus) :
    C.fixedTimeEndpoint q.1 (C.rawLocalFamily.normal q) = q.2 := by
  rw [fixedTimeEndpoint, C.normalizedSelectorEndpoint_rawNormal hq]
  exact (extChartAt I x₀).left_inv hq.2.1.2

/--
The smallest fixed-positive-time comparison used by the downstream generic
normal-coordinate interface.  It is imposed on the source of the concrete
product map, before applying its inverse.  The selected time is positive by
`C.time_pos`.

No equality of inverse normal vectors is assumed.  The three fields are just
the source and coordinate facts needed to invoke the public exponential
partial homeomorphism at the varying anchor.
-/
structure FixedPositiveTimeEndpointAgreement
    (C : FixedChartAnchorEndpointPackage g x₀) (radius : ℝ) : Prop where
  point_mem_anchorChart :
    ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
      (extChartAt I x₀ x, w) ∈ C.endpoint.source →
      ‖fixedToAnchorVelocity x₀ (x, w)‖ < radius →
        C.fixedTimeEndpoint x w ∈ (chartAt E x).source
  vector_mem_genericExpSource :
    ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
      (extChartAt I x₀ x, w) ∈ C.endpoint.source →
      ‖fixedToAnchorVelocity x₀ (x, w)‖ < radius →
        fixedToAnchorVelocity x₀ (x, w) ∈
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x).source
  endpoint_coordinate :
    ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
      (extChartAt I x₀ x, w) ∈ C.endpoint.source →
      ‖fixedToAnchorVelocity x₀ (x, w)‖ < radius →
        (chartAt E x) (C.fixedTimeEndpoint x w) =
          GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x (fixedToAnchorVelocity x₀ (x, w))

/-- Joint transition continuity and fixed-time endpoint comparison are
exactly sufficient to produce generic endpoint agreement for the transported
local family. -/
theorem transportedLocalFamily_genericEndpointAgreement
    (C : FixedChartAnchorEndpointPackage g x₀) {radius : ℝ}
    (hjoint : C.TransitionVelocityJointContinuity)
    (hendpoint : C.FixedPositiveTimeEndpointAgreement radius) :
    (C.transportedLocalFamily hjoint).GenericEndpointAgreement radius := by
  let A := C.transportedLocalFamily hjoint
  refine {
    point_mem_anchorChart := ?_
    vector_mem_genericExpSource := ?_
    endpoint_coordinate := ?_ }
  · intro x z hzSource hzNorm
    have hzRaw : (x, z) ∈ C.rawLocalFamily.sourceLocus := by
      simpa [A] using hzSource
    have hxAnchor : x ∈ C.rawLocalFamily.anchors :=
      C.rawLocalFamily.sourceLocus_fst (x, z) hzRaw
    have hwSource := C.anchor_rawNormal_mem_endpoint_source hzRaw
    have hnorm :
        ‖fixedToAnchorVelocity x₀
          (x, C.rawLocalFamily.normal (x, z))‖ < radius := by
      simpa [A, transportedNormal] using hzNorm
    have hmem := hendpoint.point_mem_anchorChart x
      (C.rawLocalFamily.normal (x, z)) hxAnchor hwSource hnorm
    rwa [C.fixedTimeEndpoint_rawNormal hzRaw] at hmem
  · intro x z hzSource hzNorm
    have hzRaw : (x, z) ∈ C.rawLocalFamily.sourceLocus := by
      simpa [A] using hzSource
    have hxAnchor : x ∈ C.rawLocalFamily.anchors :=
      C.rawLocalFamily.sourceLocus_fst (x, z) hzRaw
    have hwSource := C.anchor_rawNormal_mem_endpoint_source hzRaw
    have hnorm :
        ‖fixedToAnchorVelocity x₀
          (x, C.rawLocalFamily.normal (x, z))‖ < radius := by
      simpa [A, transportedNormal] using hzNorm
    simpa [A, transportedNormal] using
      hendpoint.vector_mem_genericExpSource x
        (C.rawLocalFamily.normal (x, z)) hxAnchor hwSource hnorm
  · intro x z hzSource hzNorm
    have hzRaw : (x, z) ∈ C.rawLocalFamily.sourceLocus := by
      simpa [A] using hzSource
    have hxAnchor : x ∈ C.rawLocalFamily.anchors :=
      C.rawLocalFamily.sourceLocus_fst (x, z) hzRaw
    have hwSource := C.anchor_rawNormal_mem_endpoint_source hzRaw
    have hnorm :
        ‖fixedToAnchorVelocity x₀
          (x, C.rawLocalFamily.normal (x, z))‖ < radius := by
      simpa [A, transportedNormal] using hzNorm
    have heq := hendpoint.endpoint_coordinate x
      (C.rawLocalFamily.normal (x, z)) hxAnchor hwSource hnorm
    rw [C.fixedTimeEndpoint_rawNormal hzRaw] at heq
    simpa [A, transportedNormal] using heq

/-- Proof-bearing package for the exact remaining varying-anchor inputs. -/
structure TransitionAgreementPackage
    (C : FixedChartAnchorEndpointPackage g x₀) where
  radius : ℝ
  radius_pos : 0 < radius
  jointContinuity : C.TransitionVelocityJointContinuity
  fixedTimeEndpoint : C.FixedPositiveTimeEndpointAgreement radius

/-- Downstream consumer: the concrete transition package produces a local
family containing the center anchor and carrying generic endpoint agreement
at a positive radius. -/
theorem TransitionAgreementPackage.exists_localFamily
    (C : FixedChartAnchorEndpointPackage g x₀)
    (P : C.TransitionAgreementPackage) :
    ∃ A : CartanSourceExponential.LocalFamily g,
      x₀ ∈ A.anchors ∧
      ∃ radius > (0 : ℝ), A.GenericEndpointAgreement radius := by
  refine ⟨C.transportedLocalFamily P.jointContinuity, ?_,
    P.radius, P.radius_pos, ?_⟩
  · exact C.center_mem_rawLocalFamily_anchors
  · exact C.transportedLocalFamily_genericEndpointAgreement
      P.jointContinuity P.fixedTimeEndpoint

end FixedChartAnchorEndpointPackage

end CartanSourceExponentialLocalFamilyTransport
end Poincare
