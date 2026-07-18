import Poincare.Global.CartanFixedChartTransitionAgreementContinuityReduction

/-!
# Fixed-chart endpoint agreement through the generic inverse

The fixed-chart selector comparison previously asked for three separate
facts at every nearby anchor: the selected endpoint lies in the preferred
chart, the transported velocity lies in the public exponential source, and
the two endpoint coordinates agree.  Two of those are domain bookkeeping.

This file isolates the one geometric equality that remains after using the
jointly regular generic normal family.  If the fixed-chart endpoint is the
inverse evaluation of that family whenever the transported velocity is in
its joint target locus, then:

* target-locus membership supplies the public exponential-source condition;
* the inverse maps into the generic normal source, hence into the preferred
  chart source; and
* the partial-homeomorphism inverse laws supply the coordinate equality.

Joint target regularity makes target-locus membership uniform after shrinking
only the open anchor slice and choosing one positive velocity radius.  Thus a
same-package transition agreement follows from moving-derivative continuity
and one manifold endpoint identity.  No continuity or coherence of the bare
`ChartedSpace.chartAt` selector is asserted here.
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
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

open CartanSourceExponential
open CartanGenericSuccessorDataMovingPersistenceReduction

/-! ## Domain facts supplied by the generic inverse -/

/-- Membership in the target of the generic normal chart includes membership
in the source of the public charted exponential. -/
theorem genericExpSource_of_mem_genericTargetLocus
    {x : M} {v : E}
    (hv : (x, v) ∈ (genericFamily g).targetLocus) :
    v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x).source := by
  change v ∈ ((chartAt E x).trans
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) x).symm).target at hv
  rw [OpenPartialHomeomorph.trans_target] at hv
  exact hv.1

/-- The inverse evaluation of a generic target vector lies in the preferred
chart source. -/
theorem genericSymmEval_mem_preferredChartSource
    {x : M} {v : E}
    (hv : (x, v) ∈ (genericFamily g).targetLocus) :
    (genericFamily g).symmEval (x, v) ∈ (chartAt E x).source := by
  have hz :
      (genericFamily g).symmEval (x, v) ∈
        ((genericFamily g).normal x).source :=
    ((genericFamily g).normal x).symm.map_source hv
  change (genericFamily g).symmEval (x, v) ∈
    ((chartAt E x).trans
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x).symm).source at hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  exact hz.1

/-- On the joint generic target locus, preferred-chart evaluation of the
generic inverse is the public charted exponential evaluation. -/
theorem preferredChart_genericSymmEval_eq_expAtChart
    {x : M} {v : E}
    (hv : (x, v) ∈ (genericFamily g).targetLocus) :
    (chartAt E x) ((genericFamily g).symmEval (x, v)) =
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x v := by
  let S := genericFamily g
  let e := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
  let z : M := S.symmEval (x, v)
  have hzSource : z ∈ (S.normal x).source :=
    (S.normal x).symm.map_source hv
  change z ∈ ((chartAt E x).trans e.symm).source at hzSource
  rw [OpenPartialHomeomorph.trans_source] at hzSource
  have hzExpTarget : (chartAt E x) z ∈ e.target := hzSource.2
  have hnormal : S.normal x z = v :=
    (S.normal x).right_inv hv
  have hinverse : e.symm ((chartAt E x) z) = v := by
    change e.symm ((chartAt E x) z) = v at hnormal
    exact hnormal
  calc
    (chartAt E x) (S.symmEval (x, v)) = (chartAt E x) z := rfl
    _ = e (e.symm ((chartAt E x) z)) := (e.right_inv hzExpTarget).symm
    _ = e v := congrArg e hinverse

/-! ## The one remaining endpoint identity -/

/--
The fixed-chart ODE selector and the public varying-anchor exponential have
the same manifold endpoint whenever the transported velocity is in the joint
target of the generic normal family.

This is strictly narrower than `FixedPositiveTimeEndpointAgreement`: it has
no radius and assumes neither preferred-chart membership nor public
exponential-source membership nor coordinate equality.  Those facts are
derived from the generic inverse below.
-/
def GenericInverseEndpointAgreement
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
    (extChartAt I x₀ x, w) ∈ C.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      C.fixedTimeEndpoint x w =
        (genericFamily g).symmEval
          (x, fixedToAnchorVelocity x₀ (x, w))

/-- The inverse-endpoint identity is preserved when only the open anchor
slice is restricted. -/
theorem genericInverseEndpointAgreement_restrictToOpenAnchorSet
    (C : FixedChartAnchorEndpointPackage g x₀)
    (h : C.GenericInverseEndpointAgreement)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).GenericInverseEndpointAgreement := by
  intro x w hxAnchor hwSource htarget
  have hxOld :=
    C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
      V hV hx₀V hxAnchor
  simpa only [restrictToOpenAnchorSet_endpoint,
    restrictToOpenAnchorSet_fixedTimeEndpoint] using
      h x w hxOld
        (by simpa only [restrictToOpenAnchorSet_endpoint] using hwSource)
        htarget

/-- Once small transported velocities are known to lie in the generic target
locus, the single inverse-endpoint identity supplies all three fields of the
existing fixed-positive-time endpoint contract. -/
theorem fixedPositiveTimeEndpointAgreement_of_genericInverseEndpointAgreement
    (C : FixedChartAnchorEndpointPackage g x₀) {radius : ℝ}
    (hinverse : C.GenericInverseEndpointAgreement)
    (htarget : ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
      (extChartAt I x₀ x, w) ∈ C.endpoint.source →
      ‖fixedToAnchorVelocity x₀ (x, w)‖ < radius →
        (x, fixedToAnchorVelocity x₀ (x, w)) ∈
          (genericFamily g).targetLocus) :
    C.FixedPositiveTimeEndpointAgreement radius := by
  refine {
    point_mem_anchorChart := ?_
    vector_mem_genericExpSource := ?_
    endpoint_coordinate := ?_ }
  · intro x w hxAnchor hwSource hnorm
    have hmem := htarget x w hxAnchor hwSource hnorm
    rw [hinverse x w hxAnchor hwSource hmem]
    exact genericSymmEval_mem_preferredChartSource hmem
  · intro x w hxAnchor hwSource hnorm
    exact genericExpSource_of_mem_genericTargetLocus
      (htarget x w hxAnchor hwSource hnorm)
  · intro x w hxAnchor hwSource hnorm
    have hmem := htarget x w hxAnchor hwSource hnorm
    rw [hinverse x w hxAnchor hwSource hmem]
    exact preferredChart_genericSymmEval_eq_expAtChart hmem

/-! ## Uniform target control from joint regularity -/

/-- Joint regularity of the generic family provides an open anchor
restriction and one positive vector radius whose product lies in the generic
target locus.  The fixed-chart endpoint source plays no role in this purely
topological step. -/
theorem exists_openAnchorRestriction_genericTargetRadius
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hregular : GenericJointRegularity g) :
    ∃ (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
        (radius : ℝ),
      0 < radius ∧
      ∀ (x : M) (w : E),
        x ∈ (C.restrictToOpenAnchorSet V hV hx₀V).rawLocalFamily.anchors →
        ‖fixedToAnchorVelocity x₀ (x, w)‖ < radius →
          (x, fixedToAnchorVelocity x₀ (x, w)) ∈
            (genericFamily g).targetLocus := by
  let S := genericFamily g
  have hcenterTarget : (x₀, (0 : E)) ∈ S.targetLocus := by
    change (0 : E) ∈ (S.normal x₀).target
    have hmap := (S.normal x₀).map_source (S.anchor_mem_source x₀)
    simpa [S.normal_anchor x₀] using hmap
  have htargetNhds : S.targetLocus ∈ 𝓝 (x₀, (0 : E)) :=
    hregular.isOpen_targetLocus.mem_nhds hcenterTarget
  rcases mem_nhds_prod_iff.mp htargetNhds with
    ⟨U, hU, W, hW, hproduct⟩
  rcases _root_.mem_nhds_iff.mp hU with
    ⟨V, hVU, hVopen, hx₀V⟩
  rcases Metric.mem_nhds_iff.mp hW with
    ⟨radius, hradius, hball⟩
  refine ⟨V, hVopen, hx₀V, radius, hradius, ?_⟩
  intro x w hxAnchor hnorm
  have hxV :=
    C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset
      V hVopen hx₀V hxAnchor
  have hvBall : fixedToAnchorVelocity x₀ (x, w) ∈
      Metric.ball (0 : E) radius := by
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm
  exact hproduct ⟨hVU hxV, hball hvBall⟩

/-! ## Same-package transition agreement -/

/--
Moving-derivative continuity and the single inverse-endpoint identity produce
an actual transition-agreement package after shrinking only the anchor slice.
The positive radius and all endpoint-domain fields are generated from joint
regularity of the generic family.
-/
theorem exists_restrictedTransitionAgreementPackage_of_genericJointRegularity
    (C : FixedChartAnchorEndpointPackage g x₀)
    (htransition : ContinuousOn
      (fixedToPreferredTransitionDerivative x₀)
      C.rawLocalFamily.anchors)
    (hregular : GenericJointRegularity g)
    (hinverse : C.GenericInverseEndpointAgreement) :
    ∃ C' : FixedChartAnchorEndpointPackage g x₀,
      Nonempty C'.TransitionAgreementPackage := by
  rcases C.exists_openAnchorRestriction_genericTargetRadius hregular with
    ⟨V, hV, hx₀V, radius, hradius, htarget⟩
  let C' := C.restrictToOpenAnchorSet V hV hx₀V
  have htransition' : ContinuousOn
      (fixedToPreferredTransitionDerivative x₀)
      C'.rawLocalFamily.anchors :=
    htransition.mono
      (C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
        V hV hx₀V)
  have hjoint : C'.TransitionVelocityJointContinuity :=
    C'.transitionVelocityJointContinuity_of_fixedToPreferredTransitionDerivative_continuousOn
      htransition'
  have hinverse' : C'.GenericInverseEndpointAgreement :=
    C.genericInverseEndpointAgreement_restrictToOpenAnchorSet
      hinverse V hV hx₀V
  have hendpoint : C'.FixedPositiveTimeEndpointAgreement radius :=
    C'.fixedPositiveTimeEndpointAgreement_of_genericInverseEndpointAgreement
      hinverse' (fun x w hx hw hnorm => htarget x w hx hnorm)
  exact ⟨C', ⟨{
    radius := radius
    radius_pos := hradius
    jointContinuity := hjoint
    fixedTimeEndpoint := hendpoint }⟩⟩

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport

/-! ## Pointwise provider -/

namespace CartanFixedChartGenericInverseEndpointReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport
open CartanGenericSuccessorDataMovingPersistenceReduction
open CartanFixedChartTransitionAgreementSubordination

/-- Per-center moving-derivative continuity and one generic-inverse endpoint
identity on a concrete fixed-chart package. -/
def PointwiseFixedChartGenericInverseEndpointData
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      ContinuousOn (fixedToPreferredTransitionDerivative x₀)
        C.rawLocalFamily.anchors ∧
      C.GenericInverseEndpointAgreement

/-- Joint generic regularity turns the pointwise inverse-endpoint data into
the existing pointwise transition-agreement provider. -/
theorem pointwiseFixedChartTransitionAgreementPackage_of_genericInverseEndpointData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hregular : GenericJointRegularity g)
    (hdata : PointwiseFixedChartGenericInverseEndpointData g) :
    PointwiseFixedChartTransitionAgreementPackage g := by
  intro x₀
  rcases hdata x₀ with ⟨C, htransition, hinverse⟩
  exact C.exists_restrictedTransitionAgreementPackage_of_genericJointRegularity
    htransition hregular hinverse

end CartanFixedChartGenericInverseEndpointReduction
end Poincare
