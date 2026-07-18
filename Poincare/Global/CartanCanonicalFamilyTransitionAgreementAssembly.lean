import Poincare.Global.CartanSourceExponentialLocalFamilyTransitionAgreement
import Poincare.Global.CartanCanonicalFamilyLocalUniformData

/-!
# Canonical Cartan continuation from fixed-chart transition packages

This module composes the two local constructions that were previously
separate:

* a positive lower-semicontinuous minorant of the canonical curvature radius
  gives one generic-normal data radius on a neighborhood of each anchor; and
* a fixed-chart product inverse, together with its honest varying-anchor
  transition agreement, gives a jointly continuous local normal family.

Restricting the latter family to the former neighborhood and taking the
minimum of the two positive radii produces the open local source-family cover
consumed by `universalSuccessorDataNeighborhood_of_localSourceFamilyCover`.
Thus the only remaining Cartan inputs are the explicitly named radius
minorant and transition-agreement packages.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

namespace CartanSourceExponential

namespace LocalFamily

/-- Restrict a chart-local normal family to an additional open set of source
anchors.  Both the anchor set and the joint endpoint locus are restricted;
the normal-coordinate function itself is unchanged. -/
def restrictAnchors
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (U : Set M) (hU : IsOpen U) : LocalFamily g where
  anchors := A.anchors ∩ U
  isOpen_anchors := A.isOpen_anchors.inter hU
  sourceLocus := A.sourceLocus ∩ Prod.fst ⁻¹' U
  isOpen_sourceLocus :=
    A.isOpen_sourceLocus.inter (hU.preimage continuous_fst)
  sourceLocus_fst q hq := ⟨A.sourceLocus_fst q hq.1, hq.2⟩
  normal := A.normal
  continuousOn_normal := A.continuousOn_normal.mono (fun _q hq ↦ hq.1)
  diagonal_mem x hx := ⟨A.diagonal_mem x hx.1, hx.2⟩
  normal_diagonal x hx := A.normal_diagonal x hx.1

@[simp]
theorem restrictAnchors_anchors
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (U : Set M) (hU : IsOpen U) :
    (A.restrictAnchors U hU).anchors = A.anchors ∩ U :=
  rfl

@[simp]
theorem restrictAnchors_sourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (U : Set M) (hU : IsOpen U) :
    (A.restrictAnchors U hU).sourceLocus =
      A.sourceLocus ∩ Prod.fst ⁻¹' U :=
  rfl

@[simp]
theorem restrictAnchors_normal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (U : Set M) (hU : IsOpen U) (q : M × M) :
    (A.restrictAnchors U hU).normal q = A.normal q :=
  rfl

/-- Generic endpoint agreement is preserved by restricting the anchor set. -/
theorem GenericEndpointAgreement.restrictAnchors
    {g : ClosedSmoothRiemannianMetric 3 M}
    {A : LocalFamily g} {radius : ℝ}
    (h : A.GenericEndpointAgreement radius)
    (U : Set M) (hU : IsOpen U) :
    (A.restrictAnchors U hU).GenericEndpointAgreement radius := by
  refine {
    point_mem_anchorChart := ?_
    vector_mem_genericExpSource := ?_
    endpoint_coordinate := ?_ }
  · intro x z hz hnorm
    exact h.point_mem_anchorChart x z hz.1 hnorm
  · intro x z hz hnorm
    exact h.vector_mem_genericExpSource x z hz.1 hnorm
  · intro x z hz hnorm
    exact h.endpoint_coordinate x z hz.1 hnorm

/-- Endpoint agreement at a radius remains valid at every smaller radius. -/
theorem GenericEndpointAgreement.mono_radius
    {g : ClosedSmoothRiemannianMetric 3 M}
    {A : LocalFamily g} {r R : ℝ}
    (h : A.GenericEndpointAgreement R) (hr : r ≤ R) :
    A.GenericEndpointAgreement r := by
  refine {
    point_mem_anchorChart := ?_
    vector_mem_genericExpSource := ?_
    endpoint_coordinate := ?_ }
  · intro x z hz hnorm
    exact h.point_mem_anchorChart x z hz (hnorm.trans_le hr)
  · intro x z hz hnorm
    exact h.vector_mem_genericExpSource x z hz (hnorm.trans_le hr)
  · intro x z hz hnorm
    exact h.endpoint_coordinate x z hz (hnorm.trans_le hr)

end LocalFamily

end CartanSourceExponential

namespace CartanCanonicalFamilyTransitionAgreementAssembly

open CartanTargetExponential
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- A local endpoint-agreement family at every source anchor, together with a
positive lsc minorant of the canonical curvature radius, proves the complete
canonical successor-data neighborhood. -/
theorem universalSuccessorDataNeighborhood_of_joint_minorant_of_localEndpointAgreementCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤
        CartanCanonicalFamilyLocalUniformData.canonicalNormalAnchorTargetRadius
          hcurv x p)
    (hlocal : ∀ x₀ : M,
      ∃ A : LocalFamily g,
        x₀ ∈ A.anchors ∧
          ∃ localRadius > (0 : ℝ),
            A.GenericEndpointAgreement localRadius) :
    UniversalSuccessorDataNeighborhood canonicalFamily g := by
  apply universalSuccessorDataNeighborhood_of_localSourceFamilyCover
    canonicalFamily
  intro x₀
  rcases
      CartanCanonicalFamilyLocalUniformData.exists_chartLocal_genericNormal_canonicalData_of_joint_minorant
        hcurv pairRadius hpositive hlower hminorant x₀ with
    ⟨U, hU, hx₀U, genericRadius, hgenericRadius,
      hgenericData⟩
  rcases hlocal x₀ with
    ⟨A, hx₀A, localRadius, hlocalRadius, hendpoint⟩
  let radius : ℝ := min localRadius genericRadius
  have hradius : 0 < radius := lt_min hlocalRadius hgenericRadius
  let B : LocalFamily g := A.restrictAnchors U hU
  have hx₀B : x₀ ∈ B.anchors := ⟨hx₀A, hx₀U⟩
  have hendpointB : B.GenericEndpointAgreement radius := by
    exact
      (hendpoint.mono_radius (min_le_left _ _)).restrictAnchors U hU
  have hanchors : B.anchors ⊆ U := fun _x hx ↦ hx.2
  have hdataB : LocalUniformNormalSuccessorData B canonicalFamily := by
    apply
      CartanCanonicalFamilyLocalUniformData.localUniformNormalSuccessorData_of_genericEndpointAgreement
        B hradius hanchors hendpointB
    intro x hxU p L z hzSource hzNorm
    exact hgenericData x hxU p L z hzSource
      (hzNorm.trans_le (min_le_right _ _))
  exact ⟨B, hx₀B, hdataB⟩

/-- Concrete fixed-chart transition-agreement packages supply the local cover
in the preceding theorem. -/
theorem universalSuccessorDataNeighborhood_of_joint_minorant_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤
        CartanCanonicalFamilyLocalUniformData.canonicalNormalAnchorTargetRadius
          hcurv x p)
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage) :
    UniversalSuccessorDataNeighborhood canonicalFamily g := by
  apply
    universalSuccessorDataNeighborhood_of_joint_minorant_of_localEndpointAgreementCover
      hcurv pairRadius hpositive hlower hminorant
  intro x₀
  rcases htransition x₀ with ⟨C, ⟨P⟩⟩
  exact
    FixedChartAnchorEndpointPackage.TransitionAgreementPackage.exists_localFamily
      C P

/-- The same explicit inputs realize every prescribed mesh in an arbitrary
rooted Cartan path skeleton. -/
theorem exists_canonicalRootedPathChainRealization_with_prescribed_mesh_of_joint_minorant_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤
        CartanCanonicalFamilyLocalUniformData.canonicalNormalAnchorTargetRadius
          hcurv x p)
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage)
    (skeleton :
      CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        SuppliedRootedPathChainRealization canonicalFamily skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  let hneighborhood :
      UniversalSuccessorDataNeighborhood canonicalFamily g :=
    universalSuccessorDataNeighborhood_of_joint_minorant_of_transitionAgreementPackages
      hcurv pairRadius hpositive hlower hminorant htransition
  exact
    exists_canonicalRootedPathChainRealization_with_prescribed_mesh
      skeleton hneighborhood mesh hmesh

end CartanCanonicalFamilyTransitionAgreementAssembly

end Poincare
