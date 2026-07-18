import Poincare.Global.CartanCanonicalFamilyComparedNeighborhood

/-!
# Compared successors from forward source-normal regularity

`CartanSourceExponential.GenericJointRegularity` records four moving-anchor
facts: openness of the forward and inverse loci and continuity of both the
forward and inverse evaluations.  The compared-successor local-cover proof
uses only two of them: openness of the generic forward source locus and
continuity of the generic normal coordinate on that locus.

This module isolates that strictly smaller contract.  It also records the
still weaker, local contract naturally matched by the intrinsic fixed-chart
ODE construction: for every center and every desired generic-normal
tolerance, some jointly regular local normal family controls the hardcoded
generic normal at a positive local scale.  This control relation contains no
transition map, endpoint-coordinate equality, or fixed-time package.

The fixed-chart selector and stationary-slice theorems already construct the
jointly regular local families.  What their current API does not prove is the
last comparison with the independently selected preferred-chart exponential.
That exact residual comparison is exposed here without retaining the stronger
`TransitionAgreementPackage` interface.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyComparedForwardNormalRegularity

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport
open CartanCanonicalFamilySuccessorProvenance
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanCanonicalFamilyProvenanceRootedAssembly

/-- The exact forward half of generic source-normal joint regularity used by
the compared-successor local-cover argument. -/
structure GenericForwardNormalRegularity
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  isOpen_sourceLocus : IsOpen (genericFamily g).sourceLocus
  continuousOn_normal :
    ContinuousOn (genericFamily g).eval (genericFamily g).sourceLocus

/-- Pointwise-local formulation of forward source-normal regularity.  This is
the form naturally produced by a moving-anchor exponential theorem: the
chosen source is a neighborhood of each of its points and the normal map is
continuous there. -/
structure GenericForwardNormalPointwiseRegularity
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  source_mem_nhds : ∀ q ∈ (genericFamily g).sourceLocus,
    (genericFamily g).sourceLocus ∈ 𝓝 q
  continuousAt_normal : ∀ q ∈ (genericFamily g).sourceLocus,
    ContinuousAt (genericFamily g).eval q

/-- Pointwise intrinsic exponential regularity assembles into the exact
forward regularity contract. -/
theorem GenericForwardNormalPointwiseRegularity.toForward
    {g : ClosedSmoothRiemannianMetric 3 M}
    (h : GenericForwardNormalPointwiseRegularity g) :
    GenericForwardNormalRegularity g := by
  refine ⟨?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    exact h.source_mem_nhds
  · intro q hq
    exact (h.continuousAt_normal q hq).continuousWithinAt

/-- Full generic joint regularity implies its strictly smaller forward half. -/
theorem GenericForwardNormalRegularity.ofJoint
    {g : ClosedSmoothRiemannianMetric 3 M}
    (h : GenericJointRegularity g) :
    GenericForwardNormalRegularity g :=
  ⟨h.isOpen_sourceLocus, h.continuousOn_eval⟩

/-- Restrict a forward-regular generic normal family to an open anchor set.
Neither inverse-locus openness nor inverse-evaluation continuity is used. -/
def genericForwardLocalFamily
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hforward : GenericForwardNormalRegularity g)
    (U : Set M) (hU : IsOpen U) : LocalFamily g where
  anchors := U
  isOpen_anchors := hU
  sourceLocus := Prod.fst ⁻¹' U ∩ (genericFamily g).sourceLocus
  isOpen_sourceLocus :=
    (hU.preimage continuous_fst).inter hforward.isOpen_sourceLocus
  sourceLocus_fst := by
    intro q hq
    exact hq.1
  normal := (genericFamily g).eval
  continuousOn_normal :=
    hforward.continuousOn_normal.mono (fun _q hq ↦ hq.2)
  diagonal_mem := by
    intro x hx
    exact ⟨hx, (genericFamily g).anchor_mem_source x⟩
  normal_diagonal := by
    intro x _hx
    exact (genericFamily g).normal_anchor x

@[simp]
theorem genericForwardLocalFamily_anchors
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hforward : GenericForwardNormalRegularity g)
    (U : Set M) (hU : IsOpen U) :
    (genericForwardLocalFamily g hforward U hU).anchors = U :=
  rfl

@[simp]
theorem genericForwardLocalFamily_normal
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hforward : GenericForwardNormalRegularity g)
    (U : Set M) (hU : IsOpen U) (x z : M) :
    (genericForwardLocalFamily g hforward U hU).normal (x, z) =
      (genericFamily g).normal x z :=
  rfl

/-- The weakest local intrinsic-normal comparison used below.  For every
center and every requested tolerance in the hardcoded generic normal, one
jointly regular local normal family controls generic source membership and
that tolerance at some positive local radius.

The family may depend on the tolerance.  No equality of normal vectors and no
transition or endpoint package is required. -/
def GenericNormalControlledLocalFamilyCover
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (genericRadius : ℝ), 0 < genericRadius →
    ∃ A : LocalFamily g, x₀ ∈ A.anchors ∧
      ∃ localRadius > (0 : ℝ),
        A.ControlsGenericNormal localRadius genericRadius

/-- Forward regularity supplies the local control cover definitionally by
using the generic normal family itself. -/
theorem GenericForwardNormalRegularity.controlledLocalFamilyCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hforward : GenericForwardNormalRegularity g) :
    GenericNormalControlledLocalFamilyCover g := by
  intro x₀ genericRadius hgenericRadius
  let A : LocalFamily g :=
    genericForwardLocalFamily g hforward Set.univ isOpen_univ
  refine ⟨A, Set.mem_univ x₀, genericRadius, hgenericRadius, ?_⟩
  intro x z hzSource hzNorm
  exact ⟨hzSource.2, hzNorm⟩

/-- The former transition-agreement boundary implies the new control cover.
This one-way conversion records that the new premise retains strictly less
proof data: only generic source membership and a norm estimate survive. -/
theorem controlledLocalFamilyCover_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage) :
    GenericNormalControlledLocalFamilyCover g := by
  intro x₀ genericRadius hgenericRadius
  rcases htransition x₀ with ⟨C, ⟨P⟩⟩
  rcases P.exists_localFamily with
    ⟨A, hx₀A, endpointRadius, hendpointRadius, hendpoint⟩
  let localRadius : ℝ := min endpointRadius genericRadius
  have hlocalRadius : 0 < localRadius :=
    lt_min hendpointRadius hgenericRadius
  have hendpointLocal : A.GenericEndpointAgreement localRadius :=
    hendpoint.mono_radius (min_le_left _ _)
  have hbase : A.ControlsGenericNormal localRadius localRadius :=
    hendpointLocal.controlsGenericNormal
  refine ⟨A, hx₀A, localRadius, hlocalRadius, ?_⟩
  intro x z hzSource hzNorm
  rcases hbase x z hzSource hzNorm with
    ⟨hzGenericSource, hzGenericNorm⟩
  exact ⟨hzGenericSource,
    hzGenericNorm.trans_le (min_le_right endpointRadius genericRadius)⟩

/-- Transfer a generic-normal provenance producer through the minimal local
normal-control relation.  This is the provenance-retaining counterpart of
`CartanSourceExponential.localUniformNormalSuccessorData_of_controlsGenericNormal`.
-/
theorem localUniformTransferredData_of_controlsGenericNormal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g)
    {localRadius genericRadius : ℝ}
    (hlocalRadius : 0 < localRadius)
    (hcontrol : A.ControlsGenericNormal localRadius genericRadius)
    (hgenericPackage :
      ∀ (x : M), x ∈ A.anchors →
        ∀ (p : RoundSphere3)
          (L : CartanMap.TangentAlignment g x p) (z : M),
          z ∈ ((genericFamily g).normal x).source →
          ‖(genericFamily g).normal x z‖ < genericRadius →
            Nonempty
              (TransferredSuccessorPackage
                (CartanChain.ChainState.mk x p L) z)) :
    LocalUniformNormalTransferredSuccessorData A := by
  refine ⟨localRadius, hlocalRadius, ?_⟩
  intro x p L z hzSource hzNorm
  rcases hcontrol x z hzSource hzNorm with
    ⟨hzGenericSource, hzGenericNorm⟩
  exact hgenericPackage x (A.sourceLocus_fst (x, z) hzSource)
    p L z hzGenericSource hzGenericNorm

section T2

variable [T2Space M]

/-- A local generic-normal package cover and the exact local normal-control
cover imply the full compared-successor diagonal neighborhood. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_localPackageCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrolCover : GenericNormalControlledLocalFamilyCover g)
    (hpackageCover : ∀ x₀ : M,
      ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
        ∃ genericRadius > (0 : ℝ),
          ∀ (x : M), x ∈ U →
            ∀ (p : RoundSphere3)
              (L : CartanMap.TangentAlignment g x p) (z : M),
              z ∈ ((genericFamily g).normal x).source →
              ‖(genericFamily g).normal x z‖ < genericRadius →
                Nonempty
                  (TransferredSuccessorPackage
                    (CartanChain.ChainState.mk x p L) z)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply comparedSuccessorLocus_mem_nhdsSet_of_localCover
  intro x₀
  rcases hpackageCover x₀ with
    ⟨U, hU, hx₀U, genericRadius, hgenericRadius, hpackage⟩
  rcases hcontrolCover x₀ genericRadius hgenericRadius with
    ⟨A, hx₀A, localRadius, hlocalRadius, hcontrol⟩
  let B : LocalFamily g := A.restrictAnchors U hU
  have hcontrolB : B.ControlsGenericNormal localRadius genericRadius := by
    intro x z hzSource hzNorm
    exact hcontrol x z hzSource.1 hzNorm
  have hpackageB :
      ∀ (x : M), x ∈ B.anchors →
        ∀ (p : RoundSphere3)
          (L : CartanMap.TangentAlignment g x p) (z : M),
          z ∈ ((genericFamily g).normal x).source →
          ‖(genericFamily g).normal x z‖ < genericRadius →
            Nonempty
              (TransferredSuccessorPackage
                (CartanChain.ChainState.mk x p L) z) := by
    intro x hx p L z hzSource hzNorm
    exact hpackage x hx.2 p L z hzSource hzNorm
  refine ⟨B, ⟨hx₀A, hx₀U⟩, ?_⟩
  exact localUniformTransferredData_of_controlsGenericNormal
    B hlocalRadius hcontrolB hpackageB

/-- Forward source-normal regularity is sufficient for a compared neighborhood
from any source-local generic package cover. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_forwardRegularity_of_localPackageCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hforward : GenericForwardNormalRegularity g)
    (hpackageCover : ∀ x₀ : M,
      ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
        ∃ genericRadius > (0 : ℝ),
          ∀ (x : M), x ∈ U →
            ∀ (p : RoundSphere3)
              (L : CartanMap.TangentAlignment g x p) (z : M),
              z ∈ ((genericFamily g).normal x).source →
              ‖(genericFamily g).normal x z‖ < genericRadius →
                Nonempty
                  (TransferredSuccessorPackage
                    (CartanChain.ChainState.mk x p L) z)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_localPackageCover
      hforward.controlledLocalFamilyCover hpackageCover

section Compact

variable [CompactSpace M] [ConnectedSpace M]

/-- The exact local normal-control cover, together with transferred-radius
local stability, removes the compared-successor neighborhood premise. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_localStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (hstable : TransferredNormalRadiusLocalStability g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_localPackageCover
      hcontrol
  intro x₀
  exact exists_chartLocal_genericNormal_transferredPackage_of_localStability
    g hstable x₀

/-- Only the forward half of generic source joint regularity is needed when
the transferred radius is locally stable. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_forwardRegularity_of_localStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hforward : GenericForwardNormalRegularity g)
    (hstable : TransferredNormalRadiusLocalStability g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_localStability
      hforward.controlledLocalFamilyCover hstable

/-- Pointwise moving-anchor source openness and normal continuity are already
sufficient; none of the inverse half of `GenericJointRegularity` is needed. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_pointwiseForwardRegularity_of_localStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hpointwise : GenericForwardNormalPointwiseRegularity g)
    (hstable : TransferredNormalRadiusLocalStability g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_forwardRegularity_of_localStability
      hpointwise.toForward hstable

/-- Unit curvature plus a positive lower-semicontinuous minorant of the
automatic transferred radius needs only the exact local normal-control cover.
-/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_controlledLocalFamilyCover_of_jointMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalTransferredAnchorTargetRadius hcurv x p) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_localPackageCover
      hcontrol
  intro x₀
  exact exists_chartLocal_genericNormal_transferredPackage_of_joint_minorant
    hcurv pairRadius hpositive hlower hminorant x₀

/-- Use the automatically selected pointwise curvature radius itself.  Its
positivity and admissibility are discharged; only lower semicontinuity and
the exact local normal-control cover remain. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_controlledLocalFamilyCover_of_canonicalRadiusLowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalTransferredAnchorTargetRadius hcurv xp.1 xp.2)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_controlledLocalFamilyCover_of_jointMinorant
      hcurv hcontrol
      (fun x p ↦ canonicalTransferredAnchorTargetRadius hcurv x p)
      (canonicalTransferredAnchorTargetRadius_pos hcurv)
      hlower
      (fun _x _p ↦ le_rfl)

/-- Forward-normal specialization of the curvature/minorant theorem. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_forwardRegularity_of_jointMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hforward : GenericForwardNormalRegularity g)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalTransferredAnchorTargetRadius hcurv x p) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_controlledLocalFamilyCover_of_jointMinorant
      hcurv hforward.controlledLocalFamilyCover
      pairRadius hpositive hlower hminorant

/-- Forward-normal form with the automatic curvature radius. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_forwardRegularity_of_canonicalRadiusLowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hforward : GenericForwardNormalRegularity g)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalTransferredAnchorTargetRadius hcurv xp.1 xp.2)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_controlledLocalFamilyCover_of_canonicalRadiusLowerSemicontinuous
      hcurv hforward.controlledLocalFamilyCover hlower

/-- Pointwise intrinsic-exponential specialization of the curvature/minorant
route. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_pointwiseForwardRegularity_of_jointMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hpointwise : GenericForwardNormalPointwiseRegularity g)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalTransferredAnchorTargetRadius hcurv x p) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_forwardRegularity_of_jointMinorant
      hcurv hpointwise.toForward pairRadius hpositive hlower hminorant

/-- Pointwise moving-anchor form with the automatic curvature radius. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_pointwiseForwardRegularity_of_canonicalRadiusLowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hpointwise : GenericForwardNormalPointwiseRegularity g)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalTransferredAnchorTargetRadius hcurv xp.1 xp.2)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_forwardRegularity_of_canonicalRadiusLowerSemicontinuous
      hcurv hpointwise.toForward hlower

end Compact

end T2

end CartanCanonicalFamilyComparedForwardNormalRegularity
end Poincare
