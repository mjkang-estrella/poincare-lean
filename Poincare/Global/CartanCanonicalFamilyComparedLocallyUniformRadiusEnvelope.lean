import Poincare.Global.CartanCanonicalFamilyComparedForwardNormalRegularity

/-!
# Canonical locally uniform transferred-radius envelopes

The curvature radius
`canonicalTransferredAnchorTargetRadius hcurv x p` is selected independently
at every parameter pair and depends on the proof `hcurv`.  Requiring that
particular choice to be lower-semicontinuous is therefore an unnecessarily
choice-sensitive boundary.

The provenance local-uniformity module already constructs a different radius:
`canonicalLocallyUniformTransferredAnchorTargetRadius g`.  It is defined from
all locally persistent admissible radii, is independent of a curvature proof,
and is automatically lower-semicontinuous.  This module packages that radius
as an envelope and proves that existence of such an envelope is equivalent to
`TransferredNormalRadiusLocalStability`.

We also sharpen the source-side input used to obtain local stability.  Full
joint regularity of the generic source family is not needed: continuity of
the inverse normal evaluation only along the zero section controls physical
endpoints.  Together with the existing local alignment-operator bound, this
gives exactly `GenericSourceNormalLocalStability`.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyComparedLocallyUniformRadiusEnvelope

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanSourceExponential
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalFamilyComparedForwardNormalRegularity

/-- The inverse-normal regularity actually used for endpoint control:
continuity only at the complete zero section.  No openness or regularity away
from `(x,0)` is retained. -/
def GenericInverseNormalZeroSectionContinuity
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x : M,
    ContinuousAt (genericFamily g).symmEval (x, (0 : E))

/-- Full generic joint regularity implies inverse-normal continuity on the
zero section. -/
theorem genericInverseNormalZeroSectionContinuity_of_jointRegularity
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : GenericJointRegularity g) :
    GenericInverseNormalZeroSectionContinuity g := by
  intro x
  let S := genericFamily g
  have hxSource : x ∈ (S.normal x).source := S.anchor_mem_source x
  have hxTarget : (x, (0 : E)) ∈ S.targetLocus := by
    change (0 : E) ∈ (S.normal x).target
    have hmap := (S.normal x).map_source hxSource
    simpa [S.normal_anchor x] using hmap
  exact hjoint.continuousOn_symmEval.continuousAt
    (hjoint.isOpen_targetLocus.mem_nhds hxTarget)

/-- Endpoint-only source-normal stability.  It asks that small generic normal
vectors at nearby anchors represent endpoints in any prescribed neighborhood
of the center.  No target alignment or successor package occurs here. -/
def GenericSourceNormalEndpointLocalStability
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x : M) (W : Set M), W ∈ 𝓝 x →
    ∃ U : Set M, U ∈ 𝓝 x ∧
      ∃ sourceRadius > (0 : ℝ),
        ∀ y ∈ U, ∀ z : M,
          z ∈ ((genericFamily g).normal y).source →
          ‖(genericFamily g).normal y z‖ < sourceRadius →
            z ∈ W

/-- Zero-section continuity of the inverse generic normal gives the exact
endpoint-local stability contract. -/
theorem genericSourceNormalEndpointLocalStability_of_inverseZeroSectionContinuity
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hinverse : GenericInverseNormalZeroSectionContinuity g) :
    GenericSourceNormalEndpointLocalStability g := by
  intro x W hW
  let S := genericFamily g
  have hxSource : x ∈ (S.normal x).source := S.anchor_mem_source x
  have hsymmZero : S.symmEval (x, (0 : E)) = x := by
    change (S.normal x).symm (0 : E) = x
    rw [← S.normal_anchor x]
    exact (S.normal x).left_inv hxSource
  have hpreimage : S.symmEval ⁻¹' W ∈ 𝓝 (x, (0 : E)) := by
    apply (hinverse x).preimage_mem_nhds
    rw [hsymmZero]
    exact hW
  rcases mem_nhds_prod_iff.mp hpreimage with
    ⟨U, hU, V, hV, hUV⟩
  rcases Metric.mem_nhds_iff.mp hV with
    ⟨sourceRadius, hsourceRadius, hball⟩
  refine ⟨U, hU, sourceRadius, hsourceRadius, ?_⟩
  intro y hy z hzSource hzNorm
  let v : E := S.normal y z
  have hvBall : v ∈ Metric.ball (0 : E) sourceRadius := by
    simpa [Metric.mem_ball, dist_eq_norm, v] using hzNorm
  have hout : S.symmEval (y, v) ∈ W :=
    hUV ⟨hy, hball hvBall⟩
  have hleft : (S.normal y).symm v = z := by
    dsimp only [v]
    exact (S.normal y).left_inv hzSource
  change (S.normal y).symm v ∈ W at hout
  rw [hleft] at hout
  exact hout

/-- Endpoint-local inverse regularity and local alignment bounds give the full
source-normal stability consumed by transferred-package continuation. -/
theorem genericSourceNormalLocalStability_of_endpointLocalStability_and_operatorNormLocalBound
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hendpoint : GenericSourceNormalEndpointLocalStability g)
    (halignment : TangentAlignmentOperatorNormLocalBound g) :
    GenericSourceNormalLocalStability g := by
  intro x W hW targetRadius htargetRadius
  rcases hendpoint x W hW with
    ⟨Uendpoint, hUendpoint, endpointRadius, hendpointRadius,
      hendpointControl⟩
  rcases halignment x with
    ⟨Ualignment, hUalignment, C, hC, hoperator⟩
  let sourceRadius : ℝ := min endpointRadius (targetRadius / C)
  have hsourceRadius : 0 < sourceRadius :=
    lt_min hendpointRadius (div_pos htargetRadius hC)
  refine ⟨Uendpoint ∩ Ualignment,
    inter_mem hUendpoint hUalignment,
    sourceRadius, hsourceRadius, ?_⟩
  intro y hy q L z hzSource hzNorm
  have hzEndpoint : z ∈ W := by
    apply hendpointControl y hy.1 z hzSource
    exact hzNorm.trans_le (by
      dsimp only [sourceRadius]
      exact min_le_left _ _)
  refine ⟨hzEndpoint, ?_⟩
  let v : E := (genericFamily g).normal y z
  let A : E →L[ℝ] E :=
    L.toContinuousLinearEquiv.toContinuousLinearMap
  have hvTarget : ‖v‖ < targetRadius / C := by
    exact hzNorm.trans_le (by
      dsimp only [sourceRadius, v]
      exact min_le_right _ _)
  calc
    ‖alignedGenericSourceNormal g y q L z‖ = ‖A v‖ := rfl
    _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    _ ≤ C * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (hoperator y hy.2 q L) (norm_nonneg v)
    _ < C * (targetRadius / C) :=
      mul_lt_mul_of_pos_left hvTarget hC
    _ = targetRadius :=
      mul_div_cancel₀ targetRadius (ne_of_gt hC)

/-- Zero-section inverse continuity plus local alignment bounds is a strictly
smaller sufficient source contract than `GenericJointRegularity`. -/
theorem genericSourceNormalLocalStability_of_inverseZeroSectionContinuity_and_operatorNormLocalBound
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hinverse : GenericInverseNormalZeroSectionContinuity g)
    (halignment : TangentAlignmentOperatorNormLocalBound g) :
    GenericSourceNormalLocalStability g :=
  genericSourceNormalLocalStability_of_endpointLocalStability_and_operatorNormLocalBound
    (genericSourceNormalEndpointLocalStability_of_inverseZeroSectionContinuity
      hinverse)
    halignment

section Compact

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- A proof-independent positive lower-semicontinuous radius family whose
values are admissible for transferred successor packages. -/
structure LocallyUniformTransferredRadiusEnvelope
    (g : ClosedSmoothRiemannianMetric 3 M) where
  radius : M → RoundSphere3 → ℝ
  positive : ∀ (x : M) (p : RoundSphere3), 0 < radius x p
  lowerSemicontinuous : LowerSemicontinuous
    (fun xp : M × RoundSphere3 ↦ radius xp.1 xp.2)
  admissible : ∀ (x : M) (p : RoundSphere3),
    TransferredNormalRadiusAdmissible g x p (radius x p)

/-- Any positive lower-semicontinuous admissible radius family is locally
stable. -/
theorem LocallyUniformTransferredRadiusEnvelope.toLocalStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (R : LocallyUniformTransferredRadiusEnvelope g) :
    TransferredNormalRadiusLocalStability g := by
  intro xp
  let radius : ℝ := R.radius xp.1 xp.2 / 2
  have hradius : 0 < radius := half_pos (R.positive xp.1 xp.2)
  let U : Set (M × RoundSphere3) :=
    (fun yq : M × RoundSphere3 ↦ R.radius yq.1 yq.2) ⁻¹' Ioi radius
  have hUopen : IsOpen U := R.lowerSemicontinuous.isOpen_preimage radius
  have hxpU : xp ∈ U := by
    change radius < R.radius xp.1 xp.2
    dsimp only [radius]
    linarith [R.positive xp.1 xp.2]
  refine ⟨radius, hradius, ?_⟩
  filter_upwards [hUopen.mem_nhds hxpU] with yq hyq
  exact (R.admissible yq.1 yq.2).mono (le_of_lt hyq)

/-- Local radius stability produces the canonical proof-independent envelope
already defined from the supremum of locally persistent candidates. -/
def canonicalLocallyUniformTransferredRadiusEnvelope
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : TransferredNormalRadiusLocalStability g) :
    LocallyUniformTransferredRadiusEnvelope g where
  radius := canonicalLocallyUniformTransferredAnchorTargetRadius g
  positive := canonicalLocallyUniformTransferredAnchorTargetRadius_pos hstable
  lowerSemicontinuous :=
    canonicalLocallyUniformTransferredAnchorTargetRadius_lowerSemicontinuous g
  admissible :=
    canonicalLocallyUniformTransferredAnchorTargetRadius_admissible hstable

/-- Existence of a positive lower-semicontinuous admissible envelope is
equivalent to the exact radius-local-stability condition. -/
theorem nonempty_locallyUniformTransferredRadiusEnvelope_iff_localStability
    (g : ClosedSmoothRiemannianMetric 3 M) :
    Nonempty (LocallyUniformTransferredRadiusEnvelope g) ↔
      TransferredNormalRadiusLocalStability g := by
  constructor
  · rintro ⟨R⟩
    exact R.toLocalStability
  · intro hstable
    exact ⟨canonicalLocallyUniformTransferredRadiusEnvelope hstable⟩

/-- The exact local normal-control cover and any proof-independent envelope
produce the compared-successor diagonal neighborhood. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_radiusEnvelope
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (R : LocallyUniformTransferredRadiusEnvelope g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_localStability
      hcontrol R.toLocalStability

/-- Canonical-envelope form: no lower-semicontinuity premise on an arbitrary
pointwise curvature radius remains. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_canonicalEnvelope
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (hstable : TransferredNormalRadiusLocalStability g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_radiusEnvelope
      hcontrol (canonicalLocallyUniformTransferredRadiusEnvelope hstable)

/-- Independent source, target, and package-continuation inputs.  This is the
choice-free producer for the canonical locally uniform radius envelope. -/
structure TransferredRadiusContinuationData
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  source : GenericSourceNormalLocalStability g
  target : ∀ p : RoundSphere3,
    (p, (0 : E)) ∈ interior
      CartanCanonicalFamilyLocalDataTransfer.genericCanonicalChartAgreementLocus
  package : TransferredSuccessorPackageDiagonalContinuation g

/-- Continuation data gives the exact local-stability boundary. -/
theorem TransferredRadiusContinuationData.toLocalStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (D : TransferredRadiusContinuationData g) :
    TransferredNormalRadiusLocalStability g :=
  transferredNormalRadiusLocalStability_of_source_target_package_stability
    D.source D.target D.package

/-- Continuation data canonically produces a proof-independent radius
envelope. -/
def TransferredRadiusContinuationData.canonicalEnvelope
    {g : ClosedSmoothRiemannianMetric 3 M}
    (D : TransferredRadiusContinuationData g) :
    LocallyUniformTransferredRadiusEnvelope g :=
  canonicalLocallyUniformTransferredRadiusEnvelope D.toLocalStability

/-- Selected compared theorem from the narrow source/target/package
continuation data and local normal control, with no arbitrary-radius
lower-semicontinuity premise. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_continuationData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (D : TransferredRadiusContinuationData g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_radiusEnvelope
      hcontrol D.canonicalEnvelope

/-- Fully decomposed source form.  The generic inverse is required to be
continuous only on the zero section; the remaining inputs are the alignment
bound, target zero-section chart agreement, and package continuation. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_inverseZeroSectionContinuity_of_operatorNormLocalBound_of_targetPackageContinuation
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (hinverse : GenericInverseNormalZeroSectionContinuity g)
    (halignment : TangentAlignmentOperatorNormLocalBound g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior
        CartanCanonicalFamilyLocalDataTransfer.genericCanonicalChartAgreementLocus)
    (hpackage : TransferredSuccessorPackageDiagonalContinuation g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  let D : TransferredRadiusContinuationData g :=
    { source :=
        genericSourceNormalLocalStability_of_inverseZeroSectionContinuity_and_operatorNormLocalBound
          hinverse halignment
      target := htarget
      package := hpackage }
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_controlledLocalFamilyCover_of_continuationData
      hcontrol D

/-- Curvature/open-locus form.  Curvature is used only to place the diagonal
inside the open conditional package locus; the canonical envelope then removes
all selected-radius lower-semicontinuity assumptions. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_inverseZeroSectionContinuity_of_operatorNormLocalBound_of_targetOpenPackageLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (hinverse : GenericInverseNormalZeroSectionContinuity g)
    (halignment : TangentAlignmentOperatorNormLocalBound g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior
        CartanCanonicalFamilyLocalDataTransfer.genericCanonicalChartAgreementLocus)
    (hopen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_inverseZeroSectionContinuity_of_operatorNormLocalBound_of_targetPackageContinuation
      hcontrol hinverse halignment htarget
  exact transferredSuccessorPackageDiagonalContinuation_of_isOpen hcurv hopen

end Compact

end CartanCanonicalFamilyComparedLocallyUniformRadiusEnvelope
end Poincare
