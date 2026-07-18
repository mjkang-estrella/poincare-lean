import Poincare.Global.CartanCanonicalFamilyProvenanceRootedAssembly

/-!
# Canonical compared-successor neighborhoods from the generic source family

The existing compared-successor assembly obtains an open local normal family
from a fixed-chart inverse-function construction.  Relating that family back
to the independently chosen generic exponential requires a
`TransitionAgreementPackage` at every anchor.

There is a shorter route when the generic source normal family itself is
jointly regular: restrict that family to the desired open anchor set and use
it directly as a `LocalFamily`.  Its normal coordinate is then definitionally
the generic normal coordinate, so no fixed-chart transition agreement is
needed.

This module records that reduction and two useful curvature specializations.
It does **not** claim that the current independently chosen generic source
family is jointly regular, nor that its pointwise positive curvature radii
vary lower-semicontinuously.  Those are genuine moving-anchor boundaries in
the present API.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyComparedNeighborhood

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanSourceExponential
open CartanCanonicalFamilySuccessorProvenance
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanCanonicalFamilyProvenanceRootedAssembly

/-- Restrict the jointly regular generic source normal family to an arbitrary
open set of anchors.

Unlike the fixed-chart local-family construction, this adapter needs no
coordinate transition: its normal is definitionally the generic normal. -/
def genericLocalFamily
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hjoint : GenericJointRegularity g)
    (U : Set M) (hU : IsOpen U) : LocalFamily g where
  anchors := U
  isOpen_anchors := hU
  sourceLocus :=
    Prod.fst ⁻¹' U ∩ (genericFamily g).sourceLocus
  isOpen_sourceLocus :=
    (hU.preimage continuous_fst).inter hjoint.isOpen_sourceLocus
  sourceLocus_fst := by
    intro q hq
    exact hq.1
  normal := (genericFamily g).eval
  continuousOn_normal :=
    hjoint.continuousOn_eval.mono (fun _q hq ↦ hq.2)
  diagonal_mem := by
    intro x hx
    exact ⟨hx, (genericFamily g).anchor_mem_source x⟩
  normal_diagonal := by
    intro x _hx
    exact (genericFamily g).normal_anchor x

@[simp]
theorem genericLocalFamily_anchors
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hjoint : GenericJointRegularity g)
    (U : Set M) (hU : IsOpen U) :
    (genericLocalFamily g hjoint U hU).anchors = U :=
  rfl

@[simp]
theorem genericLocalFamily_normal
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hjoint : GenericJointRegularity g)
    (U : Set M) (hU : IsOpen U) (x z : M) :
    (genericLocalFamily g hjoint U hU).normal (x, z) =
      (genericFamily g).normal x z :=
  rfl

/-- A source-local package supply becomes a local-uniform provenance producer
without any endpoint or transition comparison, because the local normal is
the generic normal by definition. -/
theorem genericLocalFamily_localUniformTransferredData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : GenericJointRegularity g)
    {U : Set M} (hU : IsOpen U)
    {rho : ℝ} (hrho : 0 < rho)
    (hpackage :
      ∀ (x : M), x ∈ U →
        ∀ (p : RoundSphere3)
          (L : CartanMap.TangentAlignment g x p) (z : M),
          z ∈ ((genericFamily g).normal x).source →
          ‖(genericFamily g).normal x z‖ < rho →
            Nonempty
              (TransferredSuccessorPackage
                (CartanChain.ChainState.mk x p L) z)) :
    LocalUniformNormalTransferredSuccessorData
      (genericLocalFamily g hjoint U hU) := by
  refine ⟨rho, hrho, ?_⟩
  intro x p L z hzSource hzNorm
  exact hpackage x hzSource.1 p L z hzSource.2 hzNorm

section T2

variable [T2Space M]

/-- The sharp direct-local-family consumer.  A jointly regular generic source
family and a source-local supply of uniform transferred packages imply the
full compared-successor diagonal neighborhood.

The package hypothesis is local only in the source anchor, but is uniform in
the sphere target and the dependent tangent alignment. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_localPackageCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : GenericJointRegularity g)
    (hcover : ∀ x₀ : M,
      ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
        ∃ rho > (0 : ℝ),
          ∀ (x : M), x ∈ U →
            ∀ (p : RoundSphere3)
              (L : CartanMap.TangentAlignment g x p) (z : M),
              z ∈ ((genericFamily g).normal x).source →
              ‖(genericFamily g).normal x z‖ < rho →
                Nonempty
                  (TransferredSuccessorPackage
                    (CartanChain.ChainState.mk x p L) z)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply comparedSuccessorLocus_mem_nhdsSet_of_localCover
  intro x₀
  rcases hcover x₀ with
    ⟨U, hU, hx₀U, rho, hrho, hpackage⟩
  let A : LocalFamily g := genericLocalFamily g hjoint U hU
  refine ⟨A, ?_, ?_⟩
  · exact hx₀U
  · exact genericLocalFamily_localUniformTransferredData
      hjoint hU hrho hpackage

section Compact

variable [CompactSpace M] [ConnectedSpace M]

/-- Joint regularity of the generic source family removes every fixed-chart
`TransitionAgreementPackage` from the local-stability route. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_localStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : GenericJointRegularity g)
    (hstable : TransferredNormalRadiusLocalStability g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_localPackageCover
      hjoint
  intro x₀
  exact exists_chartLocal_genericNormal_transferredPackage_of_localStability
    g hstable x₀

/-- A positive lower-semicontinuous family of admissible provenance radii,
together with generic-source joint regularity, gives the compared neighborhood
directly.  No fixed-chart transition package remains. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_admissibleRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : GenericJointRegularity g)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hadmissible : ∀ (x : M) (p : RoundSphere3),
      TransferredNormalRadiusAdmissible g x p (pairRadius x p)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_localPackageCover
      hjoint
  intro x₀
  exact exists_chartLocal_genericNormal_transferredPackage_of_admissible
    pairRadius hpositive hlower hadmissible x₀

/-- Unit constant curvature supplies pointwise admissible radii.  Thus a
positive lower-semicontinuous minorant of those automatic radii, plus joint
regularity of the generic source family, is sufficient for the complete
compared-successor neighborhood. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_genericJointRegularity_of_jointMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hjoint : GenericJointRegularity g)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalTransferredAnchorTargetRadius hcurv x p) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_localPackageCover
      hjoint
  intro x₀
  exact exists_chartLocal_genericNormal_transferredPackage_of_joint_minorant
    hcurv pairRadius hpositive hlower hminorant x₀

/-- Compact specialization using the automatically selected pointwise
curvature radius itself.  Its positivity and admissibility are automatic;
only its genuinely moving-parameter lower semicontinuity and generic-source
joint regularity remain. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_genericJointRegularity_of_canonicalRadiusLowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hjoint : GenericJointRegularity g)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalTransferredAnchorTargetRadius hcurv xp.1 xp.2)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_genericJointRegularity_of_jointMinorant
      hcurv hjoint
      (fun x p ↦ canonicalTransferredAnchorTargetRadius hcurv x p)
      (canonicalTransferredAnchorTargetRadius_pos hcurv)
      hlower
      (fun _x _p ↦ le_rfl)

/-- Decompose the radius-local-stability premise into independent moving
source, alignment, target-chart, and transferred-package continuation facts.
This corollary makes clear which parts are not consequences of pointwise
constant-curvature existence alone. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_sourceTargetPackageStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : GenericJointRegularity g)
    (halignment : TangentAlignmentOperatorNormLocalBound g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior
        CartanCanonicalFamilyLocalDataTransfer.genericCanonicalChartAgreementLocus)
    (hpackage : TransferredSuccessorPackageDiagonalContinuation g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  have hsource : GenericSourceNormalLocalStability g :=
    genericSourceNormalLocalStability_of_jointRegularity_and_operatorNormLocalBound
      hjoint halignment
  have hstable : TransferredNormalRadiusLocalStability g :=
    transferredNormalRadiusLocalStability_of_source_target_package_stability
      hsource htarget hpackage
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_localStability
      hjoint hstable

/-- Openness form of the preceding decomposition.  Curvature is used exactly
once: to place the diagonal in the conditional transferred-package locus. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_curvature_of_genericJointRegularity_of_openPackageLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hjoint : GenericJointRegularity g)
    (halignment : TangentAlignmentOperatorNormLocalBound g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior
        CartanCanonicalFamilyLocalDataTransfer.genericCanonicalChartAgreementLocus)
    (hopen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_genericJointRegularity_of_sourceTargetPackageStability
      hjoint halignment htarget
  exact transferredSuccessorPackageDiagonalContinuation_of_isOpen hcurv hopen

end Compact

end T2

end CartanCanonicalFamilyComparedNeighborhood
end Poincare
