import Poincare.Global.CartanCanonicalFamilyLocalDataTransfer
import Poincare.Global.CartanSourceExponentialFamily

/-!
# Chart-local uniform canonical Cartan successor data

The canonical-target transfer theorem supplies an ordinary metric radius for
every fixed source-target pair.  This module first converts that radius to a
radius in the generic source normal coordinate.  The resulting statement has
exactly the source-membership and normal-norm hypotheses consumed by
`CartanSourceExponential.localUniformNormalSuccessorData_of_controlsGenericNormal`.

The fixed-pair radii are still selected by classical choice.  We therefore do
not claim that they vary regularly with the anchors.  Under the explicit and
honest premise that the selected source-target normal radius is jointly lower
semicontinuous, compactness of the round-sphere target gives a positive
lower-semicontinuous source-only minorant.  Near any source anchor, half of
that minorant is one normal-coordinate radius working for all nearby source
anchors, all sphere targets, and all tangent alignments.

Finally, a chart-local source family whose endpoint coordinate agrees with the
generic source exponential inherits `LocalUniformNormalSuccessorData` after
restricting its anchor set to that neighborhood.  No joint regularity of the
independently chosen generic exponential is inferred here.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyLocalUniformData

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanSourceExponential

section Curvature

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/--
For fixed source and target anchors, constant curvature gives one positive
generic-source normal-coordinate radius on which canonical-target successor
data exist for every tangent alignment.

This is a consequence of the already proved metric-radius theorem: continuity
of the inverse of the fixed source normal chart sends a sufficiently small
normal ball into that metric ball.  It does not assert any regular dependence
of the radius on either anchor.
-/
theorem exists_normal_canonical_successor_data_radius_all_alignments_fixed_anchors_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
        z ∈ ((genericFamily g).normal x).source →
        ‖(genericFamily g).normal x z‖ < rho →
          Nonempty
            (Data canonicalFamily
              (ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      CartanCanonicalFamilyLocalDataTransfer.exists_metric_canonical_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨epsilon, hepsilon, hmetricData⟩
  let N : OpenPartialHomeomorph M E := (genericFamily g).normal x
  have hxSource : x ∈ N.source := (genericFamily g).anchor_mem_source x
  have hzeroTarget : (0 : E) ∈ N.target := by
    have hmap := N.map_source hxSource
    simpa [N, (genericFamily g).normal_anchor x] using hmap
  have hnormalSymmContinuous : ContinuousAt N.symm (0 : E) :=
    N.continuousAt_symm hzeroTarget
  have hnormalSymmZero : N.symm (0 : E) = x := by
    rw [← (genericFamily g).normal_anchor x]
    exact N.left_inv hxSource
  have hmetricNhds :
      N.symm ⁻¹' Metric.ball x epsilon ∈ 𝓝 (0 : E) := by
    apply hnormalSymmContinuous.preimage_mem_nhds
    rw [hnormalSymmZero]
    exact Metric.ball_mem_nhds x hepsilon
  rcases Metric.mem_nhds_iff.mp hmetricNhds with
    ⟨rho, hrho, hnormalBall⟩
  refine ⟨rho, hrho, ?_⟩
  intro L z hzSource hzNorm
  have hvBall : N z ∈ Metric.ball (0 : E) rho := by
    simpa [Metric.mem_ball, dist_eq_norm, N] using hzNorm
  have hzMetricBall : z ∈ Metric.ball x epsilon := by
    have hsymmBall : N.symm (N z) ∈ Metric.ball x epsilon :=
      hnormalBall hvBall
    simpa [N.left_inv hzSource] using hsymmBall
  apply hmetricData L z
  simpa [Metric.mem_ball] using hzMetricBall

/--
The positive normal-coordinate radius selected from the fixed-anchor theorem.
Its value is uniform in the tangent alignment, but its dependence on the
source and target anchors is not known to be continuous.
-/
def canonicalNormalAnchorTargetRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) : ℝ :=
  Classical.choose
    (exists_normal_canonical_successor_data_radius_all_alignments_fixed_anchors_of_curvature
      g hcurv x p)

/-- Every selected canonical normal-coordinate radius is positive. -/
theorem canonicalNormalAnchorTargetRadius_pos
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    0 < canonicalNormalAnchorTargetRadius hcurv x p :=
  (Classical.choose_spec
    (exists_normal_canonical_successor_data_radius_all_alignments_fixed_anchors_of_curvature
      g hcurv x p)).1

/-- Normal displacement below the selected radius gives canonical data. -/
theorem nonempty_canonical_data_of_normal_lt_canonicalNormalAnchorTargetRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3)
    (L : CartanMap.TangentAlignment g x p) (z : M)
    (hzSource : z ∈ ((genericFamily g).normal x).source)
    (hzNorm : ‖(genericFamily g).normal x z‖ <
      canonicalNormalAnchorTargetRadius hcurv x p) :
    Nonempty (Data canonicalFamily (ChainState.mk x p L) z) :=
  (Classical.choose_spec
    (exists_normal_canonical_successor_data_radius_all_alignments_fixed_anchors_of_curvature
      g hcurv x p)).2 L z hzSource hzNorm

/--
A positive jointly lower-semicontinuous minorant of the selected fixed-pair
normal radii yields a positive lower-semicontinuous source-only radius, uniform
over every sphere target and tangent alignment.
-/
theorem exists_positive_lowerSemicontinuous_canonical_source_normal_radius_of_joint_minorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalNormalAnchorTargetRadius hcurv x p) :
    ∃ sourceRadius : M → ℝ,
      (∀ x : M, 0 < sourceRadius x) ∧
      LowerSemicontinuous sourceRadius ∧
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        z ∈ ((genericFamily g).normal x).source →
        ‖(genericFamily g).normal x z‖ < sourceRadius x →
          Nonempty (Data canonicalFamily (ChainState.mk x p L) z) := by
  rcases
      CartanAtlasRootedPathCurvatureSuccessorRadius.exists_positive_lowerSemicontinuous_source_minorant_of_compact_target
        pairRadius hpositive hlower with
    ⟨sourceRadius, hsourcePositive, hsourceLower, hsourceMinorant⟩
  refine ⟨sourceRadius, hsourcePositive, hsourceLower, ?_⟩
  intro x p L z hzSource hzNorm
  apply
    nonempty_canonical_data_of_normal_lt_canonicalNormalAnchorTargetRadius
      hcurv x p L z hzSource
  exact hzNorm.trans_le ((hsourceMinorant x p).trans (hminorant x p))

/--
If the classically selected normal radius is jointly lower semicontinuous,
compactness of the target produces a source-only radius with no additional
minorant premise.
-/
theorem exists_positive_lowerSemicontinuous_canonical_source_normal_radius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalNormalAnchorTargetRadius hcurv xp.1 xp.2)) :
    ∃ sourceRadius : M → ℝ,
      (∀ x : M, 0 < sourceRadius x) ∧
      LowerSemicontinuous sourceRadius ∧
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        z ∈ ((genericFamily g).normal x).source →
        ‖(genericFamily g).normal x z‖ < sourceRadius x →
          Nonempty (Data canonicalFamily (ChainState.mk x p L) z) := by
  apply
    exists_positive_lowerSemicontinuous_canonical_source_normal_radius_of_joint_minorant
      hcurv (fun x p ↦ canonicalNormalAnchorTargetRadius hcurv x p)
  · exact canonicalNormalAnchorTargetRadius_pos hcurv
  · exact hlower
  · intro x p
    exact le_rfl

/--
The chart-local `hgenericData` furnished by any positive jointly
lower-semicontinuous minorant of the selected fixed-pair radii.  At every
chosen source anchor `x₀`, one open neighborhood and one positive normal
radius work simultaneously for every source anchor in that neighborhood,
every sphere target, and every tangent alignment.

Using a minorant is strictly more flexible than asking the classically
selected radius itself to be lower semicontinuous.
-/
theorem exists_chartLocal_genericNormal_canonicalData_of_joint_minorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalNormalAnchorTargetRadius hcurv x p)
    (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ rho > (0 : ℝ),
        ∀ (x : M), x ∈ U →
          ∀ (p : RoundSphere3)
            (L : CartanMap.TangentAlignment g x p) (z : M),
            z ∈ ((genericFamily g).normal x).source →
            ‖(genericFamily g).normal x z‖ < rho →
              Nonempty (Data canonicalFamily (ChainState.mk x p L) z) := by
  rcases
      exists_positive_lowerSemicontinuous_canonical_source_normal_radius_of_joint_minorant
        hcurv pairRadius hpositive hlower hminorant with
    ⟨sourceRadius, hsourcePositive, hsourceLower, hsourceData⟩
  let rho : ℝ := sourceRadius x₀ / 2
  have hrho : 0 < rho := half_pos (hsourcePositive x₀)
  let U : Set M := sourceRadius ⁻¹' Set.Ioi rho
  have hopenU : IsOpen U := hsourceLower.isOpen_preimage rho
  have hx₀U : x₀ ∈ U := by
    change rho < sourceRadius x₀
    dsimp [rho]
    linarith [hsourcePositive x₀]
  refine ⟨U, hopenU, hx₀U, rho, hrho, ?_⟩
  intro x hx p L z hzSource hzNorm
  apply hsourceData x p L z hzSource
  exact hzNorm.trans hx

/--
Specialization of the chart-local theorem to a lower-semicontinuous selected
normal radius.

The sole regularity premise is explicit because the radius is selected by
classical choice from pointwise existence.
-/
theorem exists_chartLocal_genericNormal_canonicalData_of_lowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalNormalAnchorTargetRadius hcurv xp.1 xp.2))
    (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ rho > (0 : ℝ),
        ∀ (x : M), x ∈ U →
          ∀ (p : RoundSphere3)
            (L : CartanMap.TangentAlignment g x p) (z : M),
            z ∈ ((genericFamily g).normal x).source →
            ‖(genericFamily g).normal x z‖ < rho →
              Nonempty (Data canonicalFamily (ChainState.mk x p L) z) := by
  apply exists_chartLocal_genericNormal_canonicalData_of_joint_minorant
    hcurv (fun x p ↦ canonicalNormalAnchorTargetRadius hcurv x p)
  · exact canonicalNormalAnchorTargetRadius_pos hcurv
  · exact hlower
  · intro x p
    exact le_rfl

end Curvature

/--
Endpoint agreement transfers a chart-local generic-normal Data producer to a
local source family.  This is the direct bridge from the preceding theorem to
`LocalUniformNormalSuccessorData`.
-/
theorem localUniformNormalSuccessorData_of_genericEndpointAgreement
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g)
    {U : Set M} {rho : ℝ}
    (hrho : 0 < rho)
    (hanchors : A.anchors ⊆ U)
    (hendpoint : A.GenericEndpointAgreement rho)
    (hgenericData :
      ∀ (x : M), x ∈ U →
        ∀ (p : RoundSphere3)
          (L : CartanMap.TangentAlignment g x p) (z : M),
          z ∈ ((genericFamily g).normal x).source →
          ‖(genericFamily g).normal x z‖ < rho →
            Nonempty (Data canonicalFamily (ChainState.mk x p L) z)) :
    LocalUniformNormalSuccessorData A canonicalFamily := by
  apply localUniformNormalSuccessorData_of_controlsGenericNormal
    A canonicalFamily hrho hendpoint.controlsGenericNormal
  intro x hx
  exact hgenericData x (hanchors hx)

end CartanCanonicalFamilyLocalUniformData
end Poincare
