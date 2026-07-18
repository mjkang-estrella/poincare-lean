import Poincare.Global.CartanCanonicalFamilySuccessorProvenance
import Poincare.Global.CartanCanonicalFamilyLocalUniformData
import Poincare.Global.CartanSourceExponentialLocalFamilyTransitionAgreement
import Poincare.Global.GeodesicReanchorClose

/-!
# Local-uniform canonical successor data with retained generic provenance

This is the provenance-preserving counterpart of
`CartanCanonicalFamilyLocalUniformData`.  Its selected radii produce not only
canonical `Data`, but the original generic datum and exact dependent successor
comparison packaged by `TransferredSuccessorPackage`.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyProvenanceLocalUniformData

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
open CartanCanonicalFamilyLocalDataTransfer

/-- Uniform provenance-retaining successor production on one chart-local
source family. -/
def LocalUniformNormalTransferredSuccessorData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) : Prop :=
  ∃ rho > (0 : ℝ),
    ∀ (x : M) (p : RoundSphere3)
      (L : CartanMap.TangentAlignment g x p) (z : M),
      (x, z) ∈ A.sourceLocus →
      ‖A.normal (x, z)‖ < rho →
        Nonempty
          (TransferredSuccessorPackage
            (CartanChain.ChainState.mk x p L) z)

section Curvature

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Convert the provenance-retaining metric radius to a generic normal
coordinate radius. -/
theorem exists_normal_transferredSuccessorPackage_radius_all_alignments_fixed_anchors_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
        z ∈ ((genericFamily g).normal x).source →
        ‖(genericFamily g).normal x z‖ < rho →
          Nonempty
            (TransferredSuccessorPackage
              (CartanChain.ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_metric_transferredSuccessorPackage_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨epsilon, hepsilon, hmetricPackage⟩
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
      N.symm ⁻¹' Metric.ball x epsilon ∈ nhds (0 : E) := by
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
  apply hmetricPackage L z
  simpa [Metric.mem_ball] using hzMetricBall

/-- The selected fixed-pair normal radius for provenance-retaining transfer. -/
def canonicalTransferredAnchorTargetRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) : ℝ :=
  Classical.choose
    (exists_normal_transferredSuccessorPackage_radius_all_alignments_fixed_anchors_of_curvature
      g hcurv x p)

theorem canonicalTransferredAnchorTargetRadius_pos
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    0 < canonicalTransferredAnchorTargetRadius hcurv x p :=
  (Classical.choose_spec
    (exists_normal_transferredSuccessorPackage_radius_all_alignments_fixed_anchors_of_curvature
      g hcurv x p)).1

theorem nonempty_transferredPackage_of_normal_lt_selectedRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3)
    (L : CartanMap.TangentAlignment g x p) (z : M)
    (hzSource : z ∈ ((genericFamily g).normal x).source)
    (hzNorm : ‖(genericFamily g).normal x z‖ <
      canonicalTransferredAnchorTargetRadius hcurv x p) :
    Nonempty
      (TransferredSuccessorPackage
        (CartanChain.ChainState.mk x p L) z) :=
  (Classical.choose_spec
    (exists_normal_transferredSuccessorPackage_radius_all_alignments_fixed_anchors_of_curvature
      g hcurv x p)).2 L z hzSource hzNorm

/-- A normal-coordinate radius is admissible when it produces a retained
generic/canonical successor package for every alignment and every endpoint in
the corresponding generic normal ball. -/
def TransferredNormalRadiusAdmissible
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) (radius : ℝ) : Prop :=
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
    z ∈ ((genericFamily g).normal x).source →
    ‖(genericFamily g).normal x z‖ < radius →
      Nonempty
        (TransferredSuccessorPackage
          (CartanChain.ChainState.mk x p L) z)

/-- Admissibility is downward closed in the radius. -/
theorem TransferredNormalRadiusAdmissible.mono
    {g : ClosedSmoothRiemannianMetric 3 M}
    {x : M} {p : RoundSphere3} {r s : ℝ}
    (h : TransferredNormalRadiusAdmissible g x p r)
    (hsr : s ≤ r) :
    TransferredNormalRadiusAdmissible g x p s := by
  intro L z hzSource hzNorm
  exact h L z hzSource (hzNorm.trans_le hsr)

/-- Curvature proves positive admissible radii pointwise.  This theorem does
not promote those independently selected witnesses to neighborhoods of the
source-target parameter. -/
theorem exists_pointwise_transferredNormalRadius_of_curvature
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    ∃ radius > (0 : ℝ),
      TransferredNormalRadiusAdmissible g x p radius := by
  refine ⟨canonicalTransferredAnchorTargetRadius hcurv x p,
    canonicalTransferredAnchorTargetRadius_pos hcurv x p, ?_⟩
  exact nonempty_transferredPackage_of_normal_lt_selectedRadius hcurv x p

/-- A radius is locally uniform at `(x,p)` when the same radius is admissible
at every source-target pair in a neighborhood of `(x,p)`. -/
def LocallyUniformTransferredNormalRadiusAt
    (g : ClosedSmoothRiemannianMetric 3 M)
    (xp : M × RoundSphere3) (radius : ℝ) : Prop :=
  ∀ᶠ yq in 𝓝 xp,
    TransferredNormalRadiusAdmissible g yq.1 yq.2 radius

/-- The exact missing parameter-stability statement: every source-target pair
has one positive provenance radius that remains admissible on a neighborhood
of that pair.  Pointwise curvature existence alone does not imply this. -/
def TransferredNormalRadiusLocalStability
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ xp : M × RoundSphere3,
    ∃ radius > (0 : ℝ),
      LocallyUniformTransferredNormalRadiusAt g xp radius

/-- The target vector obtained by applying a Cartan alignment to the current
generic source normal coordinate.

Naming this expression makes the two moving-coordinate boundaries explicit:
the source normal is chosen at `x`, while the alignment has dependent target
index `p`.
-/
def alignedGenericSourceNormal
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3)
    (L : CartanMap.TangentAlignment g x p) (z : M) : E :=
  L ((CartanSourceExponential.genericFamily g).normal x z)

/-- Exact local stability required from the independently chosen generic
source normal family.

Given an endpoint neighborhood `W` of `x` and a target-vector tolerance, one
source-normal radius works at all nearby source anchors, for every sphere
target and every dependent tangent alignment.  It controls both the physical
endpoint and the aligned target vector.  This statement contains no successor
data and is therefore strictly a source-coordinate regularity hypothesis,
not a renamed transferred-radius hypothesis.
-/
def GenericSourceNormalLocalStability
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x : M) (W : Set M), W ∈ 𝓝 x →
    ∀ targetRadius > (0 : ℝ),
      ∃ U : Set M, U ∈ 𝓝 x ∧
        ∃ sourceRadius > (0 : ℝ),
          ∀ y ∈ U, ∀ (q : RoundSphere3)
            (L : CartanMap.TangentAlignment g y q) (z : M),
            z ∈ ((CartanSourceExponential.genericFamily g).normal y).source →
            ‖(CartanSourceExponential.genericFamily g).normal y z‖ <
                sourceRadius →
              z ∈ W ∧
                ‖alignedGenericSourceNormal g y q L z‖ < targetRadius

/-- Local boundedness of the Euclidean operator norms of all dependent Cartan
alignments as the source anchor moves.

For each *fixed* source anchor, compactness of the round-sphere target and the
metric-isometry equation already give such a bound; see
`exists_pointwise_tangentAlignmentOperatorNorm_bound`.  The additional content
here is precisely that one bound persists on a source-anchor neighborhood.
This is an algebraic chart-metric regularity statement and contains neither
source endpoints nor successor packages.
-/
def TangentAlignmentOperatorNormLocalBound
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x : M,
    ∃ U : Set M, U ∈ 𝓝 x ∧
      ∃ C > (0 : ℝ),
        ∀ y ∈ U, ∀ (q : RoundSphere3)
          (L : CartanMap.TangentAlignment g y q),
          ‖L.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ C

/-- The derivative that converts a vector in the preferred chart at `y` to
the coordinates of one frozen chart centered at `x₀`.

This is the inverse direction to
`CartanSourceExponentialLocalFamilyTransport.fixedToAnchorVelocity`: it is the
direction needed to read the preferred-anchor metric through a stationary
fixed chart.
-/
def preferredToFixedTransitionDerivative (x₀ y : M) : E →L[ℝ] E :=
  GeodesicTransport.chartTransitionDeriv y x₀
    (extChartAt I y y)

/-- At the frozen-chart center, preferred-to-fixed velocity transport is the
identity. -/
@[simp]
theorem preferredToFixedTransitionDerivative_self (x : M) :
    preferredToFixedTransitionDerivative x x =
      ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  exact
    CartanSourceExponentialLocalFamilyTransport.fixedToAnchorVelocity_self
      x v

/-- Exact transition-derivative persistence left by the stationary local
chart construction.

For each frozen center, the preferred-to-fixed transition derivatives have
locally bounded Euclidean operator norm.  Pointwise this is automatic (the
central derivative is the identity), but the current `chartAt` structure does
not impose continuity of its preferred-chart choice in `y`.
-/
def PreferredToFixedTransitionDerivativeLocalBound : Prop :=
  ∀ x₀ : M,
    ∃ U : Set M, U ∈ 𝓝 x₀ ∧
      ∃ K > (0 : ℝ),
        ∀ y ∈ U,
          ‖preferredToFixedTransitionDerivative x₀ y‖ ≤ K

/-- The smallest operator-valued continuity statement that discharges the
preferred-to-fixed transition bound.

Existing chart-transition `ContDiff` theorems keep both chart anchors fixed
and vary only the coordinate argument.  This statement instead varies the
preferred-chart anchor itself, exactly where `ChartedSpace.chartAt` has no
built-in regularity requirement.
-/
def PreferredToFixedTransitionDerivativeContinuousAtCenters : Prop :=
  ∀ x₀ : M,
    ContinuousAt
      (fun y : M ↦ preferredToFixedTransitionDerivative x₀ y) x₀

omit [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Operator-valued continuity at every frozen center gives the required
local operator-norm bound by continuity of the norm. -/
theorem preferredToFixedTransitionDerivativeLocalBound_of_continuousAtCenters
    (hcontinuous :
      PreferredToFixedTransitionDerivativeContinuousAtCenters (M := M)) :
    PreferredToFixedTransitionDerivativeLocalBound (M := M) := by
  intro x₀
  let D : M → E →L[ℝ] E :=
    fun y ↦ preferredToFixedTransitionDerivative x₀ y
  let K : ℝ := ‖D x₀‖ + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hDcontinuous : ContinuousAt D x₀ := by
    simpa only [D] using hcontinuous x₀
  have hnormContinuous : ContinuousAt (fun y : M ↦ ‖D y‖) x₀ :=
    (@continuous_norm (E →L[ℝ] E) _).continuousAt.comp hDcontinuous
  let U : Set M := {y | ‖D y‖ < K}
  have hU : U ∈ 𝓝 x₀ := by
    change (fun y : M ↦ ‖D y‖) ⁻¹' Iio K ∈ 𝓝 x₀
    apply hnormContinuous.preimage_mem_nhds
    exact Iio_mem_nhds (by dsimp only [K]; linarith)
  refine ⟨U, hU, K, hK, ?_⟩
  intro y hy
  exact le_of_lt hy

/-- The source chart metric has one Euclidean quadratic upper bound on a
neighborhood of every moving preferred-chart anchor.

This is the exact chart-level persistence needed to control alignment
operator norms.  It is weaker than continuity of
`x ↦ CartanMap.sourceAnchorChartMetric g x`: only the diagonal quadratic
forms need a locally uniform upper bound.  The present `chartAt` API proves
smoothness inside each fixed chart, but does not by itself state this
regularity for the independently selected preferred chart as its anchor
moves.
-/
def SourceAnchorChartMetricLocalEuclideanUpperBound
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x : M,
    ∃ U : Set M, U ∈ 𝓝 x ∧
      ∃ C > (0 : ℝ),
        ∀ y ∈ U, ∀ v : E,
          CartanMap.sourceAnchorChartMetric g y v v ≤ (C * ‖v‖) ^ 2

/-- In one genuinely frozen chart, the bilinear-form-valued metric is
continuous at the center coordinate.

This is the regularity supplied by the stationary local-chart construction;
unlike continuity of `y ↦ sourceAnchorChartMetric g y`, the chart itself does
not move in this statement.
-/
theorem continuousAt_fixedChartMetric_center
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ContinuousAt
      (CovariantDerivative.chartMetric g.inner x₀)
      (extChartAt I x₀ x₀) := by
  have hmetricContDiff : ContDiffAt ℝ 0
      (CovariantDerivative.chartMetric g.inner x₀)
      (extChartAt I x₀ x₀) := by
    apply Poincare.contDiffAt_clm_of_apply
    intro v
    apply Poincare.contDiffAt_clm_of_apply
    intro w
    have hscalar :=
      CovariantDerivative.contMDiffOn_chartMetric_pairing
        g.inner x₀ (m := 0) (by simp)
        (g.contMDiff_inner.of_le (by simp)) v w
        (extChartAt I x₀ x₀)
        (mem_extChartAt_target x₀)
    exact contMDiffAt_iff_contDiffAt.mp
      (hscalar.contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds
          (mem_extChartAt_target x₀)))
  exact hmetricContDiff.continuousAt

/-- A locally bounded preferred-to-fixed transition derivative transports the
automatic fixed-chart metric bound back to the moving preferred chart.

The covariance identity is applied to the transition from the preferred
chart at `y` into the chart frozen at `x₀`.  Fixed-chart smoothness controls
the metric factor, while the transition hypothesis controls the two vector
slots.  Thus no continuity of the arbitrary preferred-chart selector is
silently assumed.
-/
theorem sourceAnchorChartMetricLocalEuclideanUpperBound_of_preferredToFixedTransitionDerivativeLocalBound
    {g : ClosedSmoothRiemannianMetric 3 M}
    (htransition : PreferredToFixedTransitionDerivativeLocalBound (M := M)) :
    SourceAnchorChartMetricLocalEuclideanUpperBound g := by
  intro x₀
  let G : E → E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric g.inner x₀
  let z₀ : E := extChartAt I x₀ x₀
  let B : ℝ := ‖G z₀‖ + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hGcontinuous : ContinuousAt G z₀ := by
    simpa only [G, z₀] using continuousAt_fixedChartMetric_center g x₀
  have hGnormContinuous : ContinuousAt (fun z : E => ‖G z‖) z₀ :=
    (@continuous_norm (E →L[ℝ] E →L[ℝ] ℝ) _).continuousAt.comp
      hGcontinuous
  have hmetricCoordinateNhds :
      {z : E | ‖G z‖ < B} ∈ 𝓝 z₀ := by
    change (fun z : E => ‖G z‖) ⁻¹' Iio B ∈ 𝓝 z₀
    apply hGnormContinuous.preimage_mem_nhds
    exact Iio_mem_nhds (by dsimp only [B]; linarith)
  have hchartContinuous : ContinuousAt (extChartAt I x₀ : M → E) x₀ :=
    continuousAt_extChartAt x₀
  have hmetricAnchorNhds :
      (extChartAt I x₀) ⁻¹' {z : E | ‖G z‖ < B} ∈ 𝓝 x₀ := by
    apply hchartContinuous.preimage_mem_nhds
    simpa only [z₀] using hmetricCoordinateNhds
  rcases htransition x₀ with
    ⟨Utransition, hUtransition, K, hK, htransitionBound⟩
  let U : Set M :=
    Utransition ∩
      (extChartAt I x₀).source ∩
        ((extChartAt I x₀) ⁻¹' {z : E | ‖G z‖ < B})
  have hU : U ∈ 𝓝 x₀ := by
    exact inter_mem
      (inter_mem hUtransition
        ((isOpen_extChartAt_source x₀).mem_nhds
          (mem_extChartAt_source x₀)))
      hmetricAnchorNhds
  let C : ℝ := B * K
  have hC : 0 < C := mul_pos hB hK
  refine ⟨U, hU, C, hC, ?_⟩
  intro y hy v
  have hyTransition : y ∈ Utransition := hy.1.1
  have hyFixedSource : y ∈ (extChartAt I x₀).source := hy.1.2
  have hyMetricBound : ‖G (extChartAt I x₀ y)‖ < B := hy.2
  let D : E →L[ℝ] E := preferredToFixedTransitionDerivative x₀ y
  have hDnorm : ‖D‖ ≤ K :=
    htransitionBound y hyTransition
  have hDv : ‖D v‖ ≤ K * ‖v‖ := by
    exact (D.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hDnorm (norm_nonneg v))
  have hyPreferredTarget :
      extChartAt I y y ∈ (extChartAt I y).target :=
    (extChartAt I y).map_source (mem_extChartAt_source y)
  have htransitionPoint :
      GeodesicTransport.chartTransition y x₀ (extChartAt I y y) =
        extChartAt I x₀ y := by
    simp [GeodesicTransport.chartTransition]
  have hyOverlap :
      (extChartAt I y).symm (extChartAt I y y) ∈
        (extChartAt I x₀).source := by
    rw [(extChartAt I y).left_inv (mem_extChartAt_source y)]
    exact hyFixedSource
  have hmetricCovariance :=
    GeodesicTransport.chartMetric_chartTransitionDeriv
      g y x₀ hyPreferredTarget hyOverlap v v
  have hpreferredMetric :
      CartanMap.sourceAnchorChartMetric g y v v =
        G (extChartAt I x₀ y) (D v) (D v) := by
    rw [CartanMap.sourceAnchorChartMetric]
    simpa only [G, D, preferredToFixedTransitionDerivative,
      htransitionPoint] using hmetricCovariance.symm
  rw [hpreferredMetric]
  calc
    G (extChartAt I x₀ y) (D v) (D v) ≤
        ‖G (extChartAt I x₀ y) (D v) (D v)‖ :=
      Real.le_norm_self _
    _ ≤ ‖G (extChartAt I x₀ y) (D v)‖ * ‖D v‖ :=
      (G (extChartAt I x₀ y) (D v)).le_opNorm (D v)
    _ ≤ (‖G (extChartAt I x₀ y)‖ * ‖D v‖) * ‖D v‖ :=
      mul_le_mul_of_nonneg_right
        ((G (extChartAt I x₀ y)).le_opNorm (D v))
        (norm_nonneg (D v))
    _ ≤ (B * ‖D v‖) * ‖D v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hyMetricBound.le (norm_nonneg (D v)))
        (norm_nonneg (D v))
    _ ≤ (B * (K * ‖v‖)) * (K * ‖v‖) := by
      gcongr
    _ ≤ (C * ‖v‖) ^ 2 := by
      have hBone : 1 ≤ B := by
        dsimp only [B]
        linarith [norm_nonneg (G z₀)]
      have hKv : 0 ≤ K * ‖v‖ :=
        mul_nonneg hK.le (norm_nonneg v)
      have hKvBound : K * ‖v‖ ≤ B * (K * ‖v‖) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hBone hKv
      calc
        (B * (K * ‖v‖)) * (K * ‖v‖) ≤
            (B * (K * ‖v‖)) * (B * (K * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hKvBound
            (mul_nonneg hB.le hKv)
        _ = (C * ‖v‖) ^ 2 := by
          dsimp only [C]
          ring

/-- Continuity of the preferred-anchor chart metric as a continuous bilinear
form is sufficient for its local Euclidean quadratic upper bound.

This theorem records exactly how a future preferred-chart regularity result
would discharge the remaining algebraic premise.  Fixed-chart smoothness is
not used here: the hypothesis concerns the genuinely moving function
`y ↦ sourceAnchorChartMetric g y`.
-/
theorem sourceAnchorChartMetricLocalEuclideanUpperBound_of_continuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontinuous : Continuous
      (fun y : M ↦ CartanMap.sourceAnchorChartMetric g y)) :
    SourceAnchorChartMetricLocalEuclideanUpperBound g := by
  intro x
  let G : M → E →L[ℝ] E →L[ℝ] ℝ :=
    fun y ↦ CartanMap.sourceAnchorChartMetric g y
  let C : ℝ := ‖G x‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let U : Set M := {y | ‖G y‖ < C ^ 2}
  have hxBound : ‖G x‖ < C ^ 2 := by
    dsimp only [C]
    nlinarith [norm_nonneg (G x)]
  have hGcontinuous : Continuous G := by
    simpa only [G] using hcontinuous
  have hGnormContinuous : Continuous (fun y : M ↦ ‖G y‖) :=
    (@continuous_norm (E →L[ℝ] E →L[ℝ] ℝ) _).comp hGcontinuous
  have hUOpen : IsOpen U := by
    exact isOpen_lt hGnormContinuous continuous_const
  have hU : U ∈ 𝓝 x :=
    hUOpen.mem_nhds hxBound
  refine ⟨U, hU, C, hC, ?_⟩
  intro y hy v
  have hGnorm : ‖G y‖ ≤ C ^ 2 :=
    le_of_lt hy
  calc
    CartanMap.sourceAnchorChartMetric g y v v = G y v v := rfl
    _ ≤ ‖G y v v‖ := Real.le_norm_self _
    _ ≤ ‖G y v‖ * ‖v‖ := (G y v).le_opNorm v
    _ ≤ (‖G y‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((G y).le_opNorm v) (norm_nonneg v)
    _ ≤ (C ^ 2 * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hGnorm (norm_nonneg v))
        (norm_nonneg v)
    _ = (C * ‖v‖) ^ 2 := by ring

/-- A locally uniform Euclidean upper bound for the moving source chart
metric controls every Cartan alignment operator.

The target chart metric is exactly the ambient Euclidean inner product.  The
alignment isometry equation therefore identifies `‖L v‖²` with the source
quadratic form, so the asserted quadratic upper bound is precisely the
operator-norm estimate.
-/
theorem tangentAlignmentOperatorNormLocalBound_of_sourceAnchorChartMetricLocalEuclideanUpperBound
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hmetric : SourceAnchorChartMetricLocalEuclideanUpperBound g) :
    TangentAlignmentOperatorNormLocalBound g := by
  intro x
  rcases hmetric x with ⟨U, hU, C, hC, hquadratic⟩
  refine ⟨U, hU, C, hC, ?_⟩
  intro y hy q L
  let A : E →L[ℝ] E :=
    L.toContinuousLinearEquiv.toContinuousLinearMap
  apply ContinuousLinearMap.opNorm_le_bound A hC.le
  intro v
  have hsquare : ‖A v‖ ^ 2 =
      CartanMap.sourceAnchorChartMetric g y v v := by
    calc
      ‖A v‖ ^ 2 = inner ℝ (A v) (A v) :=
        (real_inner_self_eq_norm_sq (A v)).symm
      _ = CartanMap.targetAnchorChartMetric q (L v) (L v) := by
        rw [RoundSphereTargetAnchorUniformity.targetAnchorChartMetric_eq_innerSL]
        rfl
      _ = CartanMap.sourceAnchorChartMetric g y v v :=
        L.map_app v v
  apply (sq_le_sq₀ (norm_nonneg (A v))
    (mul_nonneg hC.le (norm_nonneg v))).mp
  rw [hsquare]
  exact hquadratic y hy v

/-- The currently proved compact target-anchor estimate supplies the
pointwise part of `TangentAlignmentOperatorNormLocalBound` at every source
anchor.  What remains is local boundedness as that source anchor moves.
-/
theorem exists_pointwise_tangentAlignmentOperatorNorm_bound
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    ∃ C > (0 : ℝ), ∀ (q : RoundSphere3)
      (L : CartanMap.TangentAlignment g x q),
      ‖L.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ C :=
  RoundSphereTargetAnchorUniformity.exists_pos_uniform_tangentAlignment_operatorNorm_bound_all_targets
    g x

/-- Joint regularity of the varying generic inverse normal chart gives the
endpoint half of source-normal local stability.

The proof uses inverse evaluation near `(x, 0)`: a product neighborhood in
anchor-vector space is pulled back into the prescribed endpoint neighborhood.
No tangent alignment enters this statement.
-/
theorem exists_genericSourceNormal_endpoint_control_of_jointRegularity
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : CartanSourceExponential.GenericJointRegularity g)
    (x : M) (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ U : Set M, U ∈ 𝓝 x ∧
      ∃ sourceRadius > (0 : ℝ),
        ∀ y ∈ U, ∀ z : M,
          z ∈ ((CartanSourceExponential.genericFamily g).normal y).source →
          ‖(CartanSourceExponential.genericFamily g).normal y z‖ <
              sourceRadius →
            z ∈ W := by
  let S := CartanSourceExponential.genericFamily g
  have hxSource : x ∈ (S.normal x).source :=
    S.anchor_mem_source x
  have hxTarget : (x, (0 : E)) ∈ S.targetLocus := by
    change (0 : E) ∈ (S.normal x).target
    have hmap := (S.normal x).map_source hxSource
    simpa [S.normal_anchor x] using hmap
  have hsymmContinuous : ContinuousAt S.symmEval (x, (0 : E)) :=
    hjoint.continuousOn_symmEval.continuousAt
      (hjoint.isOpen_targetLocus.mem_nhds hxTarget)
  have hsymmZero : S.symmEval (x, (0 : E)) = x := by
    change (S.normal x).symm (0 : E) = x
    rw [← S.normal_anchor x]
    exact (S.normal x).left_inv hxSource
  have hpreimage : S.symmEval ⁻¹' W ∈ 𝓝 (x, (0 : E)) := by
    apply hsymmContinuous.preimage_mem_nhds
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
  have hpair : (y, v) ∈ U ×ˢ V :=
    ⟨hy, hball hvBall⟩
  have hout : S.symmEval (y, v) ∈ W :=
    hUV hpair
  have hleft : (S.normal y).symm v = z := by
    dsimp only [v]
    exact (S.normal y).left_inv hzSource
  change (S.normal y).symm v ∈ W at hout
  rw [hleft] at hout
  exact hout

/-- Joint regularity of the generic source inverse, together with local
boundedness of alignment operator norms, implies the full source-coordinate
stability needed by provenance transfer.

This separates the topological endpoint issue from the chart-metric issue:
`GenericJointRegularity` controls the inverse normal endpoint, while
`TangentAlignmentOperatorNormLocalBound` turns a small source vector into a
uniformly small aligned target vector.
-/
theorem genericSourceNormalLocalStability_of_jointRegularity_and_operatorNormLocalBound
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : CartanSourceExponential.GenericJointRegularity g)
    (halignment : TangentAlignmentOperatorNormLocalBound g) :
    GenericSourceNormalLocalStability g := by
  intro x W hW targetRadius htargetRadius
  rcases
      exists_genericSourceNormal_endpoint_control_of_jointRegularity
        hjoint x W hW with
    ⟨Uendpoint, hUendpoint, endpointRadius, hendpointRadius, hendpoint⟩
  rcases halignment x with
    ⟨Ualignment, hUalignment, C, hC, hoperator⟩
  let sourceRadius : ℝ := min endpointRadius (targetRadius / C)
  have hsourceRadius : 0 < sourceRadius := by
    dsimp only [sourceRadius]
    exact lt_min hendpointRadius (div_pos htargetRadius hC)
  refine ⟨Uendpoint ∩ Ualignment,
    inter_mem hUendpoint hUalignment,
    sourceRadius, hsourceRadius, ?_⟩
  intro y hy q L z hzSource hzNorm
  have hzEndpoint : z ∈ W := by
    apply hendpoint y hy.1 z hzSource
    exact hzNorm.trans_le (by
      dsimp only [sourceRadius]
      exact min_le_left _ _)
  refine ⟨hzEndpoint, ?_⟩
  let v : E :=
    (CartanSourceExponential.genericFamily g).normal y z
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

/-- Stationary-chart form of the source stability bridge.

Joint inverse regularity controls physical endpoints.  Fixed-chart metric
smoothness and a locally bounded preferred-to-fixed transition derivative
control every dependent tangent alignment.  These are the two independent
source-anchor facts remaining after the local selector construction.
-/
theorem genericSourceNormalLocalStability_of_jointRegularity_and_preferredToFixedTransitionDerivativeLocalBound
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hjoint : CartanSourceExponential.GenericJointRegularity g)
    (htransition : PreferredToFixedTransitionDerivativeLocalBound (M := M)) :
    GenericSourceNormalLocalStability g := by
  apply
    genericSourceNormalLocalStability_of_jointRegularity_and_operatorNormLocalBound
      hjoint
  apply
    tangentAlignmentOperatorNormLocalBound_of_sourceAnchorChartMetricLocalEuclideanUpperBound
  exact
    sourceAnchorChartMetricLocalEuclideanUpperBound_of_preferredToFixedTransitionDerivativeLocalBound
      htransition

/-- Joint parameter locus on which the target-side inputs to provenance
transfer suffice to continue a `TransferredSuccessorPackage`.

The dependent alignment quantifier is internal to the locus.  Membership only
assumes the three explicit transfer inputs at the actual aligned generic
normal vector: source-normal membership, canonical target-source membership,
and the generic/canonical target-chart germ equality.  It then asks for the
proof-bearing transferred package itself.
-/
def TransferredSuccessorPackageContinuationLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    Set ((M × RoundSphere3) × M) :=
  {param | ∀ L : CartanMap.TangentAlignment g param.1.1 param.1.2,
    param.2 ∈
        ((CartanSourceExponential.genericFamily g).normal param.1.1).source →
    alignedGenericSourceNormal g param.1.1 param.1.2 L param.2 ∈
        (canonicalFamily.chart param.1.2).source →
    (CartanTargetExponential.genericFamily.chart param.1.2 : E → E)
        =ᶠ[𝓝 (alignedGenericSourceNormal
          g param.1.1 param.1.2 L param.2)]
          (canonicalFamily.chart param.1.2 : E → E) →
      Nonempty
        (TransferredSuccessorPackage
          (CartanChain.ChainState.mk param.1.1 param.1.2 L) param.2)}

/-- The semantically exact continuation hypothesis for dependent transferred
packages: the conditional package locus is a neighborhood of the complete
source-target-endpoint diagonal.

Unlike `TransferredNormalRadiusLocalStability`, this statement contains no
normal radius.  It is an ordinary joint neighborhood assertion in the three
geometric point parameters, with the dependent alignment quantifier kept
inside the locus.
-/
def TransferredSuccessorPackageDiagonalContinuation
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  TransferredSuccessorPackageContinuationLocus g ∈
    𝓝ˢ (CartanTargetExponential.successorParameterDiagonal (M := M))

/-- Curvature puts the complete parameter diagonal in the conditional
transferred-package continuation locus. -/
theorem successorParameterDiagonal_subset_transferredSuccessorPackageContinuationLocus_of_curvature
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    CartanTargetExponential.successorParameterDiagonal (M := M) ⊆
      TransferredSuccessorPackageContinuationLocus g := by
  rintro _param ⟨⟨x, p⟩, _hxp, rfl⟩
  intro L hxSource _htargetSource _hchart
  apply nonempty_transferredPackage_of_normal_lt_selectedRadius
    hcurv x p L x hxSource
  rw [(CartanSourceExponential.genericFamily g).normal_anchor x, norm_zero]
  exact canonicalTransferredAnchorTargetRadius_pos hcurv x p

/-- Global openness of the conditional package locus supplies the weaker
diagonal-continuation hypothesis. -/
theorem transferredSuccessorPackageDiagonalContinuation_of_isOpen
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hopen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    TransferredSuccessorPackageDiagonalContinuation g := by
  exact hopen.mem_nhdsSet.mpr
    (successorParameterDiagonal_subset_transferredSuccessorPackageContinuationLocus_of_curvature
      hcurv)

/-- The former opaque transferred-radius local-stability boundary follows
from the three genuine moving-parameter facts:

1. generic source normals locally control endpoints and aligned vectors;
2. the generic/canonical target-chart agreement locus contains the target
   zero section in its interior;
3. transferred successor packages continue jointly once their explicit
   target-side transfer inputs hold.
-/
theorem transferredNormalRadiusLocalStability_of_source_target_package_stability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hsource : GenericSourceNormalLocalStability g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus)
    (hpackage : TransferredSuccessorPackageDiagonalContinuation g) :
    TransferredNormalRadiusLocalStability g := by
  rcases RoundSphereCanonicalExponential.exists_uniform_source_target_ball with
    ⟨canonicalRadius, hcanonicalRadius, hcanonicalBalls⟩
  intro xp
  rcases xp with ⟨x, p⟩
  let graphPoint : (M × RoundSphere3) × M := ((x, p), x)
  have hgraphPoint : graphPoint ∈
      CartanTargetExponential.successorParameterDiagonal (M := M) := by
    exact ⟨(x, p), Set.mem_univ _, rfl⟩
  have hpackageNhds :
      TransferredSuccessorPackageContinuationLocus g ∈
        𝓝 graphPoint :=
    mem_nhdsSet_iff_forall.mp hpackage graphPoint hgraphPoint
  rcases mem_nhds_prod_iff.mp hpackageNhds with
    ⟨A, hA, W, hW, hAW⟩
  rcases
      exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_interior
        p (htarget p) with
    ⟨V, hV, equalityRadius, hequalityRadius, hchartEq⟩
  let targetRadius : ℝ := min equalityRadius canonicalRadius
  have htargetRadius : 0 < targetRadius :=
    lt_min hequalityRadius hcanonicalRadius
  rcases hsource x W hW targetRadius htargetRadius with
    ⟨U, hU, sourceRadius, hsourceRadius, hcontrol⟩
  refine ⟨sourceRadius, hsourceRadius, ?_⟩
  filter_upwards [hA, prod_mem_nhds hU hV] with yq hyqA hyqUV
  intro L z hzSource hzNorm
  rcases hcontrol yq.1 hyqUV.1 yq.2 L z hzSource hzNorm with
    ⟨hzW, haligned⟩
  have hcontinuation :
      (yq, z) ∈ TransferredSuccessorPackageContinuationLocus g :=
    hAW ⟨hyqA, hzW⟩
  have halignedEquality :
      ‖alignedGenericSourceNormal g yq.1 yq.2 L z‖ < equalityRadius :=
    haligned.trans_le (min_le_left _ _)
  have halignedCanonical :
      ‖alignedGenericSourceNormal g yq.1 yq.2 L z‖ < canonicalRadius :=
    haligned.trans_le (min_le_right _ _)
  have halignedCanonicalBall :
      alignedGenericSourceNormal g yq.1 yq.2 L z ∈
        Metric.ball (0 : E) canonicalRadius := by
    simpa [Metric.mem_ball, dist_eq_norm] using halignedCanonical
  have halignedCanonicalSource :
      alignedGenericSourceNormal g yq.1 yq.2 L z ∈
        (canonicalFamily.chart yq.2).source := by
    simpa [canonicalFamily] using
      (hcanonicalBalls yq.2).1 halignedCanonicalBall
  have hchartGerm :
      (CartanTargetExponential.genericFamily.chart yq.2 : E → E)
          =ᶠ[𝓝 (alignedGenericSourceNormal g yq.1 yq.2 L z)]
        (canonicalFamily.chart yq.2 : E → E) :=
    genericFamily_chart_eventuallyEq_canonicalFamily_of_norm_lt
      (hchartEq yq.2 hyqUV.2) halignedEquality
  exact hcontinuation L hzSource halignedCanonicalSource hchartGerm

/-- Convenient openness form of the three-way decomposition.  Curvature is
used only to put the diagonal in the open conditional package locus. -/
theorem transferredNormalRadiusLocalStability_of_source_target_and_isOpen_packageLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hsource : GenericSourceNormalLocalStability g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus)
    (hopen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    TransferredNormalRadiusLocalStability g := by
  exact
    transferredNormalRadiusLocalStability_of_source_target_package_stability
      hsource htarget
      (transferredSuccessorPackageDiagonalContinuation_of_isOpen hcurv hopen)

/-- Positive, capped radii that are locally uniform at one source-target
pair.  The cap makes the supremum bounded without imposing any global scale. -/
def locallyUniformTransferredNormalRadiusCandidates
    (g : ClosedSmoothRiemannianMetric 3 M)
    (xp : M × RoundSphere3) : Set ℝ :=
  {radius : ℝ |
    0 < radius ∧ radius ≤ 1 ∧
      LocallyUniformTransferredNormalRadiusAt g xp radius}

/-- The canonical locally stable provenance radius.  Taking half of the
capped supremum keeps the selected value strictly below an actual locally
uniform candidate.  Inserting zero makes the supremum total even before local
positive-radius stability is supplied. -/
def canonicalLocallyUniformTransferredAnchorTargetRadius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) : ℝ :=
  sSup
      (insert (0 : ℝ)
        (locallyUniformTransferredNormalRadiusCandidates g (x, p))) /
    2

private theorem locallyUniformTransferredNormalRadiusCandidates_bddAbove
    (g : ClosedSmoothRiemannianMetric 3 M)
    (xp : M × RoundSphere3) :
    BddAbove
      (insert (0 : ℝ)
        (locallyUniformTransferredNormalRadiusCandidates g xp)) := by
  refine ⟨1, ?_⟩
  intro radius hradius
  rcases Set.mem_insert_iff.mp hradius with hradius | hradius
  · subst radius
    exact zero_le_one
  · exact hradius.2.1

/-- The locally stable envelope is always nonnegative. -/
theorem canonicalLocallyUniformTransferredAnchorTargetRadius_nonneg
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) :
    0 ≤ canonicalLocallyUniformTransferredAnchorTargetRadius g x p := by
  have hzero : (0 : ℝ) ≤
      sSup
        (insert (0 : ℝ)
          (locallyUniformTransferredNormalRadiusCandidates g (x, p))) :=
    le_csSup
      (locallyUniformTransferredNormalRadiusCandidates_bddAbove g (x, p))
      (Set.mem_insert (0 : ℝ) _)
  exact div_nonneg hzero (by norm_num)

/-- Lower semicontinuity is built into the envelope: for a fixed candidate
radius, the points where it is valid on a neighborhood form an open set. -/
theorem canonicalLocallyUniformTransferredAnchorTargetRadius_lowerSemicontinuous
    (g : ClosedSmoothRiemannianMetric 3 M) :
    LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalLocallyUniformTransferredAnchorTargetRadius g xp.1 xp.2) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  by_cases ha : a < 0
  · have hpreimage :
        (fun xp : M × RoundSphere3 ↦
          canonicalLocallyUniformTransferredAnchorTargetRadius
            g xp.1 xp.2) ⁻¹' Ioi a = Set.univ := by
      ext xp
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact ha.trans_le
        (canonicalLocallyUniformTransferredAnchorTargetRadius_nonneg
          g xp.1 xp.2)
    rw [hpreimage]
    exact isOpen_univ
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    rw [isOpen_iff_mem_nhds]
    intro xp hxp
    change a <
      canonicalLocallyUniformTransferredAnchorTargetRadius
        g xp.1 xp.2 at hxp
    let candidates : Set ℝ :=
      insert (0 : ℝ)
        (locallyUniformTransferredNormalRadiusCandidates g xp)
    have hnonempty : candidates.Nonempty := by
      exact ⟨0, by simp [candidates]⟩
    have hbdd : BddAbove candidates := by
      simpa [candidates] using
        locallyUniformTransferredNormalRadiusCandidates_bddAbove g xp
    have htwice : 2 * a < sSup candidates := by
      dsimp [canonicalLocallyUniformTransferredAnchorTargetRadius] at hxp
      simpa [candidates] using (show 2 * a <
        sSup
            (insert (0 : ℝ)
              (locallyUniformTransferredNormalRadiusCandidates g xp)) by
          linarith)
    rcases exists_lt_of_lt_csSup hnonempty htwice with
      ⟨radius, hradius, htwiceRadius⟩
    have hradiusCandidate :
        radius ∈ locallyUniformTransferredNormalRadiusCandidates g xp := by
      change radius ∈
        insert (0 : ℝ)
          (locallyUniformTransferredNormalRadiusCandidates g xp) at hradius
      rcases Set.mem_insert_iff.mp hradius with hradius | hradius
      · subst radius
        have : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha0
        exact (not_lt_of_ge this htwiceRadius).elim
      · exact hradius
    let stableSet : Set (M × RoundSphere3) :=
      {yq | ∀ᶠ wq in 𝓝 yq,
        TransferredNormalRadiusAdmissible g wq.1 wq.2 radius}
    have hstableOpen : IsOpen stableSet := by
      exact isOpen_setOf_eventually_nhds
    have hxpStable : xp ∈ stableSet := hradiusCandidate.2.2
    refine Filter.mem_of_superset
      (hstableOpen.mem_nhds hxpStable) ?_
    intro yq hyq
    change a <
      canonicalLocallyUniformTransferredAnchorTargetRadius
        g yq.1 yq.2
    have hradiusCandidateY :
        radius ∈ locallyUniformTransferredNormalRadiusCandidates g yq :=
      ⟨hradiusCandidate.1, hradiusCandidate.2.1, hyq⟩
    have hradiusLe : radius ≤
        sSup
          (insert (0 : ℝ)
            (locallyUniformTransferredNormalRadiusCandidates g yq)) :=
      le_csSup
        (locallyUniformTransferredNormalRadiusCandidates_bddAbove g yq)
        (Set.mem_insert_of_mem _ hradiusCandidateY)
    dsimp [canonicalLocallyUniformTransferredAnchorTargetRadius]
    linarith

/-- Local positive-radius stability makes the canonical envelope positive. -/
theorem canonicalLocallyUniformTransferredAnchorTargetRadius_pos
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : TransferredNormalRadiusLocalStability g)
    (x : M) (p : RoundSphere3) :
    0 < canonicalLocallyUniformTransferredAnchorTargetRadius g x p := by
  rcases hstable (x, p) with
    ⟨radius, hradius, hlocal⟩
  let capped : ℝ := min radius 1
  have hcapped : 0 < capped := by
    exact lt_min hradius zero_lt_one
  have hcappedLocal :
      LocallyUniformTransferredNormalRadiusAt g (x, p) capped := by
    filter_upwards [hlocal] with yq hyq
    exact hyq.mono (min_le_left _ _)
  have hcappedCandidate :
      capped ∈
        locallyUniformTransferredNormalRadiusCandidates g (x, p) :=
    ⟨hcapped, min_le_right _ _, hcappedLocal⟩
  have hcappedLe : capped ≤
      sSup
        (insert (0 : ℝ)
          (locallyUniformTransferredNormalRadiusCandidates g (x, p))) :=
    le_csSup
      (locallyUniformTransferredNormalRadiusCandidates_bddAbove g (x, p))
      (Set.mem_insert_of_mem _ hcappedCandidate)
  dsimp [canonicalLocallyUniformTransferredAnchorTargetRadius]
  linarith

/-- Under the exact local-stability boundary, the canonical envelope is
itself an admissible provenance radius at every source-target pair. -/
theorem canonicalLocallyUniformTransferredAnchorTargetRadius_admissible
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : TransferredNormalRadiusLocalStability g)
    (x : M) (p : RoundSphere3) :
    TransferredNormalRadiusAdmissible g x p
      (canonicalLocallyUniformTransferredAnchorTargetRadius g x p) := by
  let candidates : Set ℝ :=
    insert (0 : ℝ)
      (locallyUniformTransferredNormalRadiusCandidates g (x, p))
  have hnonempty : candidates.Nonempty := by
    exact ⟨0, by simp [candidates]⟩
  have hpositive :=
    canonicalLocallyUniformTransferredAnchorTargetRadius_pos hstable x p
  have hbelowSup : sSup candidates / 2 < sSup candidates := by
    have hsupPositive : 0 < sSup candidates := by
      dsimp [canonicalLocallyUniformTransferredAnchorTargetRadius] at hpositive
      simpa [candidates] using (show 0 <
        sSup
          (insert (0 : ℝ)
            (locallyUniformTransferredNormalRadiusCandidates g (x, p))) by
        linarith)
    linarith
  rcases exists_lt_of_lt_csSup hnonempty hbelowSup with
    ⟨radius, hradius, hbelowRadius⟩
  have hradiusCandidate :
      radius ∈ locallyUniformTransferredNormalRadiusCandidates g (x, p) := by
    change radius ∈
      insert (0 : ℝ)
        (locallyUniformTransferredNormalRadiusCandidates g (x, p)) at hradius
    rcases Set.mem_insert_iff.mp hradius with hradius | hradius
    · subst radius
      have hsupNonneg : 0 ≤ sSup candidates := by
        have hbdd : BddAbove candidates := by
          simpa [candidates] using
            locallyUniformTransferredNormalRadiusCandidates_bddAbove
              g (x, p)
        exact le_csSup hbdd (by simp [candidates])
      have : 0 ≤ sSup candidates / 2 := div_nonneg hsupNonneg (by norm_num)
      exact (not_lt_of_ge this hbelowRadius).elim
    · exact hradius
  have hradiusAdmissible :
      TransferredNormalRadiusAdmissible g x p radius :=
    hradiusCandidate.2.2.self_of_nhds
  apply hradiusAdmissible.mono
  dsimp [canonicalLocallyUniformTransferredAnchorTargetRadius]
  simpa [candidates] using le_of_lt hbelowRadius

/-- Any positive jointly lower-semicontinuous admissible provenance radius
has a positive lower-semicontinuous source-only minorant, uniformly over all
sphere targets and tangent alignments. -/
theorem exists_positive_lowerSemicontinuous_transferred_source_normal_radius_of_admissible
    {g : ClosedSmoothRiemannianMetric 3 M}
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hadmissible : ∀ (x : M) (p : RoundSphere3),
      TransferredNormalRadiusAdmissible g x p (pairRadius x p)) :
    ∃ sourceRadius : M → ℝ,
      (∀ x : M, 0 < sourceRadius x) ∧
      LowerSemicontinuous sourceRadius ∧
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        z ∈ ((genericFamily g).normal x).source →
        ‖(genericFamily g).normal x z‖ < sourceRadius x →
          Nonempty
            (TransferredSuccessorPackage
              (CartanChain.ChainState.mk x p L) z) := by
  rcases
      CartanAtlasRootedPathCurvatureSuccessorRadius.exists_positive_lowerSemicontinuous_source_minorant_of_compact_target
        pairRadius hpositive hlower with
    ⟨sourceRadius, hsourcePositive, hsourceLower, hsourceMinorant⟩
  refine ⟨sourceRadius, hsourcePositive, hsourceLower, ?_⟩
  intro x p L z hzSource hzNorm
  exact hadmissible x p L z hzSource
    (hzNorm.trans_le (hsourceMinorant x p))

/-- Chart-local provenance production from any positive jointly
lower-semicontinuous admissible radius. -/
theorem exists_chartLocal_genericNormal_transferredPackage_of_admissible
    {g : ClosedSmoothRiemannianMetric 3 M}
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hadmissible : ∀ (x : M) (p : RoundSphere3),
      TransferredNormalRadiusAdmissible g x p (pairRadius x p))
    (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ rho > (0 : ℝ),
        ∀ (x : M), x ∈ U →
          ∀ (p : RoundSphere3)
            (L : CartanMap.TangentAlignment g x p) (z : M),
            z ∈ ((genericFamily g).normal x).source →
            ‖(genericFamily g).normal x z‖ < rho →
              Nonempty
                (TransferredSuccessorPackage
                  (CartanChain.ChainState.mk x p L) z) := by
  rcases
      exists_positive_lowerSemicontinuous_transferred_source_normal_radius_of_admissible
        pairRadius hpositive hlower hadmissible with
    ⟨sourceRadius, hsourcePositive, hsourceLower, hsourcePackage⟩
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
  exact hsourcePackage x p L z hzSource (hzNorm.trans hx)

/-- The locally stable supremum envelope supplies the chart-local provenance
producer without any lower-semicontinuity or arbitrary-minorant premise. -/
theorem exists_chartLocal_genericNormal_transferredPackage_of_localStability
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hstable : TransferredNormalRadiusLocalStability g)
    (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ rho > (0 : ℝ),
        ∀ (x : M), x ∈ U →
          ∀ (p : RoundSphere3)
            (L : CartanMap.TangentAlignment g x p) (z : M),
            z ∈ ((genericFamily g).normal x).source →
            ‖(genericFamily g).normal x z‖ < rho →
              Nonempty
                (TransferredSuccessorPackage
                  (CartanChain.ChainState.mk x p L) z) := by
  apply exists_chartLocal_genericNormal_transferredPackage_of_admissible
    (fun x p ↦
      canonicalLocallyUniformTransferredAnchorTargetRadius g x p)
  · exact
      canonicalLocallyUniformTransferredAnchorTargetRadius_pos hstable
  · exact
      canonicalLocallyUniformTransferredAnchorTargetRadius_lowerSemicontinuous g
  · exact
      canonicalLocallyUniformTransferredAnchorTargetRadius_admissible hstable

/-- A jointly lower-semicontinuous positive minorant gives a source-only
provenance radius, uniformly over targets and alignments. -/
theorem exists_positive_lowerSemicontinuous_transferred_source_normal_radius_of_joint_minorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalTransferredAnchorTargetRadius hcurv x p) :
    ∃ sourceRadius : M → ℝ,
      (∀ x : M, 0 < sourceRadius x) ∧
      LowerSemicontinuous sourceRadius ∧
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        z ∈ ((genericFamily g).normal x).source →
        ‖(genericFamily g).normal x z‖ < sourceRadius x →
          Nonempty
            (TransferredSuccessorPackage
              (CartanChain.ChainState.mk x p L) z) := by
  rcases
      CartanAtlasRootedPathCurvatureSuccessorRadius.exists_positive_lowerSemicontinuous_source_minorant_of_compact_target
        pairRadius hpositive hlower with
    ⟨sourceRadius, hsourcePositive, hsourceLower, hsourceMinorant⟩
  refine ⟨sourceRadius, hsourcePositive, hsourceLower, ?_⟩
  intro x p L z hzSource hzNorm
  apply nonempty_transferredPackage_of_normal_lt_selectedRadius
    hcurv x p L z hzSource
  exact hzNorm.trans_le ((hsourceMinorant x p).trans (hminorant x p))

/-- Chart-local provenance production from the joint radius minorant. -/
theorem exists_chartLocal_genericNormal_transferredPackage_of_joint_minorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalTransferredAnchorTargetRadius hcurv x p)
    (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ rho > (0 : ℝ),
        ∀ (x : M), x ∈ U →
          ∀ (p : RoundSphere3)
            (L : CartanMap.TangentAlignment g x p) (z : M),
            z ∈ ((genericFamily g).normal x).source →
            ‖(genericFamily g).normal x z‖ < rho →
              Nonempty
                (TransferredSuccessorPackage
                  (CartanChain.ChainState.mk x p L) z) := by
  rcases
      exists_positive_lowerSemicontinuous_transferred_source_normal_radius_of_joint_minorant
        hcurv pairRadius hpositive hlower hminorant with
    ⟨sourceRadius, hsourcePositive, hsourceLower, hsourcePackage⟩
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
  apply hsourcePackage x p L z hzSource
  exact hzNorm.trans hx

end Curvature

/-- Endpoint agreement transfers generic-normal provenance production to the
chart-local source family without changing the retained package. -/
theorem localUniformTransferredData_of_genericEndpointAgreement
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g)
    {U : Set M} {rho : ℝ}
    (hrho : 0 < rho)
    (hanchors : A.anchors ⊆ U)
    (hendpoint : A.GenericEndpointAgreement rho)
    (hgenericPackage :
      ∀ (x : M), x ∈ U →
        ∀ (p : RoundSphere3)
          (L : CartanMap.TangentAlignment g x p) (z : M),
          z ∈ ((genericFamily g).normal x).source →
          ‖(genericFamily g).normal x z‖ < rho →
            Nonempty
              (TransferredSuccessorPackage
                (CartanChain.ChainState.mk x p L) z)) :
    LocalUniformNormalTransferredSuccessorData A := by
  refine ⟨rho, hrho, ?_⟩
  intro x p L z hzSource hzNorm
  rcases hendpoint.controlsGenericNormal x z hzSource hzNorm with
    ⟨hzGenericSource, hzGenericNorm⟩
  exact hgenericPackage x (hanchors (A.sourceLocus_fst (x, z) hzSource))
    p L z hzGenericSource hzGenericNorm

end CartanCanonicalFamilyProvenanceLocalUniformData
end Poincare
