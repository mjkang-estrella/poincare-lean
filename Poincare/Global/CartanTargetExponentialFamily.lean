import Poincare.Global.DifferentialInducedSuccessor
import Poincare.Global.RoundSphereCanonicalExponential
import Poincare.Global.CartanAtlasRootedPathSkeleton

/-!
# Cartan constructions with a supplied round-sphere exponential family

The existing Cartan map uses
`GeodesicTransport.expAtChartOpenPartialHomeomorph` at its target anchor.  That
partial homeomorphism is obtained by a classical choice made independently at
each anchor, so its API does not provide joint regularity as the target anchor
varies.

This module separates that target-side choice from the Cartan construction.
It provides:

* a small interface for a family of target exponential charts;
* the existing generic construction as a definitionally equal adapter;
* the reference-normalized round-sphere construction as a genuinely jointly
  regular instance, without identifying it with the generic exponential;
* Cartan maps, chart maps, chain states, and differential-successor data
  parameterized by the supplied family; and
* a compactness theorem turning joint source/target regularity into one
  anchor-uniform coordinate radius.

The source exponential on the unknown manifold remains the existing generic
`expAt`: only the round-sphere target dependency is abstracted here.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace unitInterval

namespace Poincare
namespace CartanTargetExponential

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
A target exponential chart at every round-sphere anchor.

The coordinate value at the zero tangent vector is required to be zero.  The
sphere-valued map represented by the chart is therefore based at its supplied
anchor after applying `(extChartAt I p).symm`.
-/
structure Family where
  chart : RoundSphere3 → OpenPartialHomeomorph E E
  zero_mem_source : ∀ p, (0 : E) ∈ (chart p).source
  chart_zero : ∀ p, chart p (0 : E) = 0

/-- The joint locus on which the forward target chart is locally invertible. -/
def Family.sourceLocus (F : Family) : Set (RoundSphere3 × E) :=
  {q | q.2 ∈ (F.chart q.1).source}

/-- The joint image locus of the target exponential charts. -/
def Family.targetLocus (F : Family) : Set (RoundSphere3 × E) :=
  {q | q.2 ∈ (F.chart q.1).target}

/-- Evaluation of the supplied family in joint anchor-vector parameters. -/
def Family.eval (F : Family) (q : RoundSphere3 × E) : E :=
  F.chart q.1 q.2

/-- Evaluation of the inverse charts in joint anchor-vector parameters. -/
def Family.symmEval (F : Family) (q : RoundSphere3 × E) : E :=
  (F.chart q.1).symm q.2

/--
The target-chart regularity needed for compact uniformization.

This contract records openness of both varying domains and continuity of the
forward and inverse evaluations on those domains.  In particular, it is much
stronger than having an unrelated local inverse at every fixed anchor.
-/
structure Family.JointlyRegular (F : Family) : Prop where
  isOpen_sourceLocus : IsOpen F.sourceLocus
  isOpen_targetLocus : IsOpen F.targetLocus
  continuousOn_eval : ContinuousOn F.eval F.sourceLocus
  continuousOn_symmEval : ContinuousOn F.symmEval F.targetLocus

/-- Identity strict derivative at the zero vector for every target anchor. -/
def Family.HasIdentityStrictDerivativeAtZero (F : Family) : Prop :=
  ∀ p : RoundSphere3,
    HasStrictFDerivAt (F.chart p) (ContinuousLinearMap.id ℝ E) (0 : E)

/-- The current independently chosen target exponential charts. -/
def genericFamily : Family where
  chart p :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := roundSphereMetric3) p
  zero_mem_source p :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := roundSphereMetric3) p
  chart_zero p := by
    calc
      GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p (0 : E) =
          (chartAt E p) p :=
        CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
          roundSphereMetric3 p
      _ = 0 := by
        simpa [extChartAt_coe] using
          RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero p

/--
The reference-normalized round-sphere family.  This is intentionally a
separate adapter: no equality with `genericFamily` is asserted.
-/
def canonicalFamily : Family where
  chart := RoundSphereCanonicalExponential.chartOpenPartialHomeomorph
  zero_mem_source :=
    RoundSphereCanonicalExponential.zero_mem_chartOpenPartialHomeomorph_source
  chart_zero p := by
    simpa [RoundSphereCanonicalExponential.chartOpenPartialHomeomorph] using
      RoundSphereCanonicalExponential.coordinateLocalHomeomorph_zero

/-- The generic family has the expected identity derivative at zero. -/
theorem genericFamily_hasIdentityStrictDerivativeAtZero :
    genericFamily.HasIdentityStrictDerivativeAtZero := by
  intro p
  simpa [Family.HasIdentityStrictDerivativeAtZero, genericFamily] using
    GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
      (g := roundSphereMetric3) (x₀ := p)

/-- The normalized family has the identity derivative at every anchor. -/
theorem canonicalFamily_hasIdentityStrictDerivativeAtZero :
    canonicalFamily.HasIdentityStrictDerivativeAtZero := by
  intro p
  simpa [Family.HasIdentityStrictDerivativeAtZero, canonicalFamily] using
    RoundSphereCanonicalExponential.chart_expAt_hasStrictFDerivAt_zero p

/-- The normalized family's forward source locus is a product preimage. -/
theorem canonicalFamily_sourceLocus :
    canonicalFamily.sourceLocus =
      Prod.snd ⁻¹' RoundSphereCanonicalExponential.coordinateLocalHomeomorph.source :=
  rfl

/-- The normalized family's inverse source locus is a product preimage. -/
theorem canonicalFamily_targetLocus :
    canonicalFamily.targetLocus =
      Prod.snd ⁻¹' RoundSphereCanonicalExponential.coordinateLocalHomeomorph.target :=
  rfl

/--
The normalized family is jointly regular because both coordinate maps and
both inverse-function domains are literally independent of the anchor.
-/
theorem canonicalFamily_jointlyRegular : canonicalFamily.JointlyRegular := by
  constructor
  · rw [canonicalFamily_sourceLocus]
    exact
      RoundSphereCanonicalExponential.coordinateLocalHomeomorph.open_source.preimage
        continuous_snd
  · rw [canonicalFamily_targetLocus]
    exact
      RoundSphereCanonicalExponential.coordinateLocalHomeomorph.open_target.preimage
        continuous_snd
  · rw [canonicalFamily_sourceLocus]
    change ContinuousOn
      (fun q : RoundSphere3 × E ↦
        RoundSphereCanonicalExponential.coordinateLocalHomeomorph q.2)
      (Prod.snd ⁻¹'
        RoundSphereCanonicalExponential.coordinateLocalHomeomorph.source)
    exact
      RoundSphereCanonicalExponential.coordinateLocalHomeomorph.continuousOn.comp
        continuous_snd.continuousOn (fun _ hq ↦ hq)
  · rw [canonicalFamily_targetLocus]
    change ContinuousOn
      (fun q : RoundSphere3 × E ↦
        RoundSphereCanonicalExponential.coordinateLocalHomeomorph.symm q.2)
      (Prod.snd ⁻¹'
        RoundSphereCanonicalExponential.coordinateLocalHomeomorph.target)
    exact
      RoundSphereCanonicalExponential.coordinateLocalHomeomorph.symm.continuousOn.comp
        continuous_snd.continuousOn (fun _ hq ↦ hq)

/-- The compact zero section in joint target-anchor coordinates. -/
def zeroSection : Set (RoundSphere3 × E) :=
  (fun p : RoundSphere3 ↦ (p, (0 : E))) '' Set.univ

theorem isCompact_zeroSection : IsCompact zeroSection := by
  exact isCompact_univ.image (continuous_id.prodMk continuous_const)

/-- Every family's joint source locus contains the complete zero section. -/
theorem zeroSection_subset_sourceLocus (F : Family) :
    zeroSection ⊆ F.sourceLocus := by
  rintro _q ⟨p, _hp, rfl⟩
  exact F.zero_mem_source p

/-- Every family's joint target locus contains the complete zero section. -/
theorem zeroSection_subset_targetLocus (F : Family) :
    zeroSection ⊆ F.targetLocus := by
  rintro _q ⟨p, _hp, rfl⟩
  have hmap := (F.chart p).map_source (F.zero_mem_source p)
  simpa [Family.targetLocus, F.chart_zero p] using hmap

/--
Joint openness of the varying source domains gives one positive coordinate
ball contained in every source.  This is the compact zero-section argument
that is unavailable for independently chosen pointwise inverses.
-/
theorem exists_uniform_source_ball_of_isOpen_sourceLocus
    (F : Family) (hopen : IsOpen F.sourceLocus) :
    ∃ r > (0 : ℝ), ∀ p : RoundSphere3,
      Metric.ball (0 : E) r ⊆ (F.chart p).source := by
  rcases
      isCompact_zeroSection.exists_cthickening_subset_open
        hopen (zeroSection_subset_sourceLocus F) with
    ⟨r, hr, hthick⟩
  refine ⟨r, hr, ?_⟩
  intro p v hv
  have hvnorm : ‖v‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hzero : (p, (0 : E)) ∈ zeroSection :=
    ⟨p, Set.mem_univ p, rfl⟩
  have hmem : (p, v) ∈ Metric.cthickening r zeroSection := by
    apply Metric.mem_cthickening_of_dist_le
      ((p, v) : RoundSphere3 × E) (p, (0 : E)) r zeroSection hzero
    simpa [Prod.dist_eq, dist_eq_norm] using le_of_lt hvnorm
  exact hthick hmem

/-- Joint openness gives one positive ball contained in every inverse target. -/
theorem exists_uniform_target_ball_of_isOpen_targetLocus
    (F : Family) (hopen : IsOpen F.targetLocus) :
    ∃ r > (0 : ℝ), ∀ p : RoundSphere3,
      Metric.ball (0 : E) r ⊆ (F.chart p).target := by
  rcases
      isCompact_zeroSection.exists_cthickening_subset_open
        hopen (zeroSection_subset_targetLocus F) with
    ⟨r, hr, hthick⟩
  refine ⟨r, hr, ?_⟩
  intro p v hv
  have hvnorm : ‖v‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hzero : (p, (0 : E)) ∈ zeroSection :=
    ⟨p, Set.mem_univ p, rfl⟩
  have hmem : (p, v) ∈ Metric.cthickening r zeroSection := by
    apply Metric.mem_cthickening_of_dist_le
      ((p, v) : RoundSphere3 × E) (p, (0 : E)) r zeroSection hzero
    simpa [Prod.dist_eq, dist_eq_norm] using le_of_lt hvnorm
  exact hthick hmem

/--
A jointly regular supplied exponential family has one positive ball on which
both partial-homeomorphism domains work at every target anchor.
-/
theorem exists_uniform_source_target_ball_of_jointlyRegular
    (F : Family) (hregular : F.JointlyRegular) :
    ∃ r > (0 : ℝ), ∀ p : RoundSphere3,
      Metric.ball (0 : E) r ⊆ (F.chart p).source ∧
      Metric.ball (0 : E) r ⊆ (F.chart p).target := by
  rcases exists_uniform_source_ball_of_isOpen_sourceLocus
      F hregular.isOpen_sourceLocus with ⟨rs, hrs, hs⟩
  rcases exists_uniform_target_ball_of_isOpen_targetLocus
      F hregular.isOpen_targetLocus with ⟨rt, hrt, ht⟩
  refine ⟨min rs rt, lt_min hrs hrt, ?_⟩
  intro p
  constructor
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans (hs p)
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans (ht p)

/--
The local Cartan partial homeomorphism using a supplied target exponential
family.  The source exponential remains the Riemannian exponential of `g`.
-/
def openPartialHomeomorph
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    OpenPartialHomeomorph M RoundSphere3 :=
  (chartAt E x₀).trans
    ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).symm.trans
      ((CartanMap.tangentAlignmentOpenPartialHomeomorph L).trans
        ((F.chart p₀).trans (chartAt E p₀).symm)))

/-- The total Cartan map associated to a supplied target family. -/
def cartanMap
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) : M → RoundSphere3 :=
  openPartialHomeomorph F g x₀ p₀ L

/-- The generic adapter recovers the existing Cartan partial homeomorphism. -/
@[simp]
theorem openPartialHomeomorph_generic_eq
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    openPartialHomeomorph genericFamily g x₀ p₀ L =
      CartanMap.openPartialHomeomorph g x₀ p₀ L :=
  rfl

/-- The generic adapter recovers the existing total Cartan map. -/
@[simp]
theorem cartanMap_generic_eq
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    cartanMap genericFamily g x₀ p₀ L = CartanMap.cartanMap g x₀ p₀ L :=
  rfl

theorem cartanMap_apply
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) (x : M) :
    cartanMap F g x₀ p₀ L x =
      (chartAt E p₀).symm
        (F.chart p₀
          (L ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₀).symm ((chartAt E x₀) x)))) :=
  rfl

/-- Every supplied-family Cartan map sends its source anchor to its target. -/
theorem cartanMap_anchor
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    cartanMap F g x₀ p₀ L x₀ = p₀ := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  have hM : eM.symm ((chartAt E x₀) x₀) = (0 : E) := by
    simpa [eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero
        (g := g) x₀
  have hp : (chartAt E p₀) p₀ = (0 : E) := by
    simpa [extChartAt_coe] using
      RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero p₀
  calc
    cartanMap F g x₀ p₀ L x₀ =
        (chartAt E p₀).symm (F.chart p₀ (L (eM.symm ((chartAt E x₀) x₀)))) := rfl
    _ = (chartAt E p₀).symm (F.chart p₀ (L (0 : E))) := by rw [hM]
    _ = (chartAt E p₀).symm (F.chart p₀ (0 : E)) := by simp
    _ = (chartAt E p₀).symm (0 : E) := by rw [F.chart_zero]
    _ = (chartAt E p₀).symm ((chartAt E p₀) p₀) := by rw [hp]
    _ = p₀ := (chartAt E p₀).left_inv (mem_chart_source E p₀)

/-- The source anchor lies in every supplied-family Cartan germ. -/
theorem anchor_mem_source
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    x₀ ∈ (openPartialHomeomorph F g x₀ p₀ L).source := by
  simp [openPartialHomeomorph,
    CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero]
  constructor
  · simpa [closedSmoothModelWithCorners, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x₀
  constructor
  · simp [CartanMap.tangentAlignmentOpenPartialHomeomorph]
  · constructor
    · exact F.zero_mem_source p₀
    · have hpmap :=
        (chartAt E p₀).map_source (mem_chart_source E p₀)
      have hpzero : (chartAt E p₀) p₀ = (0 : E) := by
        simpa [extChartAt_coe] using
          RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero p₀
      simpa [F.chart_zero p₀, hpzero] using hpmap

/-- The target anchor lies in every supplied-family Cartan germ image. -/
theorem anchor_mem_target
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    p₀ ∈ (openPartialHomeomorph F g x₀ p₀ L).target := by
  have hx := anchor_mem_source F g x₀ p₀ L
  have hmap := (openPartialHomeomorph F g x₀ p₀ L).map_source hx
  change cartanMap F g x₀ p₀ L x₀ ∈
    (openPartialHomeomorph F g x₀ p₀ L).target at hmap
  simpa [cartanMap_anchor] using hmap

/--
At a fixed source anchor, joint target regularity gives one ordinary metric
ball contained in every supplied-family Cartan germ, simultaneously for all
round-sphere targets and all tangent alignments.

The only source-anchor dependence left in this theorem is the generic source
normal coordinate and its Euclidean comparison constant.  No continuity of
the independently chosen source exponential in that anchor is asserted.
-/
theorem exists_metric_ball_subset_germ_source_all_targets_alignments_fixed_source
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (F : Family) (hregular : F.JointlyRegular)
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (p : RoundSphere3) (L : CartanMap.TangentAlignment g x p),
        Metric.ball x epsilon ⊆
          (openPartialHomeomorph F g x p L).source := by
  letI : MetricSpace M := g.toMetricSpace
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) x
  let sourceNormal : OpenPartialHomeomorph M E :=
    (chartAt E x).trans eM.symm
  have hxSourceNormal : x ∈ sourceNormal.source := by
    change x ∈ (chartAt E x).source ∩ (chartAt E x) ⁻¹' eM.target
    refine ⟨mem_chart_source E x, ?_⟩
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  rcases
      RoundSphereTargetAnchorUniformity.exists_pos_uniform_tangentAlignment_operatorNorm_bound_all_targets
        g x with
    ⟨C, hC, hoperator⟩
  rcases exists_uniform_source_ball_of_isOpen_sourceLocus
      F hregular.isOpen_sourceLocus with
    ⟨targetRadius, htargetRadius, htargetBall⟩
  let vectorRadius : ℝ := targetRadius / C
  have hvectorRadius : 0 < vectorRadius := div_pos htargetRadius hC
  let normalCoordinate : M → E := fun z => sourceNormal z
  have hnormal : ContinuousAt normalCoordinate x :=
    sourceNormal.continuousAt hxSourceNormal
  have hnormalZero : normalCoordinate x = (0 : E) := by
    change eM.symm ((chartAt E x) x) = (0 : E)
    simpa [eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x
  have hvectorNhds :
      normalCoordinate ⁻¹' Metric.ball (0 : E) vectorRadius ∈ 𝓝 x := by
    apply hnormal.preimage_mem_nhds
    rw [hnormalZero]
    exact Metric.ball_mem_nhds (0 : E) hvectorRadius
  have hcontrolledNhds :
      sourceNormal.source ∩
          normalCoordinate ⁻¹' Metric.ball (0 : E) vectorRadius ∈ 𝓝 x :=
    inter_mem (sourceNormal.open_source.mem_nhds hxSourceNormal) hvectorNhds
  rcases Metric.mem_nhds_iff.mp hcontrolledNhds with
    ⟨epsilon, hepsilon, hcontrolled⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro p L z hz
  have hzControlled := hcontrolled hz
  have hzSourceNormal :
      z ∈ (chartAt E x).source ∧ (chartAt E x) z ∈ eM.target := by
    simpa [sourceNormal] using hzControlled.1
  let v : E := normalCoordinate z
  have hv : ‖v‖ < vectorRadius := by
    simpa [v, Metric.mem_ball, dist_eq_norm] using hzControlled.2
  let A : E →L[ℝ] E :=
    L.toContinuousLinearEquiv.toContinuousLinearMap
  have hLv : ‖L v‖ < targetRadius := by
    calc
      ‖L v‖ = ‖A v‖ := rfl
      _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ C * ‖v‖ :=
        mul_le_mul_of_nonneg_right (hoperator p L) (norm_nonneg v)
      _ < C * vectorRadius := mul_lt_mul_of_pos_left hv hC
      _ = targetRadius := by
        dsimp only [vectorRadius]
        exact mul_div_cancel₀ targetRadius (ne_of_gt hC)
  have hLvSource : L v ∈ (F.chart p).source := by
    apply htargetBall p
    simpa [Metric.mem_ball, dist_eq_norm] using hLv
  have htargetChart : F.chart p (L v) ∈ (chartAt E p).target := by
    have huniv : (chartAt E p).target = Set.univ := by
      simpa [extChartAt_target] using
        RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_target_eq_univ p
    rw [huniv]
    exact Set.mem_univ _
  have hvAlignment :
      v ∈ (CartanMap.tangentAlignmentOpenPartialHomeomorph L).source := by
    simp [CartanMap.tangentAlignmentOpenPartialHomeomorph]
  simpa [openPartialHomeomorph, sourceNormal, normalCoordinate, eM, v] using
    ⟨hzSourceNormal.1, hzSourceNormal.2, hvAlignment, hLvSource,
      htargetChart⟩

section CartanChartMap

/-- Chart-coordinate Cartan composition for a supplied target family. -/
def cartanChartMap
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) : E → E :=
  fun y : E =>
    F.chart p₀
      (L ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x₀).symm y))

/-- Generic specialization is definitionally the existing chart map. -/
@[simp]
theorem cartanChartMap_generic_eq
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    cartanChartMap genericFamily g x₀ p₀ L =
      CartanDifferential.cartanChartMap g x₀ p₀ L :=
  rfl

/--
For the normalized family the target coordinate exponential is the same fixed
map at every target anchor.
-/
theorem cartanChartMap_canonical_eq
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    cartanChartMap canonicalFamily g x₀ p₀ L =
      fun y : E =>
        RoundSphereCanonicalExponential.coordinateLocalHomeomorph
          (L ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₀).symm y)) :=
  rfl

/-- Strict chain rule for a supplied target exponential chart. -/
theorem cartanChartMap_hasStrictFDerivAt_of_charts
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsource :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htarget :
      HasStrictFDerivAt (F.chart p₀) (B : E →L[ℝ] E) (L v)) :
    HasStrictFDerivAt
      (cartanChartMap F g x₀ p₀ L)
      ((B : E →L[ℝ] E).comp
        ((L.toContinuousLinearEquiv : E →L[ℝ] E).comp
          (A.symm : E →L[ℝ] E)))
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := F.chart p₀
  have hleft : eM.symm (eM v) = v := eM.left_inv hvsrc
  have hsource' : HasStrictFDerivAt eM (A : E →L[ℝ] E)
      (eM.symm (eM v)) := by
    rw [hleft]
    exact hsource
  have hinv :
      HasStrictFDerivAt eM.symm (A.symm : E →L[ℝ] E) (eM v) :=
    eM.hasStrictFDerivAt_symm (eM.map_source hvsrc) hsource'
  have hL :
      HasStrictFDerivAt (fun z : E => L z)
        (L.toContinuousLinearEquiv : E →L[ℝ] E) v :=
    L.toContinuousLinearEquiv.hasStrictFDerivAt
  have hL_at :
      HasStrictFDerivAt (fun z : E => L z)
        (L.toContinuousLinearEquiv : E →L[ℝ] E) (eM.symm (eM v)) := by
    rw [hleft]
    exact hL
  have hL' :
      HasStrictFDerivAt (fun y : E => L (eM.symm y))
        ((L.toContinuousLinearEquiv : E →L[ℝ] E).comp
          (A.symm : E →L[ℝ] E)) (eM v) := by
    simpa [Function.comp_def] using hL_at.comp (eM v) hinv
  have htarget' :
      HasStrictFDerivAt eS (B : E →L[ℝ] E) (L (eM.symm (eM v))) := by
    rw [hleft]
    exact htarget
  have hcomp := htarget'.comp (eM v) hL'
  simpa [cartanChartMap, eM, eS, Function.comp_def] using hcomp

/-- At the anchor, identity endpoint derivatives reduce the Cartan derivative to `L`. -/
theorem cartanChartMap_hasStrictFDerivAt_anchor
    (F : Family) (hF : F.HasIdentityStrictDerivativeAtZero)
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    HasStrictFDerivAt
      (cartanChartMap F g x₀ p₀ L)
      (L.toContinuousLinearEquiv : E →L[ℝ] E)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x₀) (0 : E)) := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  have hvsrc : (0 : E) ∈ eM.source :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) x₀
  have hsource :
      HasStrictFDerivAt eM (ContinuousLinearMap.id ℝ E) (0 : E) := by
    simpa [eM] using
      GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
        (g := g) (x₀ := x₀)
  have htarget :
      HasStrictFDerivAt (F.chart p₀) (ContinuousLinearMap.id ℝ E)
        (L (0 : E)) := by
    simpa using hF p₀
  have h :=
    cartanChartMap_hasStrictFDerivAt_of_charts
      F g x₀ p₀ L
      (v := (0 : E))
      (A := ContinuousLinearEquiv.refl ℝ E)
      (B := ContinuousLinearEquiv.refl ℝ E)
      hvsrc hsource htarget
  simpa using h

/-- Anchor derivative theorem for the normalized round-sphere family. -/
theorem canonical_cartanChartMap_hasStrictFDerivAt_anchor
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    HasStrictFDerivAt
      (cartanChartMap canonicalFamily g x₀ p₀ L)
      (L.toContinuousLinearEquiv : E →L[ℝ] E)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x₀) (0 : E)) :=
  cartanChartMap_hasStrictFDerivAt_anchor canonicalFamily
    canonicalFamily_hasIdentityStrictDerivativeAtZero g x₀ p₀ L

end CartanChartMap

section ChainStateAndData

/--
A Cartan continuation state whose target exponential dependency is explicit.
The three geometric fields are unchanged from `CartanChain.ChainState`.
-/
structure ChainState (F : Family) (g : ClosedSmoothRiemannianMetric 3 M) where
  anchor : M
  target : RoundSphere3
  alignment : CartanMap.TangentAlignment g anchor target

namespace ChainState

variable {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}

/-- The supplied-family Cartan germ carried by a state. -/
def germ (s : ChainState F g) : OpenPartialHomeomorph M RoundSphere3 :=
  openPartialHomeomorph F g s.anchor s.target s.alignment

/-- The supplied-family total Cartan map carried by a state. -/
def map (s : ChainState F g) : M → RoundSphere3 :=
  cartanMap F g s.anchor s.target s.alignment

/-- Re-anchor a state, retaining the same supplied target family. -/
def next (s : ChainState F g) (x₁ : M) : ChainState F g where
  anchor := x₁
  target := s.map x₁
  alignment :=
    Classical.choice
      (CartanMap.tangentAlignment_nonempty
        (g := g) (x₀ := x₁) (p₀ := s.map x₁))

@[simp]
theorem next_anchor (s : ChainState F g) (x₁ : M) :
    (s.next x₁).anchor = x₁ :=
  rfl

@[simp]
theorem next_target (s : ChainState F g) (x₁ : M) :
    (s.next x₁).target = s.map x₁ :=
  rfl

/-- Regard an existing chain state as a generic-family state. -/
def ofGeneric (s : CartanChain.ChainState g) : ChainState genericFamily g where
  anchor := s.anchor
  target := s.target
  alignment := s.alignment

/-- Forget the explicit generic-family tag. -/
def toGeneric (s : ChainState genericFamily g) : CartanChain.ChainState g where
  anchor := s.anchor
  target := s.target
  alignment := s.alignment

/--
Use the geometric fields of an existing chain state as the initial state for
an arbitrary supplied target family.  This does not compare the resulting
Cartan maps.
-/
def retarget (F : Family) (s : CartanChain.ChainState g) : ChainState F g where
  anchor := s.anchor
  target := s.target
  alignment := s.alignment

@[simp]
theorem ofGeneric_anchor (s : CartanChain.ChainState g) :
    (ofGeneric s).anchor = s.anchor :=
  rfl

@[simp]
theorem ofGeneric_target (s : CartanChain.ChainState g) :
    (ofGeneric s).target = s.target :=
  rfl

@[simp]
theorem toGeneric_anchor (s : ChainState genericFamily g) :
    s.toGeneric.anchor = s.anchor :=
  rfl

@[simp]
theorem toGeneric_target (s : ChainState genericFamily g) :
    s.toGeneric.target = s.target :=
  rfl

@[simp]
theorem retarget_anchor (F : Family) (s : CartanChain.ChainState g) :
    (retarget F s).anchor = s.anchor :=
  rfl

@[simp]
theorem retarget_target (F : Family) (s : CartanChain.ChainState g) :
    (retarget F s).target = s.target :=
  rfl

/-- The existing generic germ is recovered definitionally. -/
@[simp]
theorem ofGeneric_germ (s : CartanChain.ChainState g) :
    (ofGeneric s).germ = s.germ :=
  rfl

/-- The existing generic map is recovered definitionally. -/
@[simp]
theorem ofGeneric_map (s : CartanChain.ChainState g) :
    (ofGeneric s).map = s.map :=
  rfl

@[simp]
theorem toGeneric_germ (s : ChainState genericFamily g) :
    s.toGeneric.germ = s.germ :=
  rfl

@[simp]
theorem toGeneric_map (s : ChainState genericFamily g) :
    s.toGeneric.map = s.map :=
  rfl

@[simp]
theorem toGeneric_ofGeneric (s : CartanChain.ChainState g) :
    (ofGeneric s).toGeneric = s := by
  cases s
  rfl

@[simp]
theorem ofGeneric_toGeneric (s : ChainState genericFamily g) :
    ofGeneric s.toGeneric = s := by
  cases s
  rfl

end ChainState

/--
Differential data for a successor of a supplied-family Cartan state.

This is the target-parameterized counterpart of
`DifferentialInducedSuccessor.Data`.  Every target occurrence now uses
`F.chart s.target`, including endpoint coordinates, strict derivatives, and
the metric pullback point.  The generic specialization is adapted back to the
existing structure below.
-/
structure Data (F : Family) {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState F g) (x₁ : M) where
  v : E
  A : E ≃L[ℝ] E
  B : E ≃L[ℝ] E
  source_vector_mem :
    v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).source
  target_vector_mem : s.alignment v ∈ (F.chart s.target).source
  source_mem_oldChart : x₁ ∈ (extChartAt I s.anchor).source
  target_mem_oldChart : s.map x₁ ∈ (extChartAt I s.target).source
  source_coordinate :
    extChartAt I s.anchor x₁ =
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor v
  target_coordinate :
    extChartAt I s.target (s.map x₁) =
      F.chart s.target (s.alignment v)
  source_exp_derivative :
    HasStrictFDerivAt
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor) (A : E →L[ℝ] E) v
  target_exp_derivative :
    HasStrictFDerivAt (F.chart s.target) (B : E →L[ℝ] E)
      (s.alignment v)
  cartan_chart_derivative :
    HasStrictFDerivAt
      (cartanChartMap F g s.anchor s.target s.alignment)
      (CartanLocalIsometry.cartanChartDifferential s.alignment A B)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor) v)
  metric_pullback :
    ∀ u u' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner s.target
          (F.chart s.target (s.alignment v))
          (CartanLocalIsometry.cartanChartDifferential s.alignment A B u)
          (CartanLocalIsometry.cartanChartDifferential s.alignment A B u') =
        CovariantDerivative.chartMetric g.inner s.anchor
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) s.anchor) v) u u'

/--
Coordinate-only form of the induced-alignment construction.

Unlike `InducedAlignment.inducedTangentAlignmentOfChartPullback`, the two old
chart coordinates are arbitrary expressions `zM` and `zT`; no target
exponential implementation is mentioned.  This is the algebraic bridge that
makes supplied-family successor data operational.
-/
def inducedTangentAlignmentOfCoordinatePullback
    {g : ClosedSmoothRiemannianMetric 3 M}
    {x₀ x₁ : M} {p₀ p₁ : RoundSphere3}
    (L₀ : CartanMap.TangentAlignment g x₀ p₀)
    {zM zT : E} {A B : E ≃L[ℝ] E}
    (hx₁_old : x₁ ∈ (extChartAt I x₀).source)
    (hp₁_old : p₁ ∈ (extChartAt I p₀).source)
    (hxcoord : extChartAt I x₀ x₁ = zM)
    (hpcoord : extChartAt I p₀ p₁ = zT)
    (hpullback :
      ∀ u u' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ zT
            (CartanLocalIsometry.cartanChartDifferential L₀ A B u)
            (CartanLocalIsometry.cartanChartDifferential L₀ A B u') =
          CovariantDerivative.chartMetric g.inner x₀ zM u u') :
    CartanMap.TangentAlignment g x₁ p₁ := by
  let zSource : E := extChartAt I x₁ x₁
  have hzSource : zSource ∈ (extChartAt I x₁).target := by
    simpa [zSource] using
      (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
  have hsourceSymm : (extChartAt I x₁).symm zSource = x₁ := by
    simpa [zSource] using
      (extChartAt I x₁).left_inv (mem_extChartAt_source x₁)
  have hySource : (extChartAt I x₁).symm zSource ∈ (extChartAt I x₀).source := by
    rw [hsourceSymm]
    exact hx₁_old
  let sourceCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv (x₀ := x₁) (y₀ := x₀) zSource
  have hsourceCLM_inv : sourceCLM.IsInvertible := by
    dsimp [sourceCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hySource).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzSource)
  let sourceEquiv : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible sourceCLM hsourceCLM_inv
  have hsourceEquiv_coe : (sourceEquiv : E →L[ℝ] E) = sourceCLM := by
    simpa [sourceEquiv, InducedAlignment.continuousLinearEquivOfInvertible] using
      Classical.choose_spec hsourceCLM_inv
  have hsourceChartPoint :
      GeodesicTransport.chartTransition (n := 3) x₁ x₀ zSource = zM := by
    change extChartAt I x₀ ((extChartAt I x₁).symm zSource) = zM
    rw [hsourceSymm]
    exact hxcoord

  let zTarget : E := extChartAt I p₁ p₁
  have hzTarget : zTarget ∈ (extChartAt I p₁).target := by
    simpa [zTarget] using
      (extChartAt I p₁).map_source (mem_extChartAt_source p₁)
  have htargetSymm : (extChartAt I p₁).symm zTarget = p₁ := by
    simpa [zTarget] using
      (extChartAt I p₁).left_inv (mem_extChartAt_source p₁)
  have hyTarget : (extChartAt I p₁).symm zTarget ∈ (extChartAt I p₀).source := by
    rw [htargetSymm]
    exact hp₁_old
  let targetCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv (x₀ := p₁) (y₀ := p₀) zTarget
  have htargetCLM_inv : targetCLM.IsInvertible := by
    dsimp [targetCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hyTarget).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzTarget)
  let targetEquiv : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible targetCLM htargetCLM_inv
  have htargetEquiv_coe : (targetEquiv : E →L[ℝ] E) = targetCLM := by
    simpa [targetEquiv, InducedAlignment.continuousLinearEquivOfInvertible] using
      Classical.choose_spec htargetCLM_inv
  have htargetChartPoint :
      GeodesicTransport.chartTransition (n := 3) p₁ p₀ zTarget = zT := by
    change extChartAt I p₀ ((extChartAt I p₁).symm zTarget) = zT
    rw [htargetSymm]
    exact hpcoord

  let oldD : E ≃L[ℝ] E := (A.symm.trans L₀.toContinuousLinearEquiv).trans B
  have holdD :
      (oldD : E →L[ℝ] E) =
        CartanLocalIsometry.cartanChartDifferential L₀ A B := by
    ext u
    simp [oldD, CartanLocalIsometry.cartanChartDifferential]
  let induced : E ≃L[ℝ] E :=
    (sourceEquiv.trans oldD).trans targetEquiv.symm
  refine
    { toLinearEquiv := induced.toLinearEquiv
      map_app' := ?_ }
  intro u u'
  have htargetTransport :=
    GeodesicTransport.chartMetric_chartTransitionMFDeriv
      (g := roundSphereMetric3) (x₀ := p₁) (y₀ := p₀)
      (z := zTarget) hyTarget (induced u) (induced u')
  have htargetTransport' :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
          (induced u) (induced u') =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ zT
          (oldD (sourceEquiv u)) (oldD (sourceEquiv u')) := by
    have h := htargetTransport.symm
    rw [htargetChartPoint] at h
    change
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
          (induced u) (induced u') =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ zT
          (targetCLM (induced u)) (targetCLM (induced u')) at h
    rw [← htargetEquiv_coe] at h
    simpa [induced, oldD] using h
  have hpull := hpullback (sourceEquiv u) (sourceEquiv u')
  rw [← holdD] at hpull
  have hsourceTransport :=
    GeodesicTransport.chartMetric_chartTransitionMFDeriv
      (g := g) (x₀ := x₁) (y₀ := x₀)
      (z := zSource) hySource u u'
  have hsourceTransport' :
      CovariantDerivative.chartMetric g.inner x₀ zM
          (sourceEquiv u) (sourceEquiv u') =
        CovariantDerivative.chartMetric g.inner x₁ zSource u u' := by
    have h := hsourceTransport
    rw [hsourceChartPoint] at h
    change
      CovariantDerivative.chartMetric g.inner x₀ zM
          (sourceCLM u) (sourceCLM u') =
        CovariantDerivative.chartMetric g.inner x₁ zSource u u' at h
    rw [← hsourceEquiv_coe] at h
    exact h
  calc
    CartanMap.targetAnchorBilinForm p₁ (induced u) (induced u') =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
          (induced u) (induced u') := rfl
    _ = CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ zT
          (oldD (sourceEquiv u)) (oldD (sourceEquiv u')) :=
      htargetTransport'
    _ = CovariantDerivative.chartMetric g.inner x₀ zM
          (sourceEquiv u) (sourceEquiv u') := hpull
    _ = CovariantDerivative.chartMetric g.inner x₁ zSource u u' :=
      hsourceTransport'
    _ = CartanMap.sourceAnchorBilinForm g x₁ u u' := rfl

namespace Data

variable {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}
variable {s : ChainState F g} {x₁ : M}

/--
The Cartan-chart derivative field follows from the two endpoint derivatives;
it is exposed separately so callers need not repeat the supplied-family chain
rule.
-/
theorem derived_cartan_chart_derivative (d : Data F s x₁) :
    HasStrictFDerivAt
      (cartanChartMap F g s.anchor s.target s.alignment)
      (CartanLocalIsometry.cartanChartDifferential s.alignment d.A d.B)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor) d.v) := by
  exact
    cartanChartMap_hasStrictFDerivAt_of_charts
      F g s.anchor s.target s.alignment
      d.source_vector_mem d.source_exp_derivative d.target_exp_derivative

/-- The metric-preserving differential induces the next tangent alignment. -/
def alignment (d : Data F s x₁) :
    CartanMap.TangentAlignment g x₁ (s.map x₁) :=
  inducedTangentAlignmentOfCoordinatePullback
    s.alignment d.source_mem_oldChart d.target_mem_oldChart
      d.source_coordinate d.target_coordinate d.metric_pullback

/-- Re-anchor with the differential-induced supplied-family alignment. -/
def successor (d : Data F s x₁) : ChainState F g where
  anchor := x₁
  target := s.map x₁
  alignment := d.alignment

@[simp]
theorem successor_anchor (d : Data F s x₁) : d.successor.anchor = x₁ :=
  rfl

@[simp]
theorem successor_target (d : Data F s x₁) :
    d.successor.target = s.map x₁ :=
  rfl

/-- Convert supplied generic-family data to the existing successor-data API. -/
def toGeneric
    {s : ChainState genericFamily g} {x₁ : M}
    (d : Data genericFamily s x₁) :
    DifferentialInducedSuccessor.Data s.toGeneric x₁ where
  v := d.v
  A := d.A
  B := d.B
  source_vector_mem := d.source_vector_mem
  target_vector_mem := d.target_vector_mem
  source_mem_oldChart := d.source_mem_oldChart
  target_mem_oldChart := d.target_mem_oldChart
  source_coordinate := d.source_coordinate
  target_coordinate := d.target_coordinate
  source_exp_derivative := d.source_exp_derivative
  target_exp_derivative := d.target_exp_derivative
  cartan_chart_derivative := d.cartan_chart_derivative
  metric_pullback := d.metric_pullback

/-- Convert existing successor data into the explicit generic-family API. -/
def ofGeneric
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) :
    Data genericFamily (ChainState.ofGeneric s) x₁ where
  v := d.v
  A := d.A
  B := d.B
  source_vector_mem := d.source_vector_mem
  target_vector_mem := d.target_vector_mem
  source_mem_oldChart := d.source_mem_oldChart
  target_mem_oldChart := d.target_mem_oldChart
  source_coordinate := d.source_coordinate
  target_coordinate := d.target_coordinate
  source_exp_derivative := d.source_exp_derivative
  target_exp_derivative := d.target_exp_derivative
  cartan_chart_derivative := d.cartan_chart_derivative
  metric_pullback := d.metric_pullback

@[simp]
theorem toGeneric_ofGeneric
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) :
    (ofGeneric d).toGeneric = d := by
  cases d
  rfl

@[simp]
theorem ofGeneric_toGeneric
    {s : ChainState genericFamily g} {x₁ : M}
    (d : Data genericFamily s x₁) :
    ofGeneric d.toGeneric = d := by
  cases d
  rfl

end Data

/--
Canonical supplied-family successor data at the predecessor anchor.  The only
target analytic input is the identity strict derivative of the supplied chart
at zero; the metric identity is exactly the stored tangent alignment.
-/
def anchorData
    (F : Family) (hF : F.HasIdentityStrictDerivativeAtZero)
    {g : ClosedSmoothRiemannianMetric 3 M} (s : ChainState F g) :
    Data F s s.anchor where
  v := 0
  A := ContinuousLinearEquiv.refl ℝ E
  B := ContinuousLinearEquiv.refl ℝ E
  source_vector_mem :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) s.anchor
  target_vector_mem := by
    simpa using F.zero_mem_source s.target
  source_mem_oldChart := mem_extChartAt_source s.anchor
  target_mem_oldChart := by
    rw [ChainState.map,
      cartanMap_anchor F g s.anchor s.target s.alignment]
    exact mem_extChartAt_source s.target
  source_coordinate := by
    simpa [extChartAt_coe] using
      (CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
        g s.anchor).symm
  target_coordinate := by
    rw [ChainState.map,
      cartanMap_anchor F g s.anchor s.target s.alignment]
    simpa [F.chart_zero] using
      RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero
        s.target
  source_exp_derivative := by
    simpa [GeodesicTransport.expAtChartOpenPartialHomeomorph] using
      GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
        (g := g) (x₀ := s.anchor)
  target_exp_derivative := by
    simpa using hF s.target
  cartan_chart_derivative := by
    simpa [CartanLocalIsometry.cartanChartDifferential] using
      cartanChartMap_hasStrictFDerivAt_anchor
        F hF g s.anchor s.target s.alignment
  metric_pullback := by
    intro u u'
    have htargetZero :
        F.chart s.target (s.alignment (0 : E)) =
          extChartAt I s.target s.target := by
      rw [map_zero, F.chart_zero]
      exact
        (RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero
          s.target).symm
    have hsourceZero :
        GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) s.anchor (0 : E) =
          extChartAt I s.anchor s.anchor := by
      simpa [extChartAt_coe] using
        CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
          g s.anchor
    rw [htargetZero, hsourceZero]
    simpa [CartanLocalIsometry.cartanChartDifferential,
      CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using
      CartanMap.TangentAlignment.map_app s.alignment u u'

/-- Supplied-family successor data are inhabited at every predecessor anchor. -/
theorem data_nonempty_at_anchor
    (F : Family) (hF : F.HasIdentityStrictDerivativeAtZero)
    {g : ClosedSmoothRiemannianMetric 3 M} (s : ChainState F g) :
    Nonempty (Data F s s.anchor) :=
  ⟨anchorData F hF s⟩

namespace Data

variable {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}
variable {s : ChainState F g} {x₁ : M}

/-- Every supplied successor datum places its new anchor in the old germ. -/
theorem anchor_mem_predecessor_source (d : Data F s x₁) :
    x₁ ∈ s.germ.source := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  have hxchart : x₁ ∈ (chartAt E s.anchor).source := by
    simpa [extChartAt_source] using d.source_mem_oldChart
  have hxcoord : (chartAt E s.anchor) x₁ = eM d.v := by
    simpa [eM, extChartAt_coe] using d.source_coordinate
  have hxexp : (chartAt E s.anchor) x₁ ∈ eM.target := by
    rw [hxcoord]
    exact eM.map_source d.source_vector_mem
  have hinv : eM.symm ((chartAt E s.anchor) x₁) = d.v := by
    rw [hxcoord]
    exact eM.left_inv d.source_vector_mem
  have htargetChart :
      F.chart s.target (s.alignment d.v) ∈ (chartAt E s.target).target := by
    have h := (extChartAt I s.target).map_source d.target_mem_oldChart
    rw [d.target_coordinate] at h
    simpa [extChartAt_target] using h
  simpa [ChainState.germ, openPartialHomeomorph, eM, hinv] using
    ⟨hxchart, hxexp,
      (show d.v ∈
        (CartanMap.tangentAlignmentOpenPartialHomeomorph
          s.alignment).source by
        simp [CartanMap.tangentAlignmentOpenPartialHomeomorph]),
      d.target_vector_mem, htargetChart⟩

end Data

namespace Chain

/-- A realized differential-induced chain for a supplied target family. -/
structure ReachableChain
    (F : Family) {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : ChainState F g) where
  state : ℕ → ChainState F g
  initial_eq : state 0 = initial
  data : ∀ n : ℕ, Data F (state n) (nodes (n + 1))
  successor_eq : ∀ n : ℕ, state (n + 1) = (data n).successor

@[simp]
theorem ReachableChain.state_zero
    {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes : ℕ → M} {initial : ChainState F g}
    (chain : ReachableChain F nodes initial) :
    chain.state 0 = initial :=
  chain.initial_eq

@[simp]
theorem ReachableChain.state_succ
    {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes : ℕ → M} {initial : ChainState F g}
    (chain : ReachableChain F nodes initial) (n : ℕ) :
    chain.state (n + 1) = (chain.data n).successor :=
  chain.successor_eq n

@[simp]
theorem ReachableChain.state_succ_anchor
    {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes : ℕ → M} {initial : ChainState F g}
    (chain : ReachableChain F nodes initial) (n : ℕ) :
    (chain.state (n + 1)).anchor = nodes (n + 1) := by
  rw [chain.state_succ]
  exact (chain.data n).successor_anchor

/--
Build a supplied-family reachable chain from data available only at correctly
anchored states.  The recursion queries the one state it actually reaches.
-/
noncomputable def reachableChain_of_anchored_step_supply
    (F : Family) {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : ChainState F g)
    (hinitial : initial.anchor = nodes 0)
    (hstep : ∀ (n : ℕ) (s : ChainState F g),
      s.anchor = nodes n → Nonempty (Data F s (nodes (n + 1)))) :
    ReachableChain F nodes initial := by
  classical
  let stepData : ∀ (n : ℕ) (s : ChainState F g),
      s.anchor = nodes n → Data F s (nodes (n + 1)) := by
    intro n s hs
    exact Classical.choice (hstep n s hs)
  let state : ∀ n : ℕ, {s : ChainState F g // s.anchor = nodes n} := by
    intro n
    induction n with
    | zero => exact ⟨initial, hinitial⟩
    | succ n state_n =>
        let d := stepData n state_n.1 state_n.2
        exact ⟨d.successor, d.successor_anchor⟩
  refine
    { state := fun n => (state n).1
      initial_eq := rfl
      data := fun n => stepData n (state n).1 (state n).2
      successor_eq := ?_ }
  intro n
  rfl

end Chain

end ChainStateAndData

section ProofBearingSuccessorNeighborhood

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/--
The supplied-family locus where successor data exist for every tangent
alignment at the displayed source and target anchors.
-/
def UniversalSuccessorDataLocus
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M) :
    Set ((M × RoundSphere3) × M) :=
  {q | ∀ L : CartanMap.TangentAlignment g q.1.1 q.1.2,
    Nonempty (Data F (ChainState.mk q.1.1 q.1.2 L) q.2)}

/-- The compact graph of the source anchor in successor parameter space. -/
def successorParameterDiagonal : Set ((M × RoundSphere3) × M) :=
  (fun xp : M × RoundSphere3 ↦ (xp, xp.1)) '' Set.univ

theorem isCompact_successorParameterDiagonal :
    IsCompact (successorParameterDiagonal (M := M)) := by
  exact isCompact_univ.image (continuous_id.prodMk continuous_fst)

/-- Identity derivatives put the complete diagonal in the supplied data locus. -/
theorem successorParameterDiagonal_subset_universalSuccessorDataLocus
    (F : Family) (hF : F.HasIdentityStrictDerivativeAtZero)
    (g : ClosedSmoothRiemannianMetric 3 M) :
    successorParameterDiagonal (M := M) ⊆ UniversalSuccessorDataLocus F g := by
  rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
  intro L
  exact data_nonempty_at_anchor F hF (ChainState.mk x p L)

/--
The weakest proof-bearing joint stability contract: supplied successor data
form a neighborhood of the complete source-target diagonal.
-/
def UniversalSuccessorDataNeighborhood
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  UniversalSuccessorDataLocus F g ∈
    𝓝ˢ (successorParameterDiagonal (M := M))

/-- Global openness of the supplied data locus implies the neighborhood contract. -/
theorem universalSuccessorDataNeighborhood_of_isOpen
    (F : Family) (hF : F.HasIdentityStrictDerivativeAtZero)
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hopen : IsOpen (UniversalSuccessorDataLocus F g)) :
    UniversalSuccessorDataNeighborhood F g := by
  exact hopen.mem_nhdsSet.mpr
    (successorParameterDiagonal_subset_universalSuccessorDataLocus F hF g)

/--
The complete proof-bearing target-family contract.  `targetRegular` controls
the varying target charts and gives their uniform coordinate domains;
`dataNeighborhood` is the additional geometric/analytic content (strict
endpoint derivatives and metric pullback) that domain regularity alone cannot
produce.
-/
structure ProofBearingSuccessorContract
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  targetRegular : F.JointlyRegular
  targetIdentityDerivative : F.HasIdentityStrictDerivativeAtZero
  dataNeighborhood : UniversalSuccessorDataNeighborhood F g

/--
Compactness turns the supplied-family diagonal-neighborhood contract into one
metric successor radius uniform in source anchor, sphere target, and tangent
alignment.
-/
theorem exists_uniform_successor_data_radius_of_universalNeighborhood
    (F : Family) (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorDataNeighborhood F g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty (Data F (ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      (Metric.hasBasis_nhdsSet_cthickening
        (isCompact_successorParameterDiagonal (M := M))).mem_iff.mp
        hneighborhood with
    ⟨epsilon, hepsilon, hthick⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro x p L z hdist
  let graphPoint : (M × RoundSphere3) × M := ((x, p), x)
  have hgraphPoint :
      graphPoint ∈ successorParameterDiagonal (M := M) := by
    exact ⟨(x, p), Set.mem_univ _, rfl⟩
  have hmem :
      ((x, p), z) ∈
        Metric.cthickening epsilon
          (successorParameterDiagonal (M := M)) := by
    apply Metric.mem_cthickening_of_dist_le
      (((x, p), z) : (M × RoundSphere3) × M) graphPoint epsilon
        (successorParameterDiagonal (M := M)) hgraphPoint
    simpa [graphPoint, Prod.dist_eq] using le_of_lt hdist
  exact (hthick hmem) L

/-- The bundled proof-bearing contract supplies the global successor radius. -/
theorem ProofBearingSuccessorContract.exists_uniform_successor_data_radius
    {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}
    (C : ProofBearingSuccessorContract F g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty (Data F (ChainState.mk x p L) z) :=
  exists_uniform_successor_data_radius_of_universalNeighborhood
    F g C.dataNeighborhood

/--
Canonical-family specialization.  Its joint target regularity and identity
derivative are discharged, leaving only the honest supplied-family
successor-data neighborhood as proof-bearing input.
-/
def canonicalProofBearingSuccessorContract
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorDataNeighborhood canonicalFamily g) :
    ProofBearingSuccessorContract canonicalFamily g where
  targetRegular := canonicalFamily_jointlyRegular
  targetIdentityDerivative := canonicalFamily_hasIdentityStrictDerivativeAtZero
  dataNeighborhood := hneighborhood

/--
A rooted path-chain realization whose states, data, and successors all use the
supplied target exponential family.
-/
structure SuppliedRootedPathChainRealization
    (F : Family) {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton :
      CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g) where
  nodeTime : M → ℕ → unitInterval
  nodeTime_zero : ∀ x : M, nodeTime x 0 = 0
  terminalIndex : M → ℕ
  nodeTime_terminal : ∀ x : M, nodeTime x (terminalIndex x) = 1
  chain : ∀ x : M,
    Chain.ReachableChain F
      (fun n ↦ skeleton.path x (nodeTime x n))
      (ChainState.retarget F skeleton.root)

/--
One globally uniform supplied-data radius realizes every rooted path with any
prescribed positive metric mesh.  The subdivision is selected independently
on each compact path, while the recursively built chain queries data only at
its actually reached state.
-/
theorem exists_suppliedRootedPathChainRealization_with_prescribed_mesh_of_uniformRadius
    (F : Family) {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton :
      CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdata :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (p : RoundSphere3)
          (L : CartanMap.TangentAlignment g x p) (z : M),
          dist z x < epsilon →
            Nonempty (Data F (ChainState.mk x p L) z))
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : SuppliedRootedPathChainRealization F skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let radius : ℝ := min epsilon mesh
  have hradius : 0 < radius := lt_min hepsilon hmesh
  have hpath : ∀ x : M,
      ∃ (t : ℕ → unitInterval) (k : ℕ),
        0 < k ∧
          t 0 = 0 ∧
            Monotone t ∧
              (∀ n ≥ k, t n = 1) ∧
                (∀ n : ℕ,
                  dist (skeleton.path x (t n))
                    (skeleton.path x (t (n + 1))) < mesh) ∧
                  Nonempty
                    (Chain.ReachableChain F
                      (fun n ↦ skeleton.path x (t n))
                      (ChainState.retarget F skeleton.root)) := by
    intro x
    rcases CartanChain.exists_monotone_unitInterval_subdivision_dist_lt
        (γ := (skeleton.path x).toContinuousMap) hradius with
      ⟨t, htzero, htmono, ⟨m, hterminal⟩, hclose⟩
    let k : ℕ := max m 1
    have hmk : m ≤ k := le_max_left _ _
    have honeK : 1 ≤ k := le_max_right _ _
    have hk : 0 < k := Nat.zero_lt_one.trans_le honeK
    have htone : ∀ n ≥ k, t n = 1 := by
      intro n hn
      exact hterminal n (hmk.trans hn)
    have hsmall : ∀ n : ℕ,
        dist (skeleton.path x (t n))
            (skeleton.path x (t (n + 1))) < mesh := by
      intro n
      exact (hclose n).trans_le (min_le_right _ _)
    have hstep : ∀ (n : ℕ) (s : ChainState F g),
        s.anchor = skeleton.path x (t n) →
          Nonempty (Data F s (skeleton.path x (t (n + 1)))) := by
      intro n s hs
      have hdist :
          dist (skeleton.path x (t (n + 1))) s.anchor < epsilon := by
        rw [hs]
        simpa [dist_comm] using
          (hclose n).trans_le (min_le_left epsilon mesh)
      have hd := hdata s.anchor s.target s.alignment
        (skeleton.path x (t (n + 1))) hdist
      have heta : ChainState.mk s.anchor s.target s.alignment = s := by
        cases s
        rfl
      simpa [heta] using hd
    have hinitial :
        (ChainState.retarget F skeleton.root).anchor =
          skeleton.path x (t 0) := by
      rw [htzero]
      simp
    let chain : Chain.ReachableChain F
        (fun n ↦ skeleton.path x (t n))
        (ChainState.retarget F skeleton.root) :=
      Chain.reachableChain_of_anchored_step_supply
        F (fun n ↦ skeleton.path x (t n))
          (ChainState.retarget F skeleton.root) hinitial hstep
    exact ⟨t, k, hk, htzero, htmono, htone, hsmall, ⟨chain⟩⟩
  choose t k hk htzero htmono htone hsmall hchain using hpath
  let realization : SuppliedRootedPathChainRealization F skeleton :=
    { nodeTime := t
      nodeTime_zero := htzero
      terminalIndex := k
      nodeTime_terminal := fun x ↦ htone x (k x) le_rfl
      chain := fun x ↦ Classical.choice (hchain x) }
  exact ⟨realization, hk, htmono, htone, hsmall⟩

/--
The proof-bearing supplied-family diagonal neighborhood gives complete rooted
prescribed-mesh realization.
-/
theorem exists_suppliedRootedPathChainRealization_with_prescribed_mesh_of_universalNeighborhood
    (F : Family) {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton :
      CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (hneighborhood : UniversalSuccessorDataNeighborhood F g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : SuppliedRootedPathChainRealization F skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_successor_data_radius_of_universalNeighborhood
      F g hneighborhood with
    ⟨epsilon, hepsilon, hdata⟩
  exact
    exists_suppliedRootedPathChainRealization_with_prescribed_mesh_of_uniformRadius
      F skeleton hepsilon hdata mesh hmesh

/-- The bundled proof-bearing contract realizes every prescribed mesh. -/
theorem ProofBearingSuccessorContract.exists_suppliedRootedPathChainRealization_with_prescribed_mesh
    {F : Family} {g : ClosedSmoothRiemannianMetric 3 M}
    (C : ProofBearingSuccessorContract F g)
    (skeleton :
      CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : SuppliedRootedPathChainRealization F skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh :=
  exists_suppliedRootedPathChainRealization_with_prescribed_mesh_of_universalNeighborhood
    F skeleton C.dataNeighborhood mesh hmesh

/--
Canonical-family proof-bearing completion.  Joint target regularity and the
identity derivative are automatic; the sole remaining premise is the honest
successor-data neighborhood for the normalized family.
-/
theorem exists_canonicalRootedPathChainRealization_with_prescribed_mesh
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton :
      CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (hneighborhood :
      UniversalSuccessorDataNeighborhood canonicalFamily g)
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
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh :=
  (canonicalProofBearingSuccessorContract g hneighborhood).exists_suppliedRootedPathChainRealization_with_prescribed_mesh
    skeleton mesh hmesh

end ProofBearingSuccessorNeighborhood

end CartanTargetExponential
end Poincare
