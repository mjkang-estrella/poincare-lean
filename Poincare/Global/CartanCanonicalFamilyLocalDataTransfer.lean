import Poincare.Global.RoundSphereGenericExponentialAnchorIndependence
import Poincare.Global.CartanTargetExponentialFamily
import Poincare.Global.CartanAtlasRootedPathCurvatureSuccessorRadius

/-!
# Local transfer of Cartan successor data to the canonical target family

The generic and reference-normalized round-sphere exponential charts have the
same germ at zero.  This module uses that germ equality at the actual aligned
target vector to transfer generic `DifferentialInducedSuccessor.Data` to
`CartanTargetExponential.Data canonicalFamily`.

The equality must hold on a neighborhood of the aligned vector, not merely at
zero: strict Frechet derivatives are transferred by eventual equality at that
point.  We therefore first keep the aligned vector strictly inside an open
chart-equality ball.  The target metric-pullback identity then transfers by
equality of the target coordinate value, and the supplied-family Cartan
derivative is rebuilt from the two endpoint derivatives.

Constant curvature consequently gives canonical-family successor data on a
vertical neighborhood for every fixed source-target anchor pair, uniformly
over all tangent alignments.  This does not assert a radius uniform in the
anchor parameters; the supplied-family diagonal-neighborhood compactness
theorem should only be applied after genuine joint neighborhood stability has
been established.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyLocalDataTransfer

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential

/-- At a fixed target anchor, the generic and canonical target charts agree
on a positive coordinate ball. -/
theorem exists_genericFamily_chart_eq_canonicalFamily_on_ball
    (p : RoundSphere3) :
    ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
      genericFamily.chart p v = canonicalFamily.chart p v := by
  rcases
      RoundSphereGenericExponentialAnchorIndependence.exists_chart_expAt_eq_coordinateLocalHomeomorph_on_ball
        p with
    ⟨r, hr, h⟩
  refine ⟨r, hr, ?_⟩
  intro v hv
  simpa [genericFamily, canonicalFamily,
    RoundSphereCanonicalExponential.chartOpenPartialHomeomorph,
    GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using h v hv

/-- The joint locus where the independently chosen generic target chart and
the reference-normalized target chart have the same value.

The fixed-anchor theorem above says that every vertical fiber of this locus
contains a ball about zero.  Local uniformity in the target anchor is exactly
the additional assertion that this locus is a neighborhood of `(p, 0)`.
-/
def genericCanonicalChartAgreementLocus : Set (RoundSphere3 × E) :=
  {q | genericFamily.chart q.1 q.2 = canonicalFamily.chart q.1 q.2}

@[simp]
theorem mem_genericCanonicalChartAgreementLocus_iff
    (p : RoundSphere3) (v : E) :
    (p, v) ∈ genericCanonicalChartAgreementLocus ↔
      genericFamily.chart p v = canonicalFamily.chart p v :=
  Iff.rfl

/-- The entire zero section belongs to the joint chart-agreement locus. -/
theorem zero_mem_genericCanonicalChartAgreementLocus
    (p : RoundSphere3) :
    (p, (0 : E)) ∈ genericCanonicalChartAgreementLocus := by
  change genericFamily.chart p (0 : E) = canonicalFamily.chart p (0 : E)
  rw [genericFamily.chart_zero, canonicalFamily.chart_zero]

/-- Every fixed-anchor vertical fiber contains a positive ball about zero.

This is the strongest anchorwise consequence of the current generic
fixed-time API.  It deliberately makes no claim that the radii persist when
the target anchor moves.
-/
theorem exists_vertical_ball_subset_genericCanonicalChartAgreementLocus
    (p : RoundSphere3) :
    ∃ r > (0 : ℝ),
      ({p} ×ˢ Metric.ball (0 : E) r) ⊆
        genericCanonicalChartAgreementLocus := by
  rcases exists_genericFamily_chart_eq_canonicalFamily_on_ball p with
    ⟨r, hr, hEq⟩
  refine ⟨r, hr, ?_⟩
  rintro ⟨q, v⟩ ⟨hq, hv⟩
  have hqp : q = p := Set.mem_singleton_iff.mp hq
  subst q
  apply hEq v
  simpa [Metric.mem_ball, dist_eq_norm] using hv

/-- A genuine joint neighborhood of chart agreement gives a radius that is
locally uniform in the target anchor.

For the present independently chosen `genericFamily`, the hypothesis is the
single missing fact: its fixed-time construction supplies unrelated positive
time and velocity radii at different anchors, so the existing API does not
show that the agreement locus is a neighborhood of `(p, 0)`.
-/
theorem exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_nhds
    (p : RoundSphere3)
    (hJoint : genericCanonicalChartAgreementLocus ∈
      𝓝 (p, (0 : E))) :
    ∃ U : Set RoundSphere3, U ∈ 𝓝 p ∧
      ∃ r > (0 : ℝ), ∀ q ∈ U, ∀ v : E, ‖v‖ < r →
        genericFamily.chart q v = canonicalFamily.chart q v := by
  rcases mem_nhds_prod_iff.mp hJoint with
    ⟨U, hU, V, hV, hUV⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨r, hr, hball⟩
  refine ⟨U, hU, r, hr, ?_⟩
  intro q hq v hv
  have hvBall : v ∈ Metric.ball (0 : E) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hmem : (q, v) ∈ genericCanonicalChartAgreementLocus :=
    hUV ⟨hq, hball hvBall⟩
  exact (mem_genericCanonicalChartAgreementLocus_iff q v).mp hmem

/-- Neighborhood membership of the joint agreement locus is exactly the
desired target-anchor locally uniform ball statement.  Thus the remaining
gap is topological, rather than another fixed-anchor ODE comparison. -/
theorem genericCanonicalChartAgreementLocus_mem_nhds_iff
    (p : RoundSphere3) :
    genericCanonicalChartAgreementLocus ∈ 𝓝 (p, (0 : E)) ↔
      ∃ U : Set RoundSphere3, U ∈ 𝓝 p ∧
        ∃ r > (0 : ℝ), ∀ q ∈ U, ∀ v : E, ‖v‖ < r →
          genericFamily.chart q v = canonicalFamily.chart q v := by
  constructor
  · exact
      exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_nhds
        p
  · rintro ⟨U, hU, r, hr, hEq⟩
    apply mem_of_superset
      (prod_mem_nhds hU (Metric.ball_mem_nhds (0 : E) hr))
    rintro ⟨q, v⟩ ⟨hq, hv⟩
    apply (mem_genericCanonicalChartAgreementLocus_iff q v).mpr
    apply hEq q hq v
    simpa [Metric.mem_ball, dist_eq_norm] using hv

/-- Interior membership is the pointwise topological form of the one missing
joint-neighborhood fact needed for local target-anchor uniformity. -/
theorem exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_interior
    (p : RoundSphere3)
    (hJoint : (p, (0 : E)) ∈
      interior genericCanonicalChartAgreementLocus) :
    ∃ U : Set RoundSphere3, U ∈ 𝓝 p ∧
      ∃ r > (0 : ℝ), ∀ q ∈ U, ∀ v : E, ‖v‖ < r →
        genericFamily.chart q v = canonicalFamily.chart q v := by
  apply
    exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_nhds
      p
  exact mem_interior_iff_mem_nhds.mp hJoint

/-- In particular, openness of the full joint agreement locus discharges the
target-anchor local-uniformity gap at every anchor. -/
theorem exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_isOpen
    (hOpen : IsOpen genericCanonicalChartAgreementLocus)
    (p : RoundSphere3) :
    ∃ U : Set RoundSphere3, U ∈ 𝓝 p ∧
      ∃ r > (0 : ℝ), ∀ q ∈ U, ∀ v : E, ‖v‖ < r →
        genericFamily.chart q v = canonicalFamily.chart q v := by
  apply
    exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_nhds
      p
  exact hOpen.mem_nhds (zero_mem_genericCanonicalChartAgreementLocus p)

/-- A point strictly inside a chart-equality ball has a full neighborhood on
which the generic and canonical target charts agree. -/
theorem genericFamily_chart_eventuallyEq_canonicalFamily_of_norm_lt
    {p : RoundSphere3} {r : ℝ}
    (hEq : ∀ v : E, ‖v‖ < r →
      genericFamily.chart p v = canonicalFamily.chart p v)
    {v : E} (hv : ‖v‖ < r) :
    (genericFamily.chart p : E → E) =ᶠ[𝓝 v]
      (canonicalFamily.chart p : E → E) := by
  have hvBall : v ∈ Metric.ball (0 : E) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  filter_upwards [(Metric.isOpen_ball.mem_nhds hvBall)] with w hw
  apply hEq w
  simpa [Metric.mem_ball, dist_eq_norm] using hw

/-- Transfer one generic successor datum to the canonical target family once
the target chart germ agrees at the aligned vector and that vector belongs to
the canonical chart source. -/
def transferData
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    (htargetCanonical :
      s.alignment d.v ∈ (canonicalFamily.chart s.target).source)
    (hchart :
      (genericFamily.chart s.target : E → E) =ᶠ[𝓝 (s.alignment d.v)]
        (canonicalFamily.chart s.target : E → E)) :
    CartanTargetExponential.Data canonicalFamily
      (CartanTargetExponential.ChainState.retarget canonicalFamily s) z := by
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) s.anchor
  let sc : CartanTargetExponential.ChainState canonicalFamily g :=
    CartanTargetExponential.ChainState.retarget canonicalFamily s
  have hsourceCoordinate : (chartAt E s.anchor) z = eM d.v := by
    simpa [eM, extChartAt_coe] using d.source_coordinate
  have hnormal : eM.symm ((chartAt E s.anchor) z) = d.v := by
    rw [hsourceCoordinate]
    exact eM.left_inv d.source_vector_mem
  have htargetValue :
      genericFamily.chart s.target (s.alignment d.v) =
        canonicalFamily.chart s.target (s.alignment d.v) :=
    hchart.self_of_nhds
  have htargetValue' :
      GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) s.target (s.alignment d.v) =
        canonicalFamily.chart s.target (s.alignment d.v) := by
    simpa [genericFamily] using htargetValue
  have hmap : sc.map z = s.map z := by
    change
      (chartAt E s.target).symm
          (canonicalFamily.chart s.target
            (s.alignment (eM.symm ((chartAt E s.anchor) z)))) =
        (chartAt E s.target).symm
          (genericFamily.chart s.target
            (s.alignment (eM.symm ((chartAt E s.anchor) z))))
    rw [hnormal, htargetValue]
  have htargetStrict :
      HasStrictFDerivAt (canonicalFamily.chart s.target)
        (d.B : E →L[ℝ] E) (s.alignment d.v) :=
    d.target_exp_derivative.congr_of_eventuallyEq hchart
  refine
    { v := d.v
      A := d.A
      B := d.B
      source_vector_mem := d.source_vector_mem
      target_vector_mem := htargetCanonical
      source_mem_oldChart := d.source_mem_oldChart
      target_mem_oldChart := ?_
      source_coordinate := d.source_coordinate
      target_coordinate := ?_
      source_exp_derivative := d.source_exp_derivative
      target_exp_derivative := htargetStrict
      cartan_chart_derivative := ?_
      metric_pullback := ?_ }
  · rw [hmap]
    exact d.target_mem_oldChart
  · calc
      extChartAt I sc.target (sc.map z) =
          extChartAt I s.target (s.map z) := by
            simpa [sc] using congrArg (fun y ↦ extChartAt I s.target y) hmap
      _ = genericFamily.chart s.target (s.alignment d.v) := by
        simpa [genericFamily] using d.target_coordinate
      _ = canonicalFamily.chart sc.target (sc.alignment d.v) := by
        simpa [sc] using htargetValue
  · exact
      CartanTargetExponential.cartanChartMap_hasStrictFDerivAt_of_charts
        canonicalFamily g s.anchor s.target s.alignment
        d.source_vector_mem d.source_exp_derivative htargetStrict
  · intro u u'
    change
      CovariantDerivative.chartMetric roundSphereMetric3.inner s.target
          (canonicalFamily.chart s.target (s.alignment d.v))
          (CartanLocalIsometry.cartanChartDifferential
            s.alignment d.A d.B u)
          (CartanLocalIsometry.cartanChartDifferential
            s.alignment d.A d.B u') =
        CovariantDerivative.chartMetric g.inner s.anchor
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) s.anchor d.v) u u'
    rw [← htargetValue']
    exact d.metric_pullback u u'

/-- Ball-form wrapper around `transferData`. -/
def transferData_of_aligned_norm_lt
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    {r : ℝ}
    (hEq : ∀ v : E, ‖v‖ < r →
      genericFamily.chart s.target v = canonicalFamily.chart s.target v)
    (hsource : Metric.ball (0 : E) r ⊆
      (canonicalFamily.chart s.target).source)
    (haligned : ‖s.alignment d.v‖ < r) :
    CartanTargetExponential.Data canonicalFamily
      (CartanTargetExponential.ChainState.retarget canonicalFamily s) z := by
  apply transferData d
  · apply hsource
    simpa [Metric.mem_ball, dist_eq_norm] using haligned
  · exact
      genericFamily_chart_eventuallyEq_canonicalFamily_of_norm_lt hEq haligned

section Curvature

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- For fixed source and target anchors, constant curvature gives one ordinary
metric neighborhood on which canonical-family successor data exist for every
tangent alignment.

The radius is not asserted to vary continuously with either anchor. -/
theorem exists_metric_canonical_successor_data_radius_all_alignments_fixed_anchors_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty
            (CartanTargetExponential.Data canonicalFamily
              (CartanTargetExponential.ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      CartanAtlasRootedPathCurvatureSuccessorRadius.exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨genericRadius, hgenericRadius, hgenericData⟩
  rcases exists_genericFamily_chart_eq_canonicalFamily_on_ball p with
    ⟨equalityRadius, hequalityRadius, hchartEq⟩
  rcases RoundSphereCanonicalExponential.exists_uniform_source_target_ball with
    ⟨canonicalRadius, hcanonicalRadius, hcanonicalBalls⟩
  let targetRadius : ℝ := min equalityRadius canonicalRadius
  have htargetRadius : 0 < targetRadius := by
    dsimp [targetRadius]
    exact lt_min hequalityRadius hcanonicalRadius
  have hchartEqTarget : ∀ v : E, ‖v‖ < targetRadius →
      genericFamily.chart p v = canonicalFamily.chart p v := by
    intro v hv
    exact hchartEq v (hv.trans_le (by
      dsimp [targetRadius]
      exact min_le_left _ _))
  have hcanonicalSource : Metric.ball (0 : E) targetRadius ⊆
      (canonicalFamily.chart p).source := by
    intro v hv
    have hv' : v ∈ Metric.ball (0 : E) canonicalRadius :=
      Metric.ball_subset_ball (by
        dsimp [targetRadius]
        exact min_le_right _ _) hv
    simpa [canonicalFamily] using (hcanonicalBalls p).1 hv'
  rcases
      RoundSphereTargetAnchorUniformity.exists_pos_uniform_tangentAlignment_operatorNorm_bound_all_targets
        g x with
    ⟨C, hC, hoperator⟩
  let vectorRadius : ℝ := targetRadius / C
  have hvectorRadius : 0 < vectorRadius :=
    div_pos htargetRadius hC
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
  let normalCoordinate : M → E := fun z ↦ eM.symm ((chartAt E x) z)
  have htarget : (chartAt E x) x ∈ eM.target := by
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  have hchart : ContinuousAt (fun z : M ↦ (chartAt E x) z) x := by
    simpa [extChartAt_coe] using
      continuousAt_extChartAt («I» := I) x
  have hnormalContinuous : ContinuousAt normalCoordinate x :=
    (eM.continuousAt_symm htarget).comp hchart
  have hnormalZero : normalCoordinate x = (0 : E) := by
    simpa [normalCoordinate, eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x
  have hnormalNhds :
      normalCoordinate ⁻¹' Metric.ball (0 : E) vectorRadius ∈ 𝓝 x := by
    apply hnormalContinuous.preimage_mem_nhds
    rw [hnormalZero]
    exact Metric.ball_mem_nhds (0 : E) hvectorRadius
  rcases Metric.mem_nhds_iff.mp hnormalNhds with
    ⟨coordinateRadius, hcoordinateRadius, hcoordinate⟩
  let epsilon : ℝ := min genericRadius coordinateRadius
  have hepsilon : 0 < epsilon :=
    lt_min hgenericRadius hcoordinateRadius
  refine ⟨epsilon, hepsilon, ?_⟩
  intro L z hdist
  have hgenericDist : dist z x < genericRadius :=
    hdist.trans_le (by dsimp [epsilon]; exact min_le_left _ _)
  rcases hgenericData L z hgenericDist with ⟨d⟩
  have hzCoordinateBall : z ∈ Metric.ball x coordinateRadius := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (by dsimp [epsilon]; exact min_le_right _ _)
  have hnormalBall :
      normalCoordinate z ∈ Metric.ball (0 : E) vectorRadius :=
    hcoordinate hzCoordinateBall
  have hnormalNorm : ‖normalCoordinate z‖ < vectorRadius := by
    simpa [Metric.mem_ball, dist_eq_norm] using hnormalBall
  have hsourceCoordinate : (chartAt E x) z = eM d.v := by
    simpa [eM, extChartAt_coe] using d.source_coordinate
  have hdv : d.v = normalCoordinate z := by
    calc
      d.v = eM.symm (eM d.v) := (eM.left_inv d.source_vector_mem).symm
      _ = eM.symm ((chartAt E x) z) := by rw [hsourceCoordinate]
      _ = normalCoordinate z := rfl
  have hdvNorm : ‖d.v‖ < vectorRadius := by
    rw [hdv]
    exact hnormalNorm
  let A : E →L[ℝ] E :=
    L.toContinuousLinearEquiv.toContinuousLinearMap
  have haligned : ‖L d.v‖ < targetRadius := by
    calc
      ‖L d.v‖ = ‖A d.v‖ := rfl
      _ ≤ ‖A‖ * ‖d.v‖ := A.le_opNorm d.v
      _ ≤ C * ‖d.v‖ := by
        exact mul_le_mul_of_nonneg_right (hoperator p L) (norm_nonneg d.v)
      _ < C * vectorRadius := mul_lt_mul_of_pos_left hdvNorm hC
      _ = targetRadius := by
        dsimp only [vectorRadius]
        exact mul_div_cancel₀ targetRadius (ne_of_gt hC)
  refine ⟨?_⟩
  simpa [CartanTargetExponential.ChainState.retarget] using
    transferData_of_aligned_norm_lt d hchartEqTarget hcanonicalSource haligned

/-- Constant curvature proves the complete vertical section of the canonical
supplied-family successor-data neighborhood statement at every fixed
source-target pair. -/
theorem canonical_universalSuccessorDataLocus_vertical_mem_nhds_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    {z : M |
      ((x, p), z) ∈
        CartanTargetExponential.UniversalSuccessorDataLocus
          canonicalFamily g} ∈ 𝓝 x := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_metric_canonical_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨epsilon, hepsilon, hdata⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hepsilon) ?_
  intro z hz L
  apply hdata L z
  simpa [Metric.mem_ball] using hz

end Curvature

end CartanCanonicalFamilyLocalDataTransfer
end Poincare
