import Poincare.Global.CartanAtlasRootedPathAdaptiveMeshRealization
import Poincare.Global.CartanChainRigidity
import Poincare.Global.DifferentialSuccessorAdaptiveMeshCoordinates
import Poincare.Global.DifferentialSuccessorZero
import Poincare.Global.UniformTangentAlignmentDifferentialField
import Poincare.Global.RoundSphereTargetAnchorUniformity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Curvature successor radii for rooted path realization

Constant curvature supplies differential-successor data on a state-dependent
normal-coordinate ball.  This module first converts that statement into an
ordinary positive metric radius around the anchor of every actual Cartan
state.  The conversion uses only openness of the state's strict Cartan source
and continuity of the inverse source normal coordinate.

Those radii are automatic but initially depend on the complete continuation
state.  Compactness of the tangent-alignment fiber removes the alignment
dependence: for each pair of source and target anchors, one ordinary metric
radius works for every alignment.  The rooted prescribed-mesh theorem needs a
radius that can be selected before the recursively reached state is known.  We
isolate the exact remaining uniformity: a positive lower-semicontinuous
function on source anchors which minorizes the automatic curvature radius for
every pair of source and target anchors.  Lower semicontinuity makes this
anchor radius locally stable.  A triangle estimate then produces the
history-compatible pointwise path radii consumed by
`CartanAtlasRootedPathAdaptiveMeshRealization`.

Thus no `StepAvailable` policy and no constant-target or constant-basepoint
specialization occurs here.  The only residual hypothesis is a one-variable
anchor minorant uniform over the sphere target.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanAtlasRootedPathCurvatureSuccessorRadius

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanAtlasRootedPathSkeleton
open CartanAtlasRootedPathAdaptiveMeshRealization
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/--
For fixed source and target anchors, one ordinary metric ball around the
source anchor lies in the strict Cartan source for every tangent alignment.

The source inverse-normal-coordinate neighborhood is independent of the
alignment.  Compactness of the fixed-anchor alignment fiber gives a common
operator-norm bound, so a sufficiently small source vector is sent into one
fixed target exponential source ball for every alignment.  The final sphere
chart contributes no restriction because every stereographic target is
`univ`.
-/
theorem exists_metric_ball_subset_germ_source_all_alignments_fixed_anchors
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : Real),
      ∀ L : CartanMap.TangentAlignment g x p,
        Metric.ball x epsilon ⊆
          (CartanChain.ChainState.mk x p L).germ.source := by
  letI : MetricSpace M := g.toMetricSpace
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) x
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p
  let sourceNormal : OpenPartialHomeomorph M E :=
    (chartAt E x).trans eM.symm
  have hxSourceNormal : x ∈ sourceNormal.source := by
    change x ∈ (chartAt E x).source ∩ (chartAt E x) ⁻¹' eM.target
    refine ⟨mem_chart_source E x, ?_⟩
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  rcases CartanMap.exists_pos_uniform_tangentAlignment_operatorNorm_bound
      g x p with
    ⟨C, hC, hoperator⟩
  have hzeroTarget : (0 : E) ∈ eS.source := by
    exact
      GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
        (g := roundSphereMetric3) p
  rcases Metric.mem_nhds_iff.mp
      (eS.open_source.mem_nhds hzeroTarget) with
    ⟨targetRadius, htargetRadius, htargetBall⟩
  let vectorRadius : Real := targetRadius / C
  have hvectorRadius : 0 < vectorRadius :=
    div_pos htargetRadius hC
  let normalCoordinate : M → E := fun z => sourceNormal z
  have hnormal : ContinuousAt normalCoordinate x := by
    exact sourceNormal.continuousAt hxSourceNormal
  have hnormalZero : normalCoordinate x = (0 : E) := by
    change eM.symm ((chartAt E x) x) = (0 : E)
    simpa [eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero
        g x
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
  intro L z hz
  have hzControlled := hcontrolled hz
  have hzSourceNormal :
      z ∈ (chartAt E x).source ∧ (chartAt E x) z ∈ eM.target := by
    simpa [sourceNormal] using hzControlled.1
  let v : E := normalCoordinate z
  have hv : ‖v‖ < vectorRadius := by
    simpa [v, Metric.mem_ball, dist_eq_norm] using hzControlled.2
  let A : E →L[Real] E :=
    L.toContinuousLinearEquiv.toContinuousLinearMap
  have hLv : ‖L v‖ < targetRadius := by
    calc
      ‖L v‖ = ‖A v‖ := rfl
      _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ C * ‖v‖ :=
        mul_le_mul_of_nonneg_right (hoperator L) (norm_nonneg v)
      _ < C * vectorRadius := mul_lt_mul_of_pos_left hv hC
      _ = targetRadius := by
        dsimp only [vectorRadius]
        exact mul_div_cancel₀ targetRadius (ne_of_gt hC)
  have hLvSource : L v ∈ eS.source := by
    apply htargetBall
    simpa [Metric.mem_ball, dist_eq_norm] using hLv
  have htargetChart :
      (chartAt E p)
          (GeodesicTransport.expAt roundSphereMetric3 p (L v)) ∈
        (chartAt E p).target := by
    have h : extChartAt I p
          (GeodesicTransport.expAt roundSphereMetric3 p (L v)) ∈
        (extChartAt I p).target := by
      rw [RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_target_eq_univ]
      exact Set.mem_univ _
    simpa [extChartAt_coe, extChartAt_target] using h
  have hvAlignment :
      v ∈ (CartanMap.tangentAlignmentOpenPartialHomeomorph L).source := by
    simp [CartanMap.tangentAlignmentOpenPartialHomeomorph]
  simpa [CartanChain.ChainState.germ, CartanMap.openPartialHomeomorph,
    sourceNormal, normalCoordinate, eM, eS, v] using
    ⟨hzSourceNormal.1, hzSourceNormal.2, hvAlignment, hLvSource,
      htargetChart⟩

/--
For fixed source and target anchors, constant curvature gives one positive
source normal-coordinate radius on which differential-successor data exist
for every tangent alignment.  Membership in the corresponding strict Cartan
source remains explicit here; the preceding theorem supplies it uniformly on
an ordinary metric ball.

The nonzero-vector construction uses the existing differential field whose
radius precedes the tangent alignment.  The zero vector is filled by the
canonical anchor datum.
-/
theorem exists_normal_successor_data_radius_all_alignments_fixed_anchors_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    ∃ rho > (0 : Real),
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
        z ∈ (CartanChain.ChainState.mk x p L).germ.source →
        let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) x
        let v := eM.symm ((chartAt E x) z)
        ‖v‖ < rho →
          Nonempty (Data (CartanChain.ChainState.mk x p L) z) := by
  rcases
      UniformTangentAlignmentDifferentialField.exists_uniform_cartanChartDifferential_field_on_punctured_ball
        g hcurv x p with
    ⟨rho, hrho, hfieldForAlignment⟩
  refine ⟨rho, hrho, ?_⟩
  intro L
  rcases hfieldForAlignment L with
    ⟨Afield, Bfield, DF, hDF, hfield⟩
  intro z hz
  dsimp only
  let s : CartanChain.ChainState g :=
    CartanChain.ChainState.mk x p L
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) x
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p
  let v : E := eM.symm ((chartAt E x) z)
  intro hv
  by_cases hvzero : v = 0
  · have hzAnchor : z = s.anchor :=
      DifferentialSuccessorZero.eq_anchor_of_source_normal_coordinate_eq_zero
        s (by simpa [s] using hz) (by simpa [s, v, eM] using hvzero)
    subst z
    simpa [s] using DifferentialSuccessorZero.data_nonempty_at_anchor s
  · have hsource :
        z ∈ (chartAt E x).source ∧
          (chartAt E x) z ∈ eM.target ∧
            v ∈ (CartanMap.tangentAlignmentOpenPartialHomeomorph L).source ∧
              L v ∈ eS.source ∧
                (chartAt E p)
                    (GeodesicTransport.expAt roundSphereMetric3 p (L v)) ∈
                  (chartAt E p).target := by
      simpa [CartanChain.ChainState.germ, CartanMap.openPartialHomeomorph,
        eM, eS, v] using hz
    have hzcoord : extChartAt I x z = eM v := by
      simpa [eM, v, extChartAt_coe] using
        (eM.right_inv hsource.2.1).symm
    have hpcoord :
        extChartAt I p (s.map z) = eS (L v) := by
      have hright := (chartAt E p).right_inv hsource.2.2.2.2
      simpa [s, CartanChain.ChainState.map, CartanMap.cartanMap_apply,
        eM, eS, v, extChartAt_coe] using hright
    have hpold : s.map z ∈ (extChartAt I p).source := by
      have hmap := (chartAt E p).map_target hsource.2.2.2.2
      simpa [s, CartanChain.ChainState.map, CartanMap.cartanMap_apply,
        eM, eS, v, extChartAt_source] using hmap
    rcases hfield v hv hvzero with
      ⟨hsourceStrict, htargetStrict, _hinvertible, hmapStrict, hpullback⟩
    refine ⟨⟨v, Afield v, Bfield v, ?_, ?_, ?_, hpold, ?_, ?_,
      hsourceStrict, htargetStrict, ?_, ?_⟩⟩
    · exact eM.symm.map_source hsource.2.1
    · exact hsource.2.2.2.1
    · simpa [s, extChartAt_source] using hsource.1
    · simpa [s, eM] using hzcoord
    · simpa [s, eS] using hpcoord
    · simpa [s, hDF v] using hmapStrict
    · intro u u'
      rw [← hDF v]
      exact hpullback u u'

/--
For fixed source and target anchors, one ordinary metric successor-data radius
works for every tangent alignment.  This combines the alignment-uniform germ
source ball with the alignment-uniform normal-coordinate data radius.

Consequently the automatic local existence radius does not intrinsically
depend on the alignment component of a Cartan state.  The unresolved state
dependence is reduced to the source and target anchors.
-/
theorem exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : Real),
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty (Data (CartanChain.ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_metric_ball_subset_germ_source_all_alignments_fixed_anchors
        g x p with
    ⟨sourceRadius, hsourceRadius, hsource⟩
  rcases
      exists_normal_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨normalRadius, hnormalRadius, hnormalData⟩
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) x
  let normalCoordinate : M → E := fun z =>
    eM.symm ((chartAt E x) z)
  have htarget : (chartAt E x) x ∈ eM.target := by
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  have hchart : ContinuousAt (fun z : M => (chartAt E x) z) x := by
    simpa [extChartAt_coe] using
      continuousAt_extChartAt («I» := I) x
  have hnormalContinuous : ContinuousAt normalCoordinate x := by
    exact (eM.continuousAt_symm htarget).comp hchart
  have hnormalZero : normalCoordinate x = (0 : E) := by
    simpa [normalCoordinate, eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x
  have hnormalNhds :
      normalCoordinate ⁻¹' Metric.ball (0 : E) normalRadius ∈ 𝓝 x := by
    apply hnormalContinuous.preimage_mem_nhds
    rw [hnormalZero]
    exact Metric.ball_mem_nhds (0 : E) hnormalRadius
  rcases Metric.mem_nhds_iff.mp hnormalNhds with
    ⟨coordinateRadius, hcoordinateRadius, hcoordinate⟩
  let epsilon : Real := min sourceRadius coordinateRadius
  have hepsilon : 0 < epsilon :=
    lt_min hsourceRadius hcoordinateRadius
  refine ⟨epsilon, hepsilon, ?_⟩
  intro L z hdist
  have hzSourceBall : z ∈ Metric.ball x sourceRadius := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_left _ _)
  have hzSource :
      z ∈ (CartanChain.ChainState.mk x p L).germ.source :=
    hsource L hzSourceBall
  have hzCoordinateBall : z ∈ Metric.ball x coordinateRadius := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_right _ _)
  have hzNormal : normalCoordinate z ∈ Metric.ball (0 : E) normalRadius :=
    hcoordinate hzCoordinateBall
  have hv : ‖normalCoordinate z‖ < normalRadius := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzNormal
  exact hnormalData L z hzSource (by
    simpa [normalCoordinate, eM] using hv)

/--
The canonical positive ordinary metric radius selected from curvature for one
pair of source and target anchors.  Its defining existence theorem is uniform
over every tangent alignment between those anchors.
-/
def curvatureAnchorTargetRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) : Real := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose
    (exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
      g hcurv x p)

/-- Every selected source-target curvature radius is positive. -/
theorem curvatureAnchorTargetRadius_pos
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    0 < curvatureAnchorTargetRadius hcurv x p := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p)).1

/--
Displacement below the selected source-target radius produces successor data
for any tangent alignment between those anchors.
-/
theorem nonempty_data_of_dist_lt_curvatureAnchorTargetRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
      dist z x < curvatureAnchorTargetRadius hcurv x p →
        Nonempty (Data (CartanChain.ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p)).2

/--
For one actual Cartan state, constant curvature supplies differential-induced
successor data at every point of a sufficiently small ordinary metric ball
around its anchor.

The normal-coordinate existence theorem itself asks both for membership in
the strict Cartan source and for a vector norm bound.  Both are neighborhoods
of the anchor: the source is open, while the inverse normal coordinate is
continuous there and vanishes at the anchor.  Intersecting the two metric
neighborhoods gives the stated radius.
-/
theorem exists_metric_successor_data_radius_of_curvature
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : Real), ∀ z : M,
      dist z s.anchor < epsilon → Nonempty (Data s z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases DifferentialSuccessorZero.exists_data_on_ball g hcurv s with
    ⟨rho, hrho, hdata⟩
  rcases CartanChainRigidity.exists_ball_subset_germ_source s with
    ⟨sourceRadius, hsourceRadius, hsource⟩
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let normalCoordinate : M → E := fun z =>
    eM.symm ((chartAt E s.anchor) z)
  have htarget : (chartAt E s.anchor) s.anchor ∈ eM.target := by
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) s.anchor
  have hchart : ContinuousAt
      (fun z : M => (chartAt E s.anchor) z) s.anchor := by
    simpa [extChartAt_coe] using
      continuousAt_extChartAt («I» := I) s.anchor
  have hnormal : ContinuousAt normalCoordinate s.anchor := by
    exact (eM.continuousAt_symm htarget).comp hchart
  have hnormalZero : normalCoordinate s.anchor = (0 : E) := by
    simpa [normalCoordinate, eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero
        g s.anchor
  have hcoordinateNhds :
      normalCoordinate ⁻¹' Metric.ball (0 : E) rho ∈ 𝓝 s.anchor := by
    apply hnormal.preimage_mem_nhds
    rw [hnormalZero]
    exact Metric.ball_mem_nhds (0 : E) hrho
  rcases Metric.mem_nhds_iff.mp hcoordinateNhds with
    ⟨coordinateRadius, hcoordinateRadius, hcoordinate⟩
  let epsilon : Real := min sourceRadius coordinateRadius
  have hepsilon : 0 < epsilon := by
    exact lt_min hsourceRadius hcoordinateRadius
  refine ⟨epsilon, hepsilon, ?_⟩
  intro z hdist
  have hzSourceBall : z ∈ Metric.ball s.anchor sourceRadius := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_left _ _)
  have hzSource : z ∈ s.germ.source := hsource hzSourceBall
  have hzCoordinateBall : z ∈ Metric.ball s.anchor coordinateRadius := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_right _ _)
  have hzCoordinate : normalCoordinate z ∈ Metric.ball (0 : E) rho :=
    hcoordinate hzCoordinateBall
  have hv : ‖normalCoordinate z‖ < rho := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzCoordinate
  exact hdata z hzSource (by
    simpa [normalCoordinate, eM] using hv)

/--
The canonical positive metric successor radius selected from curvature for one
actual Cartan state.
-/
def curvatureStateRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) : Real := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose
    (exists_metric_successor_data_radius_of_curvature hcurv s)

/-- Every automatically selected curvature state radius is positive. -/
theorem curvatureStateRadius_pos
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    0 < curvatureStateRadius hcurv s := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_metric_successor_data_radius_of_curvature hcurv s)).1

/-- Metric displacement below the selected state radius produces actual
differential-successor data. -/
theorem nonempty_data_of_dist_lt_curvatureStateRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ z : M, dist z s.anchor < curvatureStateRadius hcurv s →
      Nonempty (Data s z) := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_metric_successor_data_radius_of_curvature hcurv s)).2

/-- A finite family of actual continuation states has one common positive
curvature successor radius.  This is the non-circular finite-history minimum
available after a family has been realized. -/
theorem exists_common_metric_successor_data_radius_for_finite_states_of_curvature
    {g : ClosedSmoothRiemannianMetric 3 M}
    {index : Type v} [Fintype index] [Nonempty index]
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (state : index → CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : Real), ∀ i : index, ∀ z : M,
      dist z (state i).anchor < epsilon → Nonempty (Data (state i) z) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let epsilon : Real :=
    Finset.univ.inf' Finset.univ_nonempty
      (fun i : index => curvatureStateRadius hcurv (state i))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact curvatureStateRadius_pos hcurv (state i)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro i z hdist
  apply nonempty_data_of_dist_lt_curvatureStateRadius hcurv (state i) z
  exact hdist.trans_le
    (Finset.inf'_le
      (fun j : index => curvatureStateRadius hcurv (state j))
      (Finset.mem_univ i))

/--
An anchor radius works uniformly over the full Cartan-state fiber above every
source point.  This is strictly weaker and more geometric than the original
path-cell `hlocal`: it has one source point and one next point rather than a
path center plus two samples.
-/
def AnchorUniformSuccessorDataRadius
    (g : ClosedSmoothRiemannianMetric 3 M) (radius : M → Real) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ x : M, 0 < radius x ∧
    ∀ (s : CartanChain.ChainState g), s.anchor = x →
      ∀ z : M, dist z x < radius x → Nonempty (Data s z)

/--
The parameter locus on which every tangent alignment at a source-target pair
admits differential-successor data at the supplied next source point.

The dependent alignment quantifier is internal to the locus.  Consequently,
openness of this one subset is a genuine joint parameter-regularity contract,
not a pointwise family of arbitrarily selected radii.
-/
def UniversalSuccessorDataLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    Set ((M × RoundSphere3) × M) :=
  {q | ∀ L : CartanMap.TangentAlignment g q.1.1 q.1.2,
    Nonempty
      (Data (CartanChain.ChainState.mk q.1.1 q.1.2 L) q.2)}

/-- The complete source-target diagonal belongs to the universal successor
data locus, by the canonical zero-vector datum. -/
theorem universalSuccessorDataLocus_diagonal
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (p : RoundSphere3) :
    ((x, p), x) ∈ UniversalSuccessorDataLocus g := by
  intro L
  exact DifferentialSuccessorZero.data_nonempty_at_anchor
    (CartanChain.ChainState.mk x p L)

/-- The compact graph of the source anchor inside the joint source-target-next
parameter space. -/
def successorParameterDiagonal : Set ((M × RoundSphere3) × M) :=
  (fun xp : M × RoundSphere3 ↦ (xp, xp.1)) '' Set.univ

/-- Compactness of the manifold and round sphere makes the complete parameter
diagonal compact. -/
theorem isCompact_successorParameterDiagonal :
    IsCompact (successorParameterDiagonal (M := M)) := by
  exact isCompact_univ.image (continuous_id.prodMk continuous_fst)

/-- The universal successor-data locus contains the complete parameter
diagonal. -/
theorem successorParameterDiagonal_subset_universalSuccessorDataLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    successorParameterDiagonal (M := M) ⊆ UniversalSuccessorDataLocus g := by
  rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
  exact universalSuccessorDataLocus_diagonal g x p

/--
The weakest joint regularity contract needed for compact uniformization: the
universal successor-data locus is a neighborhood of the parameter diagonal.
Unlike global openness, this says nothing away from small successor steps.
-/
def UniversalSuccessorDataNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  UniversalSuccessorDataLocus g ∈
    𝓝ˢ (successorParameterDiagonal (M := M))

/-- Global openness of the universal locus implies the strictly weaker
diagonal-neighborhood contract. -/
theorem universalSuccessorDataNeighborhood_of_isOpen
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hopen : IsOpen (UniversalSuccessorDataLocus g)) :
    UniversalSuccessorDataNeighborhood g := by
  exact hopen.mem_nhdsSet.mpr
    (successorParameterDiagonal_subset_universalSuccessorDataLocus g)

/--
Constant curvature proves the full vertical section of the desired joint
neighborhood statement at every fixed source-target pair: successor data are
available on a neighborhood of the source anchor, simultaneously for all
tangent alignments.

What remains between this theorem and `UniversalSuccessorDataNeighborhood` is
precisely stability as the source and target anchors vary.  Pointwise positive
vertical radii alone cannot supply that stability.
-/
theorem universalSuccessorDataLocus_vertical_mem_nhds_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    {z : M | ((x, p), z) ∈ UniversalSuccessorDataLocus g} ∈ 𝓝 x := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨epsilon, hepsilon, hdata⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hepsilon) ?_
  intro z hz
  intro L
  apply hdata L z
  simpa [Metric.mem_ball] using hz

/--
The diagonal-neighborhood contract, rather than global openness, already gives
one positive successor-data radius uniform in source anchor, sphere target,
and tangent alignment.  Compactness converts the neighborhood filter into a
closed-thickening basis around the diagonal graph.
-/
theorem exists_uniform_successor_data_radius_of_universalNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorDataNeighborhood g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : Real),
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty (Data (CartanChain.ChainState.mk x p L) z) := by
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

/--
If the universal successor-data locus is open in all three anchors, compactness
of `M × RoundSphere3` turns its neighborhood of the diagonal graph into one
global positive metric radius.  The proof thickens the compact diagonal graph
inside the open locus; a point whose next source anchor is close to its current
source anchor lies in that thickening.

This theorem removes both target quantification and lower-semicontinuous
radius selection.  Its sole premise is the honest joint openness statement
which the independently chosen generic exponential charts do not currently
provide automatically.
-/
theorem exists_uniform_successor_data_radius_of_isOpen_universalLocus
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hopen : IsOpen (UniversalSuccessorDataLocus g)) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : Real),
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty (Data (CartanChain.ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  let diagonalGraph : Set ((M × RoundSphere3) × M) :=
    (fun xp : M × RoundSphere3 ↦ (xp, xp.1)) '' Set.univ
  have hgraphCompact : IsCompact diagonalGraph := by
    exact isCompact_univ.image (continuous_id.prodMk continuous_fst)
  have hgraphSubset : diagonalGraph ⊆ UniversalSuccessorDataLocus g := by
    rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
    exact universalSuccessorDataLocus_diagonal g x p
  rcases hgraphCompact.exists_cthickening_subset_open hopen hgraphSubset with
    ⟨epsilon, hepsilon, hthick⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro x p L z hdist
  let graphPoint : (M × RoundSphere3) × M := ((x, p), x)
  have hgraphPoint : graphPoint ∈ diagonalGraph := by
    exact ⟨(x, p), Set.mem_univ _, rfl⟩
  have hmem : ((x, p), z) ∈ Metric.cthickening epsilon diagonalGraph := by
    apply Metric.mem_cthickening_of_dist_le
      (((x, p), z) : (M × RoundSphere3) × M) graphPoint epsilon
        diagonalGraph hgraphPoint
    simpa [graphPoint, Prod.dist_eq] using le_of_lt hdist
  exact (hthick hmem) L

/--
A jointly lower-semicontinuous positive radius over source and sphere-target
anchors has a positive lower-semicontinuous source-only minorant.

For each source anchor, lower semicontinuity on the compact round sphere makes
the target minimum attained.  Joint lower semicontinuity and the tube lemma
show that these attained minimum values are lower semicontinuous in the source
anchor.  This is the precise compact-target reduction needed by rooted path
realization; no continuity of a classically selected pointwise radius is
silently assumed.
-/
theorem exists_positive_lowerSemicontinuous_source_minorant_of_compact_target
    (radius : M → RoundSphere3 → Real)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < radius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ radius xp.1 xp.2)) :
    ∃ sourceRadius : M → Real,
      (∀ x : M, 0 < sourceRadius x) ∧
      LowerSemicontinuous sourceRadius ∧
      ∀ (x : M) (p : RoundSphere3), sourceRadius x ≤ radius x p := by
  classical
  have hminimum : ∀ x : M, ∃ pmin : RoundSphere3,
      ∀ p : RoundSphere3, radius x pmin ≤ radius x p := by
    intro x
    have hfixed : LowerSemicontinuous (radius x) := by
      have hcomp := hlower.comp (Continuous.prodMk_right x)
      simpa [Function.comp_def] using hcomp
    rcases
        hfixed.lowerSemicontinuousOn Set.univ |>.exists_isMinOn
          Set.univ_nonempty isCompact_univ with
      ⟨pmin, _hpminMem, hpmin⟩
    exact ⟨pmin, fun p ↦ hpmin (Set.mem_univ p)⟩
  choose pmin hpmin using hminimum
  let sourceRadius : M → Real := fun x ↦ radius x (pmin x)
  have hsourcePositive : ∀ x : M, 0 < sourceRadius x := by
    intro x
    exact hpositive x (pmin x)
  have hsourceMinorant : ∀ (x : M) (p : RoundSphere3),
      sourceRadius x ≤ radius x p := by
    intro x p
    exact hpmin x p
  have hsourceLower : LowerSemicontinuous sourceRadius := by
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro a
    rw [isOpen_iff_mem_nhds]
    intro x hx
    let V : Set (M × RoundSphere3) :=
      (fun xp : M × RoundSphere3 ↦ radius xp.1 xp.2) ⁻¹' Ioi a
    have hVOpen : IsOpen V := by
      exact hlower.isOpen_preimage a
    have hfiber : ({x} : Set M) ×ˢ (Set.univ : Set RoundSphere3) ⊆ V := by
      rintro ⟨x', p⟩ ⟨hx', _hp⟩
      have hxx : x' = x := Set.mem_singleton_iff.mp hx'
      subst x'
      change a < radius x p
      exact hx.trans_le (hsourceMinorant x p)
    rcases generalized_tube_lemma isCompact_singleton
        (isCompact_univ : IsCompact (Set.univ : Set RoundSphere3))
        hVOpen hfiber with
      ⟨U, W, hUOpen, _hWOpen, hxU, htargetW, hUW⟩
    refine Filter.mem_of_superset
      (hUOpen.mem_nhds (hxU (Set.mem_singleton x))) ?_
    intro y hy
    have hypair : (y, pmin y) ∈ V :=
      hUW ⟨hy, htargetW (Set.mem_univ (pmin y))⟩
    exact hypair
  exact ⟨sourceRadius, hsourcePositive, hsourceLower, hsourceMinorant⟩

/--
A positive lower-semicontinuous anchor-uniform successor radius produces the
pointwise history-compatible path radii required by adaptive rooted
realization.

At a path center `c`, lower semicontinuity gives a metric neighborhood on
which the anchor radius stays above half its value at `gamma c`.  Intersect
that neighborhood with a quarter-radius ball.  If the left and right samples
lie in this smaller ball, their mutual distance is less than half the center
radius and therefore less than the anchor radius at the left sample.
-/
theorem exists_historyCompatible_path_radius_of_anchorUniform_lowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (gamma : C(unitInterval, M)) (anchorRadius : M → Real)
    (hanchor : AnchorUniformSuccessorDataRadius g anchorRadius)
    (hlower : LowerSemicontinuous anchorRadius) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ pathRadius : unitInterval → Real,
      (∀ c : unitInterval, 0 < pathRadius c) ∧
      ∀ (c u v : unitInterval) (s : CartanChain.ChainState g),
        dist (gamma u) (gamma c) < pathRadius c →
        dist (gamma v) (gamma c) < pathRadius c →
        s.anchor = gamma u → Nonempty (Data s (gamma v)) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  change ∀ x : M, 0 < anchorRadius x ∧
    ∀ (s : CartanChain.ChainState g), s.anchor = x →
      ∀ z : M, dist z x < anchorRadius x → Nonempty (Data s z) at hanchor
  have hpoint : ∀ c : unitInterval, ∃ r > (0 : Real),
      ∀ (u v : unitInterval) (s : CartanChain.ChainState g),
        dist (gamma u) (gamma c) < r →
        dist (gamma v) (gamma c) < r →
        s.anchor = gamma u → Nonempty (Data s (gamma v)) := by
    intro c
    let q : M := gamma c
    have hqPositive : 0 < anchorRadius q := (hanchor q).1
    let U : Set M := anchorRadius ⁻¹' Ioi (anchorRadius q / 2)
    have hUOpen : IsOpen U := by
      exact hlower.isOpen_preimage (anchorRadius q / 2)
    have hqU : q ∈ U := by
      change anchorRadius q / 2 < anchorRadius q
      exact half_lt_self hqPositive
    rcases Metric.isOpen_iff.mp hUOpen q hqU with
      ⟨neighborhoodRadius, hneighborhoodRadius, hball⟩
    let r : Real := min neighborhoodRadius (anchorRadius q / 4)
    have hr : 0 < r := by
      exact lt_min hneighborhoodRadius (div_pos hqPositive (by norm_num))
    refine ⟨r, hr, ?_⟩
    intro u v s hu hv hs
    have huNeighborhood :
        dist (gamma u) q < neighborhoodRadius := by
      exact hu.trans_le (min_le_left _ _)
    have huU : gamma u ∈ U := by
      apply hball
      simpa [Metric.mem_ball] using huNeighborhood
    have hleftRadius : anchorRadius q / 2 < anchorRadius (gamma u) := by
      simpa [U] using huU
    have huv : dist (gamma v) (gamma u) < anchorRadius q / 2 := by
      calc
        dist (gamma v) (gamma u) ≤
            dist (gamma v) q + dist (gamma u) q :=
          dist_triangle_right _ _ _
        _ < r + r := add_lt_add hv hu
        _ ≤ anchorRadius q / 4 + anchorRadius q / 4 :=
          add_le_add (min_le_right _ _) (min_le_right _ _)
        _ = anchorRadius q / 2 := by ring
    exact (hanchor (gamma u)).2 s hs (gamma v)
      (huv.trans hleftRadius)
  choose pathRadius hpathRadiusPos hpathRadius using hpoint
  exact ⟨pathRadius, hpathRadiusPos, hpathRadius⟩

/--
The original rooted `hlocal` boundary is discharged by an anchor-uniform
lower-semicontinuous radius.  Every root-to-endpoint path may then be realized
with any globally prescribed positive mesh.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_anchorUniformRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g)
    (anchorRadius : M → Real)
    (hanchor : AnchorUniformSuccessorDataRadius g anchorRadius)
    (hlower : LowerSemicontinuous anchorRadius)
    (mesh : Real) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : Nat),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hpath : ∀ x : M, ∃ pathRadius : unitInterval → Real,
      (∀ c : unitInterval, 0 < pathRadius c) ∧
      ∀ (c u v : unitInterval) (s : CartanChain.ChainState g),
        dist (skeleton.path x u) (skeleton.path x c) < pathRadius c →
        dist (skeleton.path x v) (skeleton.path x c) < pathRadius c →
        s.anchor = skeleton.path x u →
          Nonempty (Data s (skeleton.path x v)) := by
    intro x
    exact
      exists_historyCompatible_path_radius_of_anchorUniform_lowerSemicontinuous
        (skeleton.path x) anchorRadius hanchor hlower
  choose pathRadius hpathRadiusPos hpathRadius using hpath
  exact
    exists_rootedPathChainRealization_with_prescribed_mesh_of_successor_radii
      skeleton pathRadius hpathRadiusPos hpathRadius mesh hmesh

/--
Joint openness of the universal successor-data locus directly gives complete
rooted path realization with any prescribed positive mesh.  Compactness first
produces one constant radius valid for every source anchor, sphere target, and
tangent alignment; a constant function is lower semicontinuous, so the general
anchor-uniform realization theorem applies.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_isOpen_universalSuccessorDataLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g)
    (hopen : IsOpen (UniversalSuccessorDataLocus g))
    (mesh : Real) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : Nat),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_successor_data_radius_of_isOpen_universalLocus
      g hopen with
    ⟨epsilon, hepsilon, hdata⟩
  let anchorRadius : M → Real := fun _x ↦ epsilon
  have hanchor : AnchorUniformSuccessorDataRadius g anchorRadius := by
    change ∀ x : M, 0 < anchorRadius x ∧
      ∀ (s : CartanChain.ChainState g), s.anchor = x →
        ∀ z : M, dist z x < anchorRadius x → Nonempty (Data s z)
    intro x
    refine ⟨hepsilon, ?_⟩
    intro s hs z hdist
    have hdist' : dist z s.anchor < epsilon := by
      simpa [anchorRadius, hs] using hdist
    have hdatum : Nonempty
        (Data
          (CartanChain.ChainState.mk s.anchor s.target s.alignment) z) :=
      hdata s.anchor s.target s.alignment z hdist'
    have heta :
        CartanChain.ChainState.mk s.anchor s.target s.alignment = s := by
      cases s
      rfl
    simpa [heta] using hdatum
  have hlower : LowerSemicontinuous anchorRadius := by
    exact lowerSemicontinuous_const
  exact
    exists_rootedPathChainRealization_with_prescribed_mesh_of_anchorUniformRadius
      skeleton anchorRadius hanchor hlower mesh hmesh

/--
The weakest joint diagonal-neighborhood contract already suffices for complete
rooted realization.  This is stronger than the preceding consumer because it
does not ask the successor-data locus to be open away from the diagonal.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_universalSuccessorDataNeighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g)
    (hneighborhood : UniversalSuccessorDataNeighborhood g)
    (mesh : Real) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : Nat),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_successor_data_radius_of_universalNeighborhood
      g hneighborhood with
    ⟨epsilon, hepsilon, hdata⟩
  let anchorRadius : M → Real := fun _x ↦ epsilon
  have hanchor : AnchorUniformSuccessorDataRadius g anchorRadius := by
    change ∀ x : M, 0 < anchorRadius x ∧
      ∀ (s : CartanChain.ChainState g), s.anchor = x →
        ∀ z : M, dist z x < anchorRadius x → Nonempty (Data s z)
    intro x
    refine ⟨hepsilon, ?_⟩
    intro s hs z hdist
    have hdist' : dist z s.anchor < epsilon := by
      simpa [anchorRadius, hs] using hdist
    have hdatum : Nonempty
        (Data
          (CartanChain.ChainState.mk s.anchor s.target s.alignment) z) :=
      hdata s.anchor s.target s.alignment z hdist'
    have heta :
        CartanChain.ChainState.mk s.anchor s.target s.alignment = s := by
      cases s
      rfl
    simpa [heta] using hdatum
  have hlower : LowerSemicontinuous anchorRadius := by
    exact lowerSemicontinuous_const
  exact
    exists_rootedPathChainRealization_with_prescribed_mesh_of_anchorUniformRadius
      skeleton anchorRadius hanchor hlower mesh hmesh

/--
Constant curvature automatically supplies the state-dependent radii.  Hence a
positive lower-semicontinuous anchor function which minorizes every selected
state radius is sufficient for the complete rooted prescribed-mesh
realization.

This is the narrowed true boundary: all local differential existence,
normal-coordinate conversion, path compactness, finite minima, and actual
chain recursion are proved; only the anchor-fiber minorant remains.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_curvature_anchorMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (skeleton : RootedCartanPathSkeleton g)
    (anchorRadius : M → Real)
    (hpositive : ∀ x : M, 0 < anchorRadius x)
    (hlower : LowerSemicontinuous anchorRadius)
    (hminorant : ∀ s : CartanChain.ChainState g,
      anchorRadius s.anchor ≤ curvatureStateRadius hcurv s)
    (mesh : Real) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : Nat),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  have hanchor : AnchorUniformSuccessorDataRadius g anchorRadius := by
    change ∀ x : M, 0 < anchorRadius x ∧
      ∀ (s : CartanChain.ChainState g), s.anchor = x →
        ∀ z : M, dist z x < anchorRadius x → Nonempty (Data s z)
    intro x
    refine ⟨hpositive x, ?_⟩
    intro s hs z hdist
    apply nonempty_data_of_dist_lt_curvatureStateRadius hcurv s z
    have hdistState : dist z s.anchor < anchorRadius s.anchor := by
      simpa [hs] using hdist
    exact hdistState.trans_le (hminorant s)
  exact
    exists_rootedPathChainRealization_with_prescribed_mesh_of_anchorUniformRadius
      skeleton anchorRadius hanchor hlower mesh hmesh

/--
Constant curvature and tangent-alignment compactness reduce the full rooted
local-existence boundary to target-anchor uniformity alone.  It suffices to
give a positive lower-semicontinuous source-anchor radius which minorizes the
selected curvature radius for every sphere target.  No quantification over
tangent alignments or recursively reached Cartan states remains in the
hypothesis.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_curvature_anchorTargetMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (skeleton : RootedCartanPathSkeleton g)
    (anchorRadius : M → Real)
    (hpositive : ∀ x : M, 0 < anchorRadius x)
    (hlower : LowerSemicontinuous anchorRadius)
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      anchorRadius x ≤ curvatureAnchorTargetRadius hcurv x p)
    (mesh : Real) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : Nat),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  have hanchor : AnchorUniformSuccessorDataRadius g anchorRadius := by
    change ∀ x : M, 0 < anchorRadius x ∧
      ∀ (s : CartanChain.ChainState g), s.anchor = x →
        ∀ z : M, dist z x < anchorRadius x → Nonempty (Data s z)
    intro x
    refine ⟨hpositive x, ?_⟩
    intro s hs z hdist
    have hdistAnchor : dist z s.anchor < anchorRadius s.anchor := by
      simpa [hs] using hdist
    have hdistTarget :
        dist z s.anchor <
          curvatureAnchorTargetRadius hcurv s.anchor s.target :=
      hdistAnchor.trans_le (hminorant s.anchor s.target)
    have hdata : Nonempty
        (Data
          (CartanChain.ChainState.mk s.anchor s.target s.alignment) z) :=
      nonempty_data_of_dist_lt_curvatureAnchorTargetRadius
        hcurv s.anchor s.target s.alignment z hdistTarget
    have heta :
        CartanChain.ChainState.mk s.anchor s.target s.alignment = s := by
      cases s
      rfl
    simpa [heta] using hdata
  exact
    exists_rootedPathChainRealization_with_prescribed_mesh_of_anchorUniformRadius
      skeleton anchorRadius hanchor hlower mesh hmesh

/--
A jointly lower-semicontinuous positive source-target minorant of the automatic
curvature radii is enough for full rooted realization.  Compactness of the
round sphere takes the target minimum internally and constructs the
source-only lower-semicontinuous radius required by the preceding theorem.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_curvature_jointAnchorTargetMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (skeleton : RootedCartanPathSkeleton g)
    (pairRadius : M → RoundSphere3 → Real)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ curvatureAnchorTargetRadius hcurv x p)
    (mesh : Real) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : Nat),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_positive_lowerSemicontinuous_source_minorant_of_compact_target
        pairRadius hpositive hlower with
    ⟨anchorRadius, hanchorPositive, hanchorLower, hanchorMinorant⟩
  apply
    exists_rootedPathChainRealization_with_prescribed_mesh_of_curvature_anchorTargetMinorant
      hcurv skeleton anchorRadius hanchorPositive hanchorLower
  · intro x p
    exact (hanchorMinorant x p).trans (hminorant x p)
  · exact hmesh

/--
If the canonically selected source-target curvature radius is itself jointly
lower semicontinuous, no separate minorant or target-uniformity hypothesis is
needed.  This corollary deliberately exposes that regularity as a premise:
the radius is selected by classical choice, so its lower semicontinuity must
not be inferred merely from pointwise positivity.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_curvatureAnchorTargetRadius_lowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (skeleton : RootedCartanPathSkeleton g)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        curvatureAnchorTargetRadius hcurv xp.1 xp.2))
    (mesh : Real) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : Nat),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  apply
    exists_rootedPathChainRealization_with_prescribed_mesh_of_curvature_jointAnchorTargetMinorant
      hcurv skeleton
      (fun x p ↦ curvatureAnchorTargetRadius hcurv x p)
  · exact curvatureAnchorTargetRadius_pos hcurv
  · exact hlower
  · intro x p
    exact le_rfl
  · exact hmesh

end CartanAtlasRootedPathCurvatureSuccessorRadius
end Poincare
