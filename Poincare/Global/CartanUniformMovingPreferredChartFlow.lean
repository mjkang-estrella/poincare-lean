import Poincare.Global.CartanFixedChartGenericInverseEndpointODETailOverlapReduction

/-!
# A uniform preferred-chart geodesic flow near a moving anchor

The variable-initial-state Picard-Lindelöf flow in one fixed chart can be
transported to the preferred charts of nearby anchors under two explicit
hypotheses: one uniform chart/cutoff transition neighborhood and one uniform
bound for the reverse velocity transition.  The resulting package has a
common time and moving-chart velocity radius.

This construction supplies the ODE and retained chart/cutoff domains.  It
does not identify these transported trajectories with the separately chosen
public `expAt`.
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
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The precise missing joint chart-choice condition: one fixed-coordinate
position neighborhood is contained in the honest chart/cutoff transition
locus for every moving anchor in one manifold neighborhood. -/
def UniformPreferredChartTransportNeighborhood (x₀ : M) : Prop :=
  ∃ V : Set M, V ∈ 𝓝 x₀ ∧ ∃ U : Set E,
    U ∈ 𝓝 (extChartAt I x₀ x₀) ∧
      ∀ x ∈ V, U ⊆ chartTransitionCutoffGoodLocus x₀ x

/-- Joint anchor-position locus underlying the uniform preferred-chart
transport condition. -/
def preferredChartTransportGoodLocus (x₀ : M) : Set (M × E) :=
  {q | q.2 ∈ chartTransitionCutoffGoodLocus x₀ q.1}

/-- Uniform preferred-chart transport is exactly the existence of a product
neighborhood inside the joint good locus. -/
theorem uniformPreferredChartTransportNeighborhood_iff_jointGoodLocus_mem_nhds
    (x₀ : M) :
    UniformPreferredChartTransportNeighborhood x₀ ↔
      preferredChartTransportGoodLocus x₀ ∈
        nhds (x₀, extChartAt I x₀ x₀) := by
  constructor
  · rintro ⟨V, hV, U, hU, hsub⟩
    refine Filter.mem_of_superset (prod_mem_nhds hV hU) ?_
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    change z ∈ chartTransitionCutoffGoodLocus x₀ x
    exact hsub x hx hz
  · intro hjoint
    rcases mem_nhds_prod_iff.mp hjoint with
      ⟨V, hV, U, hU, hproduct⟩
    refine ⟨V, hV, U, hU, ?_⟩
    intro x hx z hz
    have hxz : (x, z) ∈ preferredChartTransportGoodLocus x₀ :=
      hproduct ⟨hx, hz⟩
    exact hxz

/-- The centered anchor-coordinate pair belongs to the joint chart/cutoff
good locus. -/
theorem center_mem_preferredChartTransportGoodLocus (x₀ : M) :
    (x₀, extChartAt I x₀ x₀) ∈ preferredChartTransportGoodLocus x₀ := by
  have hxSource : x₀ ∈ (extChartAt I x₀).source :=
    mem_extChartAt_source x₀
  have hzTarget : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hxSource
  have hcutoff : extChartAt I x₀ x₀ ∈
      IsometryInstantiate.cutoffOneLocus x₀ :=
    mem_of_mem_nhds
      (IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x₀)
  change
    (((extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target ∧
        (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈
          (extChartAt I x₀).source) ∧
      extChartAt I x₀ x₀ ∈ IsometryInstantiate.cutoffOneLocus x₀) ∧
    GeodesicTransport.chartTransition x₀ x₀ (extChartAt I x₀ x₀) ∈
      IsometryInstantiate.cutoffOneLocus x₀)
  refine ⟨⟨⟨hzTarget, ?_⟩, hcutoff⟩, ?_⟩
  · simpa only [(extChartAt I x₀).left_inv hxSource] using hxSource
  · simpa [GeodesicTransport.chartTransition_apply,
      (extChartAt I x₀).left_inv hxSource] using hcutoff

/-- Joint openness at the centered pair is sufficient for the exact uniform
preferred-chart transport hypothesis. -/
theorem uniformPreferredChartTransportNeighborhood_of_isOpen_jointGoodLocus
    (x₀ : M)
    (hopen : IsOpen (preferredChartTransportGoodLocus x₀)) :
    UniformPreferredChartTransportNeighborhood x₀ :=
  (uniformPreferredChartTransportNeighborhood_iff_jointGoodLocus_mem_nhds x₀).2
    (hopen.mem_nhds (center_mem_preferredChartTransportGoodLocus x₀))

/-- Convert a velocity in the moving preferred chart back to the fixed
`x₀` chart at the same manifold anchor. -/
def movingToFixedVelocity (x₀ : M) (q : M × E) : E :=
  GeodesicTransport.chartTransitionDeriv q.1 x₀
    (extChartAt I q.1 q.1) q.2

/-- The forward derivative sends the exact reverse-coordinate velocity back
to the original moving-chart velocity. -/
theorem fixedToAnchorVelocity_movingToFixedVelocity
    (x₀ x : M) (hx : x ∈ (extChartAt I x₀).source) (u : E) :
    fixedToAnchorVelocity x₀ (x, movingToFixedVelocity x₀ (x, u)) = u := by
  let zT : E := extChartAt I x x
  let Dforward : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := x₀) (y₀ := x) (extChartAt I x₀ x)
  let Dreverse : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := x) (y₀ := x₀) zT
  have hzT : zT ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  have hxT : (extChartAt I x).symm zT = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  let Dnew : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I x).symm) (range I) zT
  let Cold : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x₀) x
  let Iold : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I x₀).symm) (range I) (extChartAt I x₀ x)
  let Cnew : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) x
  have holdCLM : Iold.comp Cold = ContinuousLinearMap.id ℝ E := by
    simpa [Iold, Cold] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx)
  have hnewCLM : Cnew.comp Dnew = ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hzT
    rw [hxT] at h
    simpa [Cnew, Dnew] using h
  have hcomp : Dforward.comp Dreverse = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro w
    change Dforward (Dreverse w) = w
    dsimp [Dforward, Dreverse,
      GeodesicTransport.chartTransitionMFDeriv]
    have hxT' : (chartAt E x).symm zT = x := by
      simpa [extChartAt_coe] using hxT
    have hold' :
        (chartAt E x₀).symm ((chartAt E x₀) x) = x :=
      (chartAt E x₀).left_inv (by simpa [extChartAt_source] using hx)
    rw [hxT', hold']
    change Cnew (Iold (Cold (Dnew w))) = w
    calc
      Cnew (Iold (Cold (Dnew w))) = Cnew (Dnew w) := by
        have hw := congrArg (fun L : E →L[ℝ] E => L (Dnew w)) holdCLM
        simpa [ContinuousLinearMap.comp_apply] using congrArg Cnew hw
      _ = w := by
        have hw := congrArg (fun L : E →L[ℝ] E => L w) hnewCLM
        simpa [ContinuousLinearMap.comp_apply] using hw
  have hforward :
      GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x) =
        Dforward := by
    have hz : extChartAt I x₀ x ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hx
    have hsource : (extChartAt I x₀).symm (extChartAt I x₀ x) ∈
        (extChartAt I x).source := by
      rw [(extChartAt I x₀).left_inv hx]
      exact mem_extChartAt_source x
    simpa [Dforward] using
      GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
        x₀ x hz hsource
  have hreverse :
      GeodesicTransport.chartTransitionDeriv x x₀ (extChartAt I x x) =
        Dreverse := by
    have hsource : (extChartAt I x).symm (extChartAt I x x) ∈
        (extChartAt I x₀).source := by
      rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
      exact hx
    simpa [Dreverse, zT] using
      GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
        x x₀ ((extChartAt I x).map_source (mem_extChartAt_source x)) hsource
  change
    GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x)
      (GeodesicTransport.chartTransitionDeriv x x₀
        (extChartAt I x x) u) = u
  rw [hforward, hreverse]
  have hu := congrArg (fun L : E →L[ℝ] E => L u) hcomp
  simpa [ContinuousLinearMap.comp_apply] using hu

/-- A single fixed-chart PL flow transported to all nearby preferred charts.
The velocity parameter remains in the fixed `x₀` chart; its initial moving
velocity is the exact chart-transition derivative shown below. -/
structure UniformFixedVelocityPreferredChartFlowPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) where
  anchors : Set M
  anchors_mem_nhds : anchors ∈ 𝓝 x₀
  anchor_mem_fixedChartSource : anchors ⊆ (extChartAt I x₀).source
  time : ℝ
  time_pos : 0 < time
  fixedVelocityRadius : ℝ
  fixedVelocityRadius_pos : 0 < fixedVelocityRadius
  trajectory : M → E → ℝ → E × E
  initial : ∀ x ∈ anchors, ∀ v : E, ‖v‖ < fixedVelocityRadius →
    trajectory x v 0 =
      (extChartAt I x x, fixedToAnchorVelocity x₀ (x, v))
  derivative : ∀ x ∈ anchors, ∀ v : E, ‖v‖ < fixedVelocityRadius →
    ∀ t ∈ Icc (-time) time,
      HasDerivWithinAt (trajectory x v)
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x)
          (trajectory x v t))
        (Icc (-time) time) t
  position_mem_target : ∀ x ∈ anchors, ∀ v : E,
    ‖v‖ < fixedVelocityRadius → ∀ t ∈ Icc (-time) time,
      (trajectory x v t).1 ∈ (extChartAt I x).target
  position_mem_cutoffOne : ∀ x ∈ anchors, ∀ v : E,
    ‖v‖ < fixedVelocityRadius → ∀ t ∈ Icc (-time) time,
      (trajectory x v t).1 ∈ IsometryInstantiate.cutoffOneLocus x

/-- The variable-initial-state PL flow plus one joint transition neighborhood
constructs a genuinely uniform transported preferred-chart flow.  No field
identifies its endpoint with the separately chosen public `expAt`. -/
theorem exists_uniformFixedVelocityPreferredChartFlowPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (htransport : UniformPreferredChartTransportNeighborhood x₀) :
    Nonempty (UniformFixedVelocityPreferredChartFlowPackage g x₀) := by
  rcases htransport with ⟨V, hV, U, hU, hgood⟩
  rcases
      GeodesicTransport.exists_uniform_local_geodesic_chart_flow_variable_initialState_with_position_mem_neighborhood
        g x₀ hU with
    ⟨r, hr, ε, hε, a, α, hα⟩
  let z₀ : E := extChartAt I x₀ x₀
  let T : ℝ := ε / 2
  let δ : ℝ := (r : ℝ) / 2
  let W : Set M :=
    V ∩ (extChartAt I x₀).source ∩
      (extChartAt I x₀) ⁻¹' Metric.ball z₀ ((r : ℝ) / 2)
  have hT : 0 < T := by dsimp [T]; linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact half_pos (by exact_mod_cast hr)
  have hW : W ∈ 𝓝 x₀ := by
    have hsource : (extChartAt I x₀).source ∈ 𝓝 x₀ :=
      extChartAt_source_mem_nhds x₀
    have hball : Metric.ball z₀ ((r : ℝ) / 2) ∈ 𝓝 z₀ :=
      Metric.ball_mem_nhds z₀ (half_pos (by exact_mod_cast hr))
    have hpre : (extChartAt I x₀) ⁻¹'
        Metric.ball z₀ ((r : ℝ) / 2) ∈ 𝓝 x₀ := by
      simpa [z₀] using (continuousAt_extChartAt x₀).preimage_mem_nhds hball
    exact inter_mem (inter_mem hV hsource) hpre
  let sourceTrajectory : M → E → ℝ → E × E :=
    fun x v => α (extChartAt I x₀ x, v)
  let trajectory : M → E → ℝ → E × E :=
    fun x v => GeodesicTransport.chartTransitionState x₀ x
      (sourceTrajectory x v)
  have hinitialState : ∀ x ∈ W, ∀ v : E, ‖v‖ < δ →
      (extChartAt I x₀ x, v) ∈
        closedBall (z₀, (0 : E)) (r : ℝ) := by
    intro x hx v hv
    have hxball : extChartAt I x₀ x ∈
        Metric.ball z₀ ((r : ℝ) / 2) := hx.2
    have hvball : v ∈ Metric.ball (0 : E) ((r : ℝ) / 2) := by
      simpa [δ, Metric.mem_ball, dist_eq_norm] using hv
    have hprod : (extChartAt I x₀ x, v) ∈
        closedBall z₀ (r : ℝ) ×ˢ closedBall (0 : E) (r : ℝ) := by
      constructor
      · exact ball_subset_closedBall
          (Metric.ball_subset_ball (half_le_self (by exact_mod_cast hr.le)) hxball)
      · exact ball_subset_closedBall
          (Metric.ball_subset_ball (half_le_self (by exact_mod_cast hr.le)) hvball)
    simpa [closedBall_prod_same] using hprod
  have hsmallInterval : Icc (-T) T ⊆ Ioo (-ε) ε := by
    intro t ht
    dsimp [T] at ht ⊢
    constructor
    · calc
        -ε < -(ε / 2) := by linarith
        _ ≤ t := ht.1
    · calc
        t ≤ ε / 2 := ht.2
        _ < ε := by linarith
  refine ⟨{
    anchors := W
    anchors_mem_nhds := hW
    anchor_mem_fixedChartSource := fun _x hx => hx.1.2
    time := T
    time_pos := hT
    fixedVelocityRadius := δ
    fixedVelocityRadius_pos := hδ
    trajectory := trajectory
    initial := ?_
    derivative := ?_
    position_mem_target := ?_
    position_mem_cutoffOne := ?_ }⟩
  · intro x hx v hv
    have hspec := hα (extChartAt I x₀ x, v) (hinitialState x hx v hv)
    have hxSource : x ∈ (extChartAt I x₀).source := hx.1.2
    have hfixedInv : (extChartAt I x₀).symm (extChartAt I x₀ x) = x :=
      (extChartAt I x₀).left_inv hxSource
    have hsource₀ : sourceTrajectory x v 0 = (extChartAt I x₀ x, v) := by
      simpa [sourceTrajectory] using hspec.1
    change
      (GeodesicTransport.chartTransition x₀ x (sourceTrajectory x v 0).1,
        GeodesicTransport.chartTransitionDeriv x₀ x
          (sourceTrajectory x v 0).1 (sourceTrajectory x v 0).2) = _
    rw [hsource₀]
    apply Prod.ext
    · have hfixedInv' :
          (chartAt E x₀).symm ((chartAt E x₀) x) = x := by
        simpa [extChartAt_coe] using hfixedInv
      simp [GeodesicTransport.chartTransition, hfixedInv']
    · rfl
  · intro x hx v hv t ht
    have hspec := hα (extChartAt I x₀ x, v) (hinitialState x hx v hv)
    have htBig : t ∈ Icc (-ε) ε := Ioo_subset_Icc_self (hsmallInterval ht)
    have hsource : HasDerivAt (sourceTrajectory x v)
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x₀)
          (sourceTrajectory x v t)) t := by
      simpa [sourceTrajectory] using
        (hspec.2.1 t htBig).hasDerivAt
          (Icc_mem_nhds (hsmallInterval ht).1 (hsmallInterval ht).2)
    have hpositionU : (sourceTrajectory x v t).1 ∈ U := by
      simpa [sourceTrajectory] using hspec.2.2.2.1 t htBig
    have hgoodAt : (sourceTrajectory x v t).1 ∈
        chartTransitionCutoffGoodLocus x₀ x :=
      hgood x hx.1.1 hpositionU
    have hsourceN :=
      (isOpen_extChartAt_target x₀).mem_nhds hgoodAt.1.1.1
    have htargetN :
        {q : E | (extChartAt I x₀).symm q ∈
          (extChartAt I x).source} ∈ 𝓝 (sourceTrajectory x v t).1 :=
      (continuousAt_extChartAt_symm'' hgoodAt.1.1.1).preimage_mem_nhds
        ((isOpen_extChartAt_source x).mem_nhds hgoodAt.1.1.2)
    have hsourceCut :=
      IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
        hgoodAt.1.2
    have htransitionDeriv :=
      GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
        x₀ x hgoodAt.1.1.1 hgoodAt.1.1.2
    have htargetCut := htransitionDeriv.continuousAt.preimage_mem_nhds
      (IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
        hgoodAt.2)
    have hder :=
      GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
        g x₀ x hsource hsourceN htargetN hsourceCut htargetCut
    exact (by simpa [trajectory] using hder.hasDerivWithinAt)
  · intro x hx v hv t ht
    have hspec := hα (extChartAt I x₀ x, v) (hinitialState x hx v hv)
    have htBig : t ∈ Icc (-ε) ε :=
      Ioo_subset_Icc_self (hsmallInterval ht)
    have hpositionU : (sourceTrajectory x v t).1 ∈ U := by
      simpa [sourceTrajectory] using hspec.2.2.2.1 t htBig
    have hgoodAt := hgood x hx.1.1 hpositionU
    have hmap := (extChartAt I x).map_source hgoodAt.1.1.2
    simpa [trajectory, sourceTrajectory,
      GeodesicTransport.chartTransitionState,
      GeodesicTransport.chartTransition_apply] using hmap
  · intro x hx v hv t ht
    have hspec := hα (extChartAt I x₀ x, v) (hinitialState x hx v hv)
    have htBig : t ∈ Icc (-ε) ε :=
      Ioo_subset_Icc_self (hsmallInterval ht)
    have hpositionU : (sourceTrajectory x v t).1 ∈ U := by
      simpa [sourceTrajectory] using hspec.2.2.2.1 t htBig
    have hgoodAt := hgood x hx.1.1 hpositionU
    simpa [trajectory, sourceTrajectory,
      GeodesicTransport.chartTransitionState] using hgoodAt.2

/-- Local uniform operator control for converting moving-chart velocities
back to the frozen chart.  This is the quantitative condition needed to turn
the preceding fixed-velocity radius into a genuine moving-velocity radius. -/
def UniformMovingToFixedVelocityBound (x₀ : M) : Prop :=
  ∃ V : Set M, V ∈ 𝓝 x₀ ∧ ∃ K > (0 : ℝ),
    ∀ x ∈ V,
      ‖GeodesicTransport.chartTransitionDeriv x x₀
        (extChartAt I x x)‖ ≤ K

/-- Continuity at the anchor of the reverse transition derivative supplies
the required local uniform operator bound. -/
theorem uniformMovingToFixedVelocityBound_of_continuousAt
    (x₀ : M)
    (hcontinuous : ContinuousAt
      (fun x : M => GeodesicTransport.chartTransitionDeriv x x₀
        (extChartAt I x x)) x₀) :
    UniformMovingToFixedVelocityBound x₀ := by
  let D : M → E →L[ℝ] E := fun x =>
    GeodesicTransport.chartTransitionDeriv x x₀ (extChartAt I x x)
  let K : ℝ := ‖D x₀‖ + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hnorm : ContinuousAt (fun x => ‖D x‖) x₀ := by
    have hDcontinuous : ContinuousAt D x₀ := by
      simpa [D] using hcontinuous
    exact hDcontinuous.norm
  have hlt : ∀ᶠ x in nhds x₀, ‖D x‖ < K := by
    exact hnorm.eventually (Iio_mem_nhds (by dsimp [K]; linarith))
  exact ⟨{x | ‖D x‖ < K}, hlt, K, hK,
    fun x hx => by simpa [D] using hx.le⟩

/-- A transported preferred-chart flow with its input parameter expressed in
the moving preferred chart itself.  This is the full preferred trajectory
domain/ODE/target/cutoff interface except for a common state-radius field and
the deliberately absent public-`expAt` endpoint law. -/
structure UniformMovingVelocityPreferredChartFlowPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) where
  anchors : Set M
  anchors_mem_nhds : anchors ∈ 𝓝 x₀
  time : ℝ
  time_pos : 0 < time
  velocityRadius : ℝ
  velocityRadius_pos : 0 < velocityRadius
  trajectory : M → E → ℝ → E × E
  initial : ∀ x ∈ anchors, ∀ u : E, ‖u‖ < velocityRadius →
    trajectory x u 0 = (extChartAt I x x, u)
  derivative : ∀ x ∈ anchors, ∀ u : E, ‖u‖ < velocityRadius →
    ∀ t ∈ Icc (-time) time,
      HasDerivWithinAt (trajectory x u)
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x)
          (trajectory x u t))
        (Icc (-time) time) t
  position_mem_target : ∀ x ∈ anchors, ∀ u : E,
    ‖u‖ < velocityRadius → ∀ t ∈ Icc (-time) time,
      (trajectory x u t).1 ∈ (extChartAt I x).target
  position_mem_cutoffOne : ∀ x ∈ anchors, ∀ u : E,
    ‖u‖ < velocityRadius → ∀ t ∈ Icc (-time) time,
      (trajectory x u t).1 ∈ IsometryInstantiate.cutoffOneLocus x

/-- Uniform inverse-transition bounds upgrade the fixed-coordinate package to
a uniform moving-coordinate package. -/
theorem UniformFixedVelocityPreferredChartFlowPackage.toMovingVelocity
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (P : UniformFixedVelocityPreferredChartFlowPackage g x₀)
    (hbound : UniformMovingToFixedVelocityBound x₀) :
    Nonempty (UniformMovingVelocityPreferredChartFlowPackage g x₀) := by
  rcases hbound with ⟨V, hV, K, hK, hbound⟩
  let W : Set M := P.anchors ∩ V
  let δ : ℝ := P.fixedVelocityRadius / K
  have hδ : 0 < δ := div_pos P.fixedVelocityRadius_pos hK
  have hsmall : ∀ x ∈ W, ∀ u : E, ‖u‖ < δ →
      ‖movingToFixedVelocity x₀ (x, u)‖ < P.fixedVelocityRadius := by
    intro x hx u hu
    let D : E →L[ℝ] E :=
      GeodesicTransport.chartTransitionDeriv x x₀ (extChartAt I x x)
    have hD : ‖D‖ ≤ K := by simpa [D] using hbound x hx.2
    calc
      ‖movingToFixedVelocity x₀ (x, u)‖ = ‖D u‖ := rfl
      _ ≤ ‖D‖ * ‖u‖ := D.le_opNorm u
      _ ≤ K * ‖u‖ :=
        mul_le_mul_of_nonneg_right hD (norm_nonneg u)
      _ < K * δ := mul_lt_mul_of_pos_left hu hK
      _ = P.fixedVelocityRadius := by
        dsimp [δ]
        field_simp [ne_of_gt hK]
  refine ⟨{
    anchors := W
    anchors_mem_nhds := inter_mem P.anchors_mem_nhds hV
    time := P.time
    time_pos := P.time_pos
    velocityRadius := δ
    velocityRadius_pos := hδ
    trajectory := fun x u => P.trajectory x (movingToFixedVelocity x₀ (x, u))
    initial := ?_
    derivative := ?_
    position_mem_target := ?_
    position_mem_cutoffOne := ?_ }⟩
  · intro x hx u hu
    rw [P.initial x hx.1 _ (hsmall x hx u hu)]
    rw [fixedToAnchorVelocity_movingToFixedVelocity x₀ x
      (P.anchor_mem_fixedChartSource hx.1) u]
  · intro x hx u hu t ht
    exact P.derivative x hx.1 _ (hsmall x hx u hu) t ht
  · intro x hx u hu t ht
    exact P.position_mem_target x hx.1 _ (hsmall x hx u hu) t ht
  · intro x hx u hu t ht
    exact P.position_mem_cutoffOne x hx.1 _ (hsmall x hx u hu) t ht

/-- Combined uniform moving-anchor transport theorem. -/
theorem exists_uniformMovingVelocityPreferredChartFlowPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (htransport : UniformPreferredChartTransportNeighborhood x₀)
    (hbound : UniformMovingToFixedVelocityBound x₀) :
    Nonempty (UniformMovingVelocityPreferredChartFlowPackage g x₀) := by
  rcases exists_uniformFixedVelocityPreferredChartFlowPackage g x₀ htransport with
    ⟨P⟩
  exact P.toMovingVelocity hbound

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport
end Poincare
