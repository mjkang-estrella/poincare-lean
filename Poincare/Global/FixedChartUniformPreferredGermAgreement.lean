import Poincare.Global.FixedChartUniformSourceNormal
import Poincare.Global.CartanSuppliedSourceGermTransfer
import Poincare.Global.ChartTransitionGeodesicMap
import Poincare.Global.CartanFixedChartGenericInverseEndpointODEPrimitive

/-!
# Fixed-anchor frame and inverse comparison for a retained flow

The preferred-frame derivative is invertible on every retained chart overlap.
Endpoint agreement transfers to inverse normal coordinates on their actual
open domains. The remaining interval comparison is stated explicitly below.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology ContDiff NNReal Manifold

namespace Poincare.FixedChartUniformPreferredGermAgreement

universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
variable (C : FixedChartUniformSourceNormal.Patch g x₀ U)

/-- The fixed-chart velocity expressed in the preferred frame of the anchor. -/
def anchorFrame (x₀ x : M) : E →L[ℝ] E :=
  GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x)

/-- Both chart differentials are invertible on the retained overlap. -/
theorem anchorFrame_isInvertible (x : M) (hx : x ∈ C.anchors) :
    (anchorFrame x₀ x).IsInvertible := by
  have hz := (extChartAt I x₀).map_source hx.1
  have hy : (extChartAt I x₀).symm (extChartAt I x₀ x) ∈
      (extChartAt I x).source := by
    rw [(extChartAt I x₀).left_inv hx.1]
    exact mem_extChartAt_source x
  rw [anchorFrame, GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
    x₀ x hz hy]
  exact (isInvertible_mfderiv_extChartAt hy).comp
    (isInvertible_mfderivWithin_extChartAt_symm hz)

/-- Equality of endpoint germs gives equality of inverse normal germs.
Continuity pulls the velocity neighborhood back to the anchor, where both
partial inverse laws apply. -/
theorem normal_eventuallyEq_generic_in_anchor_frame_of_endpoint_agreement
    (x : M) (hx : x ∈ C.anchors)
    (h : (C.endpoint x : E → M) =ᶠ[𝓝 (0 : E)]
      (fun v => GeodesicTransport.expAt g x (anchorFrame x₀ x v))) :
    (fun z : M => anchorFrame x₀ x (C.normal x z)) =ᶠ[𝓝 x]
      (fun z : M => (CartanSourceExponential.genericFamily g).normal x z) := by
  have hn : Tendsto (C.normal x) (𝓝 x) (𝓝 (0 : E)) := by
    simpa only [C.normal_anchor x hx] using
      ((C.normal x).continuousAt (C.anchor_mem_normal_source x hx)).tendsto
  have hJ : Tendsto (anchorFrame x₀ x) (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using ((anchorFrame x₀ x).continuous.continuousAt (x := (0 : E))).tendsto
  have hinv := GeodesicTransport.expAtChartOpenPartialHomeomorph_eventually_left_inverse g x
  filter_upwards [hn h, (hJ.comp hn) hinv,
    (C.normal x).open_source.mem_nhds (C.anchor_mem_normal_source x hx)] with z hz hi hs
  have he : GeodesicTransport.expAt g x (anchorFrame x₀ x (C.normal x z)) = z :=
    hz.symm.trans ((C.normal x).left_inv hs)
  change (GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm
    (extChartAt I x (GeodesicTransport.expAt g x
      (anchorFrame x₀ x (C.normal x z)))) = anchorFrame x₀ x (C.normal x z) at hi
  rw [he] at hi
  exact hi.symm

/-- At a fixed anchor, all sufficiently small initial velocities stay in any
prescribed position neighborhood for the entire retained time interval. -/
theorem eventually_position_mem_forall_time (x : M) (hx : x ∈ C.anchors)
    {V : Set E} (hV : V ∈ 𝓝 (extChartAt I x₀ x)) :
    ∀ᶠ w : E in 𝓝 (0 : E), ∀ t ∈ Icc (-C.T) C.T,
      (C.α (extChartAt I x₀ x, w) t).1 ∈ V := by
  let K := Icc (-C.T) C.T
  let z := extChartAt I x₀ x
  have hq : (z, (0 : E)) ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ) :=
    ball_subset_closedBall (C.P_source_subset (C.zero_mem_source z hx.2))
  have hstat : ∀ t ∈ K, C.α (z, 0) t = (z, 0) :=
    FixedChartUniformNormalRadius.flow_zero_velocity
      (contDiff_geodesicFlowField (GeodesicTransport.chartChristoffelField_contDiff g x₀))
      C.T_pos (C.flow_law _ hq).1 (C.flow_law _ hq).2
  let D : Set (E × K) := {p | (z, p.1) ∈ C.P.source}
  have hopen : IsOpen D := C.P.open_source.preimage
    (continuous_const.prodMk continuous_fst)
  have hc : ContinuousOn (fun p : E × K => (C.α (z, p.1) p.2).1) D := by
    apply C.continuous_flow.fst.comp
      ((continuous_const.prodMk continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p hp
    exact ⟨ball_subset_closedBall (C.P_source_subset hp), p.2.property⟩
  have he : ∀ᶠ w : E in 𝓝 (0 : E), ∀ t : K,
      (C.α (z, w) t).1 ∈ V := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (X := E) (Y := K) (x₀ := (0 : E))
      (P := fun w t => (C.α (z, w) t).1 ∈ V) (fun t _ => ?_)
    · simpa only [mem_univ, forall_const] using h
    have hc' := hc.continuousAt (hopen.mem_nhds
      (show ((0 : E), t) ∈ D from C.zero_mem_source z hx.2))
    have hv' : V ∈ 𝓝 ((C.α (z, 0) t).1) := by
      rw [hstat t t.property]
      exact hV
    exact hc'.tendsto hv'
  filter_upwards [he] with w hw t ht
  exact hw ⟨t, ht⟩

/-- Chart transitions are smooth at points of the actual overlap. -/
theorem chartTransition_contDiffAt (a b : M) {z : E}
    (hz : z ∈ (extChartAt I a).target)
    (hb : (extChartAt I a).symm z ∈ (extChartAt I b).source) :
    ContDiffAt ℝ 2 (GeodesicTransport.chartTransition a b) z := by
  have hb' : (extChartAt I a).symm z ∈ (chartAt E b).source := by
    rwa [extChartAt_source] at hb
  have ho : ContMDiffAt I (modelWithCornersSelf ℝ E) 2 (extChartAt I b)
      ((extChartAt I a).symm z) := contMDiffAt_extChartAt' hb'
  have hiw : ContMDiffWithinAt (modelWithCornersSelf ℝ E) I 2
      ((extChartAt I a).symm) (range I) z :=
    contMDiffWithinAt_extChartAt_symm_range a hz
  have hi : ContMDiffAt (modelWithCornersSelf ℝ E) I 2
      ((extChartAt I a).symm) z := by
    simpa [ModelWithCorners.range_eq_univ] using hiw
  exact contMDiffAt_iff_contDiffAt.mp
    (by simpa [GeodesicTransport.chartTransition, Function.comp_def] using ho.comp z hi)

/-- Small fixed-anchor trajectories satisfy the preferred-frame ODE on the
whole retained interval, with continuity at both endpoints. -/
theorem eventually_transported_solves
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (x : M) (hx : x ∈ C.anchors) :
    ∀ᶠ w : E in 𝓝 (0 : E),
      ContinuousOn (GeodesicTransport.chartTransitionState x₀ x
        (C.α (extChartAt I x₀ x, w))) (Icc (-C.T) C.T) ∧
      ∀ t ∈ Ioo (-C.T) C.T,
        HasDerivAt (GeodesicTransport.chartTransitionState x₀ x
          (C.α (extChartAt I x₀ x, w)))
          (geodesicFlowField (GeodesicTransport.chartChristoffelField g x)
            (GeodesicTransport.chartTransitionState x₀ x
              (C.α (extChartAt I x₀ x, w)) t)) t := by
  let z := extChartAt I x₀ x
  let F := GeodesicTransport.chartTransition (n := 3) x₀ x
  have hz : z ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source hx.1
  have hinv : (extChartAt I x₀).symm z = x := (extChartAt I x₀).left_inv hx.1
  have hx' : (extChartAt I x₀).symm z ∈ (extChartAt I x).source := by
    rw [hinv]; exact mem_extChartAt_source x
  have hq : (z, (0 : E)) ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ) :=
    ball_subset_closedBall (C.P_source_subset (C.zero_mem_source z hx.2))
  have hzU : z ∈ U := by
    have h := C.position_mem (z, 0) hq 0 (by constructor <;> linarith [C.T_pos])
    rw [(C.flow_law _ hq).1] at h
    exact h
  let V : Set E := {q | ∀ᶠ r in 𝓝 q,
    r ∈ (extChartAt I x₀).target ∧
    (extChartAt I x₀).symm r ∈ (extChartAt I x).source ∧
    GeodesicTransport.cutoff (n := 3) x₀ r = 1 ∧
    GeodesicTransport.cutoff (n := 3) x (F r) = 1}
  have hV : V ∈ 𝓝 z := by
    apply isOpen_setOf_eventually_nhds.mem_nhds
    have h1 := (isOpen_extChartAt_target x₀).mem_nhds hz
    have h2 := (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
      ((isOpen_extChartAt_source x).mem_nhds hx')
    have h3 := IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus (hU hzU)
    have h4 : ∀ᶠ r in 𝓝 z, GeodesicTransport.cutoff (n := 3) x (F r) = 1 := by
      have hf : F z = extChartAt I x x := by
        simp only [F, GeodesicTransport.chartTransition_apply, hinv]
      have ht : ∀ᶠ r in 𝓝 (F z), GeodesicTransport.cutoff (n := 3) x r = 1 := by
        rw [hf]
        exact GeodesicTransport.cutoff_eventuallyEq_one x
      exact (chartTransition_contDiffAt x₀ x hz hx').continuousAt.tendsto.eventually ht
    filter_upwards [h1, h2, h3, h4] with r h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hsmall : ∀ᶠ w : E in 𝓝 (0 : E), (z, w) ∈ C.P.source :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (C.P.open_source.mem_nhds (C.zero_mem_source z hx.2))
  filter_upwards [eventually_position_mem_forall_time C x hx hV, hsmall] with w hw hws
  have hq' := ball_subset_closedBall (C.P_source_subset hws)
  have hd := (C.flow_law (z, w) hq').2
  have hc := HasDerivWithinAt.continuousOn hd
  have hgood : ∀ t ∈ Icc (-C.T) C.T,
      (C.α (z, w) t).1 ∈ (extChartAt I x₀).target ∧
      (extChartAt I x₀).symm (C.α (z, w) t).1 ∈ (extChartAt I x).source := by
    intro t ht
    exact (mem_of_mem_nhds (hw t ht)).imp_right And.left
  constructor
  · intro t ht
    have hF := chartTransition_contDiffAt x₀ x (hgood t ht).1 (hgood t ht).2
    have hpos := hc.fst t ht
    have hvel := hc.snd t ht
    have hfirst := hF.continuousAt.comp_continuousWithinAt (f := fun s : ℝ => (C.α (z, w) s).1) hpos
    have hsecond := (hF.continuousAt_fderiv (by norm_num)).comp_continuousWithinAt (f := fun s : ℝ => (C.α (z, w) s).1) hpos
    exact hfirst.prodMk (hsecond.clm_apply hvel)
  · intro t ht
    have hh := hw t (Ioo_subset_Icc_self ht)
    exact GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
      g x₀ x ((hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (hh.mono fun _ h => h.1) (hh.mono fun _ h => h.2.1)
      (hh.mono fun _ h => h.2.2.1) (hh.mono fun _ h => h.2.2.2)

/-- The normalized retained endpoint agrees with the preferred exponential
at each fixed anchor. The velocity neighborhood may depend on that anchor. -/
theorem normalized_endpoint_eventuallyEq_expAt
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (x : M) (hx : x ∈ C.anchors) :
    (fun v : E => (extChartAt I x₀).symm
      (FixedChartUniformNormalRadius.expChart C.α C.T
        (extChartAt I x₀ x) (C.T⁻¹ • v))) =ᶠ[𝓝 (0 : E)]
      (fun v : E => GeodesicTransport.expAt g x (anchorFrame x₀ x v)) := by
  obtain ⟨P⟩ := GeodesicTransport.exists_preferredChartExpAtTrajectoryPackage g x
  let Q := P.reparameterize C.T C.T_pos
  have hQt : Q.time = C.T := rfl
  have hscale : Tendsto (fun v : E => C.T⁻¹ • v) (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [id_eq, smul_zero] using
      ((continuous_id.const_smul C.T⁻¹).continuousAt (x := (0 : E))).tendsto
  have hJ : Tendsto (anchorFrame x₀ x) (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using
      ((anchorFrame x₀ x).continuous.continuousAt (x := (0 : E))).tendsto
  have hsmall : ∀ᶠ v : E in 𝓝 (0 : E),
      ‖anchorFrame x₀ x (C.T⁻¹ • v)‖ < Q.velocityRadius := by
    simpa only [mem_ball, dist_zero_right] using
      (hJ.comp hscale).eventually (ball_mem_nhds (0 : E) Q.velocityRadius_pos)
  have hendsource := (C.endpoint x).open_source.mem_nhds (C.zero_mem_endpoint_source x hx)
  have hend : Tendsto (C.endpoint x) (𝓝 (0 : E)) (𝓝 x) := by
    simpa only [C.endpoint_zero x hx] using
      ((C.endpoint x).continuousAt (C.zero_mem_endpoint_source x hx)).tendsto
  have hchart : ∀ᶠ v : E in 𝓝 (0 : E), C.endpoint x v ∈ (extChartAt I x).source :=
    hend.eventually ((isOpen_extChartAt_source x).mem_nhds
    (mem_extChartAt_source x))
  filter_upwards [hscale.eventually (eventually_transported_solves C hU x hx),
    hsmall, hendsource, hchart] with v hsol hv hvs hvchart
  let w := C.T⁻¹ • v
  let u := anchorFrame x₀ x w
  let γ := GeodesicTransport.chartTransitionState x₀ x
    (C.α (extChartAt I x₀ x, w))
  let η := Q.trajectory u
  have hu : ‖u‖ < Q.velocityRadius := hv
  have hγc : ContinuousOn γ (Icc (-C.T) C.T) := hsol.1
  have hηd : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt η
      (geodesicFlowField (GeodesicTransport.chartChristoffelField g x) (η t))
      (Icc (-C.T) C.T) t := by
    simpa only [hQt] using Q.derivative u hu
  have hηc := HasDerivWithinAt.continuousOn hηd
  obtain ⟨R, hR⟩ := ((isCompact_Icc.image_of_continuousOn hγc).union
    (isCompact_Icc.image_of_continuousOn hηc)).isBounded.subset_closedBall
      (extChartAt I x x, (0 : E))
  obtain ⟨K, hK⟩ :=
    GeodesicTransport.geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
      g x (extChartAt I x x, (0 : E)) R
  have hinit : γ 0 = η 0 := by
    have h0 := (C.flow_law _ (C.endpoint_source_initial_mem hvs)).1
    have hη0 := Q.initial u hu
    change C.α (extChartAt I x₀ x, w) 0 = (extChartAt I x₀ x, w) at h0
    dsimp only [γ, η, GeodesicTransport.chartTransitionState]
    rw [h0, hη0]
    apply Prod.ext
    · exact congrArg (extChartAt I x) ((extChartAt I x₀).left_inv hx.1)
    · rfl
  have heq : EqOn γ η (Icc (-C.T) C.T) :=
    ODE_solution_unique_of_mem_Icc
      (v := fun _ => geodesicFlowField (GeodesicTransport.chartChristoffelField g x))
      (s := fun _ => closedBall (extChartAt I x x, (0 : E)) R)
      (fun _ _ => hK) (by constructor <;> linarith [C.T_pos]) hγc hsol.2
      (fun t ht => hR (Or.inl (mem_image_of_mem γ (Ioo_subset_Icc_self ht)))) hηc
      (fun t ht => (hηd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (fun t ht => hR (Or.inr (mem_image_of_mem η (Ioo_subset_Icc_self ht)))) hinit
  have ht : C.T ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], le_rfl⟩
  have hexp := Q.expAt_eq u hu C.T (by rw [hQt]; exact ⟨C.T_pos.le, le_rfl⟩)
  have hTu : C.T • u = anchorFrame x₀ x v := by
    simp [u, w, map_smul, smul_smul, C.T_pos.ne']
  rw [hTu] at hexp
  have hcoord : extChartAt I x (C.endpoint x v) = (γ C.T).1 := by
    rw [C.endpoint_apply]
    rfl
  calc
    (extChartAt I x₀).symm
        (FixedChartUniformNormalRadius.expChart C.α C.T
          (extChartAt I x₀ x) (C.T⁻¹ • v)) = C.endpoint x v := (C.endpoint_apply x v).symm
    _ = (extChartAt I x).symm (extChartAt I x (C.endpoint x v)) :=
      ((extChartAt I x).left_inv hvchart).symm
    _ = (extChartAt I x).symm (η C.T).1 := by rw [hcoord, heq ht]
    _ = GeodesicTransport.expAt g x (anchorFrame x₀ x v) := hexp.symm

end Poincare.FixedChartUniformPreferredGermAgreement
