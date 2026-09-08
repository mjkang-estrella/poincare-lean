import Poincare.Global.CartanSuppliedUniformPatchSwitch

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
namespace CartanSuppliedBufferedPairAgreement
open CartanSuppliedDifferentialSuccessor CartanSuppliedFinitePatchCover
open FixedChartUniformPreferredGermAgreement

/-- The derivative between two fixed hosts is the change between their
stored velocity frames, on the actual overlap. -/
theorem patchFrame_chartTransition {a b : M} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (D : FixedChartUniformSourceNormal.Patch g b V)
    (x : M) (hxC : x ∈ C.anchors) (hxD : x ∈ D.anchors) (v : E) :
    patchFrame D x (GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x) v) =
      patchFrame C x v := by
  have frame : ∀ {a : M} {U : Set E}
      (C : FixedChartUniformSourceNormal.Patch g a U) (hx : x ∈ C.anchors),
      (patchFrame C x : E →L[ℝ] E) = anchorFrame a x := by
    intro a U C hx
    unfold patchFrame
    rw [dif_pos hx]
    exact Classical.choose_spec (anchorFrame_isInvertible C x hx)
  let q := extChartAt I a x
  have hqa := (extChartAt I a).map_source hxC.1
  have hqb := (extChartAt I b).map_source hxD.1
  have hab : (extChartAt I a).symm q ∈ (extChartAt I b).source := by
    rw [(extChartAt I a).left_inv hxC.1]
    exact hxD.1
  have hbx : (extChartAt I b).symm (extChartAt I b x) ∈ (extChartAt I x).source := by
    rw [(extChartAt I b).left_inv hxD.1]
    exact mem_extChartAt_source x
  have hax : (extChartAt I a).symm q ∈ (extChartAt I x).source := by
    rw [(extChartAt I a).left_inv hxC.1]
    exact mem_extChartAt_source x
  have habq : GeodesicTransport.chartTransition a b q = extChartAt I b x := by
    exact congrArg (extChartAt I b) ((extChartAt I a).left_inv hxC.1)
  have hdab := (chartTransition_contDiffAt a b hqa hab).differentiableAt (by norm_num)
  have hdbx := (chartTransition_contDiffAt b x hqb hbx).differentiableAt (by norm_num)
  have hdax := (chartTransition_contDiffAt a x hqa hax).differentiableAt (by norm_num)
  have he : (GeodesicTransport.chartTransition b x ∘ GeodesicTransport.chartTransition a b)
      =ᶠ[𝓝 q] GeodesicTransport.chartTransition a x := by
    have hi := (continuousAt_extChartAt_symm'' hqa).tendsto
    filter_upwards [hi ((isOpen_extChartAt_source b).mem_nhds hab)] with z hz
    change extChartAt I x ((extChartAt I b).symm
      (extChartAt I b ((extChartAt I a).symm z))) = _
    rw [(extChartAt I b).left_inv hz]
    rfl
  rw [← habq] at hdbx
  have hd := ((hdbx.hasFDerivAt.comp q hdab.hasFDerivAt).congr_of_eventuallyEq
    he.symm).unique hdax.hasFDerivAt
  change (patchFrame D x : E →L[ℝ] E) _ = (patchFrame C x : E →L[ℝ] E) _
  rw [frame C hxC, frame D hxD]
  simpa only [anchorFrame, GeodesicTransport.chartTransitionDeriv, habq,
    ContinuousLinearMap.comp_apply] using congrArg (fun A : E →L[ℝ] E => A v) hd

/-- A fixed chart transition has one operator bound over a compact overlap. -/
theorem exists_uniform_chartTransition_bound {a b : M} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (D : FixedChartUniformSourceNormal.Patch g b V)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) (hKD : K ⊆ D.anchors) :
    ∃ R > (0 : ℝ), ∀ x ∈ K,
      ‖GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x)‖ ≤ R := by
  let J := fun x : M => GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x)
  have hc : ContinuousOn J K := by
    intro x hx
    have ht := (extChartAt I a).map_source (hKC hx).1
    have hs : (extChartAt I a).symm (extChartAt I a x) ∈ (extChartAt I b).source := by
      rw [(extChartAt I a).left_inv (hKC hx).1]
      exact (hKD hx).1
    exact ((chartTransition_contDiffAt a b ht hs).continuousAt_fderiv (by norm_num)
      |>.comp (continuousAt_extChartAt' (hKC hx).1)).continuousWithinAt
  obtain ⟨R, hR, hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨R, hR, fun x hx => hb _ ⟨x, hx, rfl⟩⟩

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- One velocity radius keeps every normalized trajectory in both fixed
hosts and transports its geodesic equation on the entire unit interval. -/
theorem exists_uniform_transported_flow_radius {a b : M} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (D : FixedChartUniformSourceNormal.Patch g b V)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus a)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus b)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) (hKD : K ⊆ D.anchors) :
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ v : E, ‖v‖ < ρ →
      let q := (extChartAt I a x, C.T⁻¹ • v)
      let γ := fun t : ℝ => ((C.α q (C.T * t)).1, C.T • (C.α q (C.T * t)).2)
      let β := GeodesicTransport.chartTransitionState a b γ
      q ∈ closedBall (extChartAt I a a, 0) (C.r : ℝ) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (γ t).1 ∈ (extChartAt I a).target ∧
        (extChartAt I a).symm (γ t).1 ∈ D.anchors) ∧
      ContinuousOn β (Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt β
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g b) (β t)) t := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨ε, hε, hεD⟩ := hK.exists_cthickening_subset_open D.isOpen_anchors hKD
  obtain ⟨ρ, hρ, hflow⟩ := FixedChartMappedGeodesicAssembly.exists_uniform_flow_displacement_radius
    C K hK hKC hε
  refine ⟨ρ, hρ, ?_⟩
  intro x hx v hv
  obtain ⟨hq, hpositions⟩ := hflow x hx v hv
  let q := (extChartAt I a x, C.T⁻¹ • v)
  let γ := fun t : ℝ => ((C.α q (C.T * t)).1, C.T • (C.α q (C.T * t)).2)
  let F := GeodesicTransport.chartTransition (n := 3) a b
  let β := GeodesicTransport.chartTransitionState a b γ
  have htime : ∀ t ∈ Icc (0 : ℝ) 1, C.T * t ∈ Icc (-C.T) C.T := by
    intro t ht
    constructor <;> nlinarith [C.T_pos, ht.1, ht.2]
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1,
      (γ t).1 ∈ (extChartAt I a).target ∧ (extChartAt I a).symm (γ t).1 ∈ D.anchors := by
    intro t ht
    obtain ⟨hchart, hdist⟩ := hpositions (C.T * t) (htime t ht)
    exact ⟨hchart, hεD (mem_cthickening_of_dist_le _ x ε K hx hdist.le)⟩
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ
      (geodesicFlowField (GeodesicTransport.chartChristoffelField g a) (γ t))
      (Icc (0 : ℝ) 1) t := fun _ ht =>
    FixedChartUniformEndpointReanchoring.normalizedFlow_hasDerivWithinAt C hq ht
  have hc := HasDerivWithinAt.continuousOn hd
  refine ⟨hq, hpos, ?_, ?_⟩
  · intro t ht
    have hF := chartTransition_contDiffAt a b (hpos t ht).1 (hpos t ht).2.1
    exact (hF.continuousAt.comp_continuousWithinAt (f := fun s => (γ s).1) (hc.fst t ht)).prodMk
      (((hF.continuousAt_fderiv (by norm_num)).comp_continuousWithinAt
        (f := fun s => (γ s).1) (hc.fst t ht)).clm_apply (hc.snd t ht))
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hy := (hpos t ht').2
    have hF := chartTransition_contDiffAt a b (hpos t ht').1 hy.1
    have hcutC := (FixedChartMovingPositionJacobi.flow_mem_target_cutoffOne C hU hq
      (htime t ht')).2
    have hcutD : ∀ᶠ w in 𝓝 (F (γ t).1), GeodesicTransport.cutoff (n := 3) b w = 1 := by
      have hzero := D.endpoint_source_initial_mem (D.zero_mem_endpoint_source _ hy)
      have h := (FixedChartMovingPositionJacobi.flow_mem_target_cutoffOne D hV hzero
        (show (0 : ℝ) ∈ Icc (-D.T) D.T by constructor <;> linarith [D.T_pos])).2
      rw [(D.flow_law _ hzero).1] at h
      exact h
    exact GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds g a b
      ((hd t ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      ((isOpen_extChartAt_target a).mem_nhds (hpos t ht').1)
      ((continuousAt_extChartAt_symm'' (hpos t ht').1).tendsto
        ((isOpen_extChartAt_source b).mem_nhds hy.1))
      hcutC (hF.continuousAt.tendsto.eventually hcutD)

end CartanSuppliedBufferedPairAgreement
end Poincare
