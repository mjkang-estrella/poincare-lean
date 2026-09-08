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
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt β
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g b) (β t))
        (Icc (0 : ℝ) 1) t := by
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
    have ht' := ht
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
    have htrans := GeodesicTransport.chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one
      (g := g) (x₀ := a) (y₀ := b) (z := (γ t).1)
      ((isOpen_extChartAt_target a).mem_nhds (hpos t ht').1)
      ((continuousAt_extChartAt_symm'' (hpos t ht').1).tendsto
        ((isOpen_extChartAt_source b).mem_nhds hy.1))
      hcutC (hF.continuousAt.tendsto.eventually hcutD) (γ t).2 (γ t).2
    exact FixedChartUniformEndpointReanchoring.mappedState_hasDerivWithinAt_of_differentiable_fderiv
      F _ _ (hd t ht) (hF.differentiableAt (by norm_num))
      ((hF.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
        (by norm_num)) htrans

/-- The two retained endpoints agree after the host chart derivative, with
one velocity radius chosen before the anchor in the compact overlap. -/
theorem exists_uniform_endpoint_chartTransition {a b : M} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (D : FixedChartUniformSourceNormal.Patch g b V)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus a)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus b)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) (hKD : K ⊆ D.anchors) :
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ v : E, ‖v‖ < ρ →
      v ∈ (C.endpoint x).source ∧
      GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x) v ∈
        (D.endpoint x).source ∧
      C.endpoint x v = D.endpoint x
        (GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x) v) := by
  obtain ⟨ρf, hρf, hf⟩ := exists_uniform_transported_flow_radius C D hU hV K hK hKC hKD
  obtain ⟨ρC, hρC, hC⟩ := FixedChartLocalSuccessorExistence.exists_uniform_endpoint_radius C K hK hKC
  obtain ⟨ρD, hρD, hD⟩ := FixedChartLocalSuccessorExistence.exists_uniform_endpoint_radius D K hK hKD
  obtain ⟨R, hR, hbound⟩ := exists_uniform_chartTransition_bound C D K hK hKC hKD
  refine ⟨min ρf (min ρC (ρD / R)), lt_min hρf (lt_min hρC (div_pos hρD hR)), ?_⟩
  intro x hx v hv
  let w := GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x) v
  have hw : ‖w‖ < ρD := by
    calc
      _ ≤ ‖GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x)‖ * ‖v‖ :=
        (GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x)).le_opNorm v
      _ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg v)
      _ < ρD := by
        have h := (hv.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
        simpa only [mul_comm R] using (lt_div_iff₀ hR).mp h
  have hvsrc := (hC x hx v ((hv.trans_le (min_le_right _ _)).trans_le (min_le_left _ _))).1
  have hwsrc := (hD x hx w hw).1
  obtain ⟨hq, hpositions, hβc, hβd⟩ := hf x hx v (hv.trans_le (min_le_left _ _))
  let q := (extChartAt I a x, C.T⁻¹ • v)
  let γ := fun t : ℝ => ((C.α q (C.T * t)).1, C.T • (C.α q (C.T * t)).2)
  let β := GeodesicTransport.chartTransitionState a b γ
  let r := (extChartAt I b x, D.T⁻¹ • w)
  let η := fun t : ℝ => ((D.α r (D.T * t)).1, D.T • (D.α r (D.T * t)).2)
  have hr := D.endpoint_source_initial_mem hwsrc
  have hηd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt η
      (geodesicFlowField (GeodesicTransport.chartChristoffelField g b) (η t))
      (Icc (0 : ℝ) 1) t := fun _ ht =>
    FixedChartUniformEndpointReanchoring.normalizedFlow_hasDerivWithinAt D hr ht
  have hηc := HasDerivWithinAt.continuousOn hηd
  have hγ0 : γ 0 = (extChartAt I a x, v) := by
    have hq0 : C.α q 0 = q := (C.flow_law _ hq).1
    dsimp only [γ]
    rw [mul_zero, hq0]
    simp [q, smul_smul, C.T_pos.ne']
  have hη0 : η 0 = (extChartAt I b x, w) := by
    have hr0 : D.α r 0 = r := (D.flow_law _ hr).1
    dsimp only [η]
    rw [mul_zero, hr0]
    simp [r, smul_smul, D.T_pos.ne']
  have h0 : β 0 = η 0 := by
    change (GeodesicTransport.chartTransition a b (γ 0).1,
      GeodesicTransport.chartTransitionDeriv a b (γ 0).1 (γ 0).2) = _
    rw [hγ0, hη0]
    exact Prod.ext (congrArg (extChartAt I b) ((extChartAt I a).left_inv (hKC hx).1)) rfl
  obtain ⟨R', hR'⟩ := ((isCompact_Icc.image_of_continuousOn hβc).union
    (isCompact_Icc.image_of_continuousOn hηc)).isBounded.subset_closedBall (0 : E × E)
  obtain ⟨A, hA⟩ := GeodesicTransport.geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
    g b (0 : E × E) R'
  have heq : EqOn β η (Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => geodesicFlowField (GeodesicTransport.chartChristoffelField g b))
      (s := fun _ => closedBall (0 : E × E) R')
      (fun _ _ => hA) hβc
      (fun t ht => (hβd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hR' (Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)) hηc
      (fun t ht => (hηd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hR' (Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩)) h0
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hend := congrArg (fun s : E × E => (extChartAt I b).symm s.1) (heq h1)
  refine ⟨hvsrc, hwsrc, ?_⟩
  have hCb : (extChartAt I a).symm (C.α q C.T).1 ∈ (extChartAt I b).source := by
    simpa only [mul_one] using (hpositions 1 h1).2.1
  change (extChartAt I b).symm (extChartAt I b
    ((extChartAt I a).symm (C.α q (C.T * 1)).1)) =
    (extChartAt I b).symm (D.α r (D.T * 1)).1 at hend
  rw [mul_one, mul_one, (extChartAt I b).left_inv hCb] at hend
  simpa only [C.endpoint_apply, D.endpoint_apply,
    FixedChartUniformNormalRadius.expChart] using hend

/-- Inverting the uniformly compared endpoints gives the actual normal
transition law, including both normal source domains. -/
theorem exists_uniform_normal_chartTransition {a b : M} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (D : FixedChartUniformSourceNormal.Patch g b V)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus a)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus b)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) (hKD : K ⊆ D.anchors) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ z : M, dist z x < ρ →
      z ∈ (C.normal x).source ∩ (D.normal x).source ∧
      D.normal x z = GeodesicTransport.chartTransitionDeriv a b
        (extChartAt I a x) (C.normal x z) := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨r, hr, he⟩ := exists_uniform_endpoint_chartTransition C D hU hV K hK hKC hKD
  obtain ⟨ρC, hρC, hC⟩ := FixedChartLocalSuccessorExistence.exists_uniform_normal_radius C K hK hKC hr
  obtain ⟨ρD, hρD, hD⟩ := FixedChartLocalSuccessorExistence.exists_uniform_normal_radius D K hK hKD zero_lt_one
  refine ⟨min ρC ρD, lt_min hρC hρD, ?_⟩
  intro x hx z hz
  obtain ⟨_, hzC, hv⟩ := hC x hx z (hz.trans_le (min_le_left _ _))
  have hzD := (hD x hx z (hz.trans_le (min_le_right _ _))).2.1
  obtain ⟨_, hw, heq⟩ := he x hx (C.normal x z) hv
  have hleft : C.endpoint x (C.normal x z) = z := (C.normal x).left_inv hzC
  rw [hleft] at heq
  refine ⟨⟨hzC, hzD⟩, ?_⟩
  exact (congrArg (D.normal x) heq).trans ((D.endpoint x).left_inv hw)

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The intrinsic alignment commutes with both host changes. Its two output
vectors are related by the target transition, rather than equal coordinates. -/
theorem linear_chartTransition_of_normal_chartTransition
    {a b : M} {c d : RoundSphere3} {U V W Z : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (C' : FixedChartUniformSourceNormal.Patch g b V)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 c W)
    (D' : FixedChartUniformSourceNormal.Patch roundSphereMetric3 d Z)
    (x : M) (hxC : x ∈ C.anchors) (hxC' : x ∈ C'.anchors)
    (p : RoundSphere3) (hpD : p ∈ D.anchors) (hpD' : p ∈ D'.anchors)
    (L : CartanMap.TangentAlignment g x p) (z : M)
    (hn : C'.normal x z = GeodesicTransport.chartTransitionDeriv a b
      (extChartAt I a x) (C.normal x z)) :
    GeodesicTransport.chartTransitionDeriv c d (extChartAt I c p)
      (linear (patch C D) ⟨x, p, L⟩ (C.normal x z)) =
      linear (patch C' D') ⟨x, p, L⟩ (C'.normal x z) := by
  have hsource : patchFrame C' x (C'.normal x z) = patchFrame C x (C.normal x z) := by
    rw [hn]
    exact patchFrame_chartTransition C C' x hxC hxC' _
  apply (patchFrame D' p).injective
  rw [patchFrame_chartTransition D D' p hpD hpD']
  simpa only [linear, patch, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply] using congrArg L hsource.symm

end CartanSuppliedBufferedPairAgreement
end Poincare
