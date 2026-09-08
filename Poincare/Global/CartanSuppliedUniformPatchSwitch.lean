import Poincare.Global.CartanSuppliedFinitePatchCover

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor

namespace CartanSuppliedUniformPatchSwitch
open CartanSuppliedFinitePatchCover

structure SwitchControl (B : QuantitativeCover g) where
  radius : ℝ
  radius_pos : 0 < radius
  agreement : letI : MetricSpace M := g.toMetricSpace
    ∀ (a b : B.Label) (s : CartanChain.ChainState g),
      B.Buffered a s → B.Buffered b s →
      ball s.anchor radius ⊆ (germ (B.interp a) s).source ∩ (germ (B.interp b) s).source ∧
      EqOn (map (B.interp a) s) (map (B.interp b) s) (ball s.anchor radius)

structure System (g : ClosedSmoothRiemannianMetric 3 M) where
  cover : QuantitativeCover g
  switch : SwitchControl cover

def System.mesh (S : System g) : ℝ :=
  min S.cover.step (min S.cover.evaluation
    (min S.cover.retention S.switch.radius)) / 32

/-- Buffered interpretations represent the same germ at their common geometric anchor. -/
theorem buffered_eventuallyEq : ∀ (B : QuantitativeCover g)
    (a b : B.Label) (s : CartanChain.ChainState g),
    B.Buffered a s → B.Buffered b s →
    map (B.interp a) s =ᶠ[𝓝 s.anchor] map (B.interp b) s := by
  intro B a b s ha hb
  have hlocal : ∀ c : B.Label, B.Buffered c s →
      map (B.interp c) s =ᶠ[𝓝 s.anchor] s.map := by
    intro c hc
    exact CartanSuppliedDifferentialTransfer.patch_germ_eventuallyEq_generic
      (B.source.center c.1) (B.target.center c.2)
      (B.source.zone c.1) (B.target.zone c.2)
      (B.source.patch c.1) (B.target.patch c.2)
      (B.source.cutoff c.1) (B.target.cutoff c.2) s
      (B.source.buffer_subset c.1 hc.1) (B.target.buffer_subset c.2 hc.2)
  exact (hlocal a ha).trans (hlocal b hb).symm

/-- H1 already supplies one common source ball for every buffered patch pair. -/
theorem buffered_common_source (B : QuantitativeCover g) (a b : B.Label)
    (s : CartanChain.ChainState g) (ha : B.Buffered a s) (hb : B.Buffered b s) :
    letI : MetricSpace M := g.toMetricSpace
    ball s.anchor B.step ⊆ (germ (B.interp a) s).source ∩
      (germ (B.interp b) s).source := by
  letI : MetricSpace M := g.toMetricSpace
  intro z hz
  exact ⟨(B.h1 a.1 a.2 s.anchor ha.1 s.target ha.2 s.alignment z hz).2.2.1,
    (B.h1 b.1 b.2 s.anchor hb.1 s.target hb.2 s.alignment z hz).2.2.1⟩

/-- At each fixed state, a finite minimum works for every buffered label pair.
The radius here is still selected after the state, including its alignment. -/
theorem exists_state_switch_radius (B : QuantitativeCover g)
    (s : CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ρ > (0 : ℝ), ∀ a b : B.Label, B.Buffered a s → B.Buffered b s →
      ball s.anchor ρ ⊆ (germ (B.interp a) s).source ∩ (germ (B.interp b) s).source ∧
      EqOn (map (B.interp a) s) (map (B.interp b) s) (ball s.anchor ρ) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hpairs : ∀ c : B.Label × B.Label, ∃ r > (0 : ℝ),
      B.Buffered c.1 s → B.Buffered c.2 s →
      ball s.anchor r ⊆ (germ (B.interp c.1) s).source ∩
        (germ (B.interp c.2) s).source ∧
      EqOn (map (B.interp c.1) s) (map (B.interp c.2) s) (ball s.anchor r) := by
    intro c
    by_cases ha : B.Buffered c.1 s
    · by_cases hb : B.Buffered c.2 s
      · obtain ⟨r, hr, heq⟩ := Metric.mem_nhds_iff.mp
          (buffered_eventuallyEq B c.1 c.2 s ha hb)
        refine ⟨min r B.step, lt_min hr B.step_pos, fun _ _ => ⟨?_, ?_⟩⟩
        · exact (ball_subset_ball (min_le_right _ _)).trans
            (buffered_common_source B c.1 c.2 s ha hb)
        · exact fun _ hz => heq (ball_subset_ball (min_le_left _ _) hz)
      · exact ⟨1, zero_lt_one, fun _ h => (hb h).elim⟩
    · exact ⟨1, zero_lt_one, fun h => (ha h).elim⟩
  letI : Fintype B.Label := inferInstanceAs
    (Fintype (Fin B.source.count × Fin B.target.count))
  choose r hr hagree using hpairs
  obtain ⟨ρ, hρ, hle⟩ := exists_positive_lower_bound r hr
  refine ⟨ρ, hρ, ?_⟩
  intro a b ha hb
  obtain ⟨hs, he⟩ := hagree (a, b) ha hb
  exact ⟨(ball_subset_ball (hle (a, b))).trans hs,
    he.mono (ball_subset_ball (hle (a, b)))⟩

/-- All four geometric radii contribute a positive operating mesh. -/
theorem mesh_pos : ∀ S : System g, 0 < S.mesh := by
  intro S
  exact div_pos (lt_min S.cover.step_pos (lt_min S.cover.evaluation_pos
    (lt_min S.cover.retention_pos S.switch.radius_pos))) (by norm_num)

/-- The four-mesh transition ball fits inside each of the four control radii. -/
theorem four_mul_mesh_le (S : System g) :
    4 * S.mesh ≤ S.cover.step ∧ 4 * S.mesh ≤ S.cover.evaluation ∧
    4 * S.mesh ≤ S.cover.retention ∧ 4 * S.mesh ≤ S.switch.radius := by
  have hpos := mesh_pos S
  have hle : 4 * S.mesh ≤ min S.cover.step (min S.cover.evaluation
      (min S.cover.retention S.switch.radius)) := by
    dsimp only [System.mesh] at hpos ⊢
    linarith
  simpa only [le_min_iff] using hle

/-- H2 in the old patch and same-state switch control compare the next interpretation. -/
theorem transition_eqOn : ∀ (S : System g) (a b : S.cover.Label)
    (s : CartanChain.ChainState g) (z : M)
    (d : Data (S.cover.interp a) s z),
    S.cover.Valid a s → S.cover.Valid b d.successor →
    letI : MetricSpace M := g.toMetricSpace
    dist z s.anchor < 4 * S.mesh →
      ball z (4 * S.mesh) ⊆ (germ (S.cover.interp a) s).source ∩
        (germ (S.cover.interp b) d.successor).source ∧
      EqOn (map (S.cover.interp a) s) (map (S.cover.interp b) d.successor)
        (ball z (4 * S.mesh)) := by
  intro S a b s z d ha hb
  letI : MetricSpace M := g.toMetricSpace
  intro hz
  have hbounds := four_mul_mesh_le S
  have haB : S.cover.Buffered a s :=
    ⟨interior_subset (S.cover.source.core_subset a.1 ha.1),
      interior_subset (S.cover.target.core_subset a.2 ha.2)⟩
  have hbB : S.cover.Buffered b d.successor :=
    ⟨interior_subset (S.cover.source.core_subset b.1 hb.1),
      interior_subset (S.cover.target.core_subset b.2 hb.2)⟩
  obtain ⟨hx, hp⟩ := S.cover.retained a.1 a.2 s ha.1 ha.2 z
    (hz.trans_le hbounds.2.2.1)
  have haNext : S.cover.Buffered a d.successor :=
    ⟨interior_subset hx, interior_subset hp⟩
  obtain ⟨hsource, heq⟩ := S.cover.h2 a.1 a.2 s.anchor haB.1 s.target haB.2
    s.alignment z d (hz.trans_le hbounds.1)
  obtain ⟨hswitchSource, hswitchEq⟩ := S.switch.agreement a b d.successor haNext hbB
  have hEval : ball z (4 * S.mesh) ⊆ ball z S.cover.evaluation :=
    ball_subset_ball hbounds.2.1
  have hSwitch : ball z (4 * S.mesh) ⊆ ball d.successor.anchor S.switch.radius :=
    ball_subset_ball hbounds.2.2.2
  exact ⟨fun y hy => ⟨(hsource (hEval hy)).1, (hswitchSource (hSwitch hy)).2⟩,
    fun y hy => (heq (hEval hy)).trans (hswitchEq (hSwitch hy))⟩

/-- At fixed source and target anchors the generic comparison is uniform over
all tangent alignments. The operator bound controls the inverse-normal input. -/
theorem buffered_eventuallyEq_generic_forall_alignment
    (B : QuantitativeCover g) (a : B.Label) (x : M) (p : RoundSphere3)
    (hx : x ∈ B.source.buffer a.1) (hp : p ∈ B.target.buffer a.2) :
    ∀ᶠ z in 𝓝 x, ∀ L : CartanMap.TangentAlignment g x p,
      map (B.interp a) ⟨x, p, L⟩ z = (⟨x, p, L⟩ : CartanChain.ChainState g).map z := by
  let C := B.source.patch a.1
  let D := B.target.patch a.2
  have hxC : x ∈ C.anchors := B.source.buffer_subset a.1 hx
  have hpD : p ∈ D.anchors := B.target.buffer_subset a.2 hp
  have hsource := FixedChartUniformPreferredGermAgreement.normal_eventuallyEq_generic_in_anchor_frame
    C (B.source.cutoff a.1) x hxC
  have htarget := FixedChartUniformPreferredGermAgreement.normal_eventuallyEq_generic_in_anchor_frame
    D (B.target.cutoff a.2) p hpD
  have hJx : (patchFrame C x : E →L[ℝ] E) =
      FixedChartUniformPreferredGermAgreement.anchorFrame (B.source.center a.1) x := by
    unfold patchFrame
    rw [dif_pos hxC]
    exact Classical.choose_spec
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hxC)
  have hJp : (patchFrame D p : E →L[ℝ] E) =
      FixedChartUniformPreferredGermAgreement.anchorFrame (B.target.center a.2) p := by
    unfold patchFrame
    rw [dif_pos hpD]
    exact Classical.choose_spec
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible D p hpD)
  rw [← hJx] at hsource
  rw [← hJp] at htarget
  let N := (CartanSourceExponential.genericFamily roundSphereMetric3).normal p
  let J := patchFrame D p
  have hz : (0 : E) ∈ (D.normal p).target := by
    simpa only [D.normal_anchor p hpD] using
      (D.normal p).map_source (D.anchor_mem_normal_source p hpD)
  have hinvzero : (D.normal p).symm (0 : E) = p := by
    rw [← D.normal_anchor p hpD]
    exact (D.normal p).left_inv (D.anchor_mem_normal_source p hpD)
  have htN : Tendsto (D.normal p).symm (𝓝 (0 : E)) (𝓝 p) := by
    simpa only [hinvzero] using ((D.normal p).continuousAt_symm hz).tendsto
  have htJ : Tendsto J.symm (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using (J.symm.continuous.continuousAt (x := (0 : E))).tendsto
  have ht := htN.comp htJ
  have hinverse : ∀ᶠ v in 𝓝 (0 : E), (D.normal p).symm (J.symm v) = N.symm v := by
    filter_upwards [ht htarget,
      ht (N.open_source.mem_nhds
        ((CartanSourceExponential.genericFamily roundSphereMetric3).anchor_mem_source p)),
      htJ ((D.normal p).open_target.mem_nhds hz)] with v hv hvs hvt
    have heq : N ((D.normal p).symm (J.symm v)) = v := by
      calc
        N ((D.normal p).symm (J.symm v)) =
            J (D.normal p ((D.normal p).symm (J.symm v))) := hv.symm
        _ = v := by rw [(D.normal p).right_inv hvt, J.apply_symm_apply]
    exact ((N.left_inv hvs).symm.trans (congrArg N.symm heq))
  obtain ⟨δ, hδ, hδeq⟩ := Metric.mem_nhds_iff.mp hinverse
  obtain ⟨R, hR, hbound⟩ :=
    CartanMap.exists_pos_uniform_tangentAlignment_operatorNorm_bound g x p
  let Nsource := (CartanSourceExponential.genericFamily g).normal x
  have hnormal : Tendsto Nsource (𝓝 x) (𝓝 (0 : E)) := by
    simpa only [Nsource, CartanSourceExponential.Family.normal_anchor] using
      (Nsource.continuousAt
        ((CartanSourceExponential.genericFamily g).anchor_mem_source x)).tendsto
  have hsmall : ∀ᶠ z in 𝓝 x, ‖Nsource z‖ < δ / R := by
    simpa only [mem_ball, dist_zero_right] using
      hnormal.eventually (ball_mem_nhds (0 : E) (div_pos hδ hR))
  filter_upwards [hsource, hsmall] with z hzs hzn L
  have hinput : ‖L (Nsource z)‖ < δ := by
    calc
      _ ≤ ‖(L.toContinuousLinearEquiv : E →L[ℝ] E)‖ * ‖Nsource z‖ :=
        (L.toContinuousLinearEquiv : E →L[ℝ] E).le_opNorm _
      _ ≤ R * ‖Nsource z‖ := mul_le_mul_of_nonneg_right (hbound L) (norm_nonneg _)
      _ < δ := by simpa only [mul_comm R] using (lt_div_iff₀ hR).mp hzn
  have hi := hδeq (show L (Nsource z) ∈ ball (0 : E) δ by simpa using hinput)
  rw [← generic_map_eq (⟨x, p, L⟩ : CartanChain.ChainState g)]
  change (D.normal p).symm (J.symm (L (patchFrame C x (C.normal x z)))) =
    N.symm (L (Nsource z))
  change patchFrame C x (C.normal x z) = Nsource z at hzs
  rw [hzs]
  exact hi

/-- At fixed anchors one ball works for every label pair and every alignment.
Only the dependence on the two moving anchors remains in this local result. -/
theorem exists_fixed_anchor_switch_radius (B : QuantitativeCover g)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ρ > (0 : ℝ), ∀ (a b : B.Label) (L : CartanMap.TangentAlignment g x p),
      B.Buffered a ⟨x, p, L⟩ → B.Buffered b ⟨x, p, L⟩ →
      ball x ρ ⊆ (germ (B.interp a) ⟨x, p, L⟩).source ∩
        (germ (B.interp b) ⟨x, p, L⟩).source ∧
      EqOn (map (B.interp a) ⟨x, p, L⟩) (map (B.interp b) ⟨x, p, L⟩)
        (ball x ρ) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  letI : Fintype B.Label := inferInstanceAs
    (Fintype (Fin B.source.count × Fin B.target.count))
  have hpairs : ∀ c : B.Label × B.Label, ∃ r > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x p,
      B.Buffered c.1 ⟨x, p, L⟩ → B.Buffered c.2 ⟨x, p, L⟩ →
      ball x r ⊆ (germ (B.interp c.1) ⟨x, p, L⟩).source ∩
        (germ (B.interp c.2) ⟨x, p, L⟩).source ∧
      EqOn (map (B.interp c.1) ⟨x, p, L⟩) (map (B.interp c.2) ⟨x, p, L⟩)
        (ball x r) := by
    intro c
    by_cases ha : x ∈ B.source.buffer c.1.1 ∧ p ∈ B.target.buffer c.1.2
    · by_cases hb : x ∈ B.source.buffer c.2.1 ∧ p ∈ B.target.buffer c.2.2
      · have hevent : ∀ᶠ z in 𝓝 x, ∀ L : CartanMap.TangentAlignment g x p,
            map (B.interp c.1) ⟨x, p, L⟩ z = map (B.interp c.2) ⟨x, p, L⟩ z := by
          filter_upwards [buffered_eventuallyEq_generic_forall_alignment B c.1 x p ha.1 ha.2,
            buffered_eventuallyEq_generic_forall_alignment B c.2 x p hb.1 hb.2]
            with z hza hzb L
          exact (hza L).trans (hzb L).symm
        obtain ⟨r, hr, heq⟩ := Metric.mem_nhds_iff.mp hevent
        refine ⟨min r B.step, lt_min hr B.step_pos, ?_⟩
        intro L hLa hLb
        exact ⟨(ball_subset_ball (min_le_right _ _)).trans
            (buffered_common_source B c.1 c.2 ⟨x, p, L⟩ hLa hLb),
          fun z hz => heq (ball_subset_ball (min_le_left _ _) hz) L⟩
      · exact ⟨1, zero_lt_one, fun _ _ h => (hb h).elim⟩
    · exact ⟨1, zero_lt_one, fun _ h => (ha h).elim⟩
  choose r hr hagree using hpairs
  obtain ⟨ρ, hρ, hle⟩ := exists_positive_lower_bound r hr
  refine ⟨ρ, hρ, ?_⟩
  intro a b L ha hb
  obtain ⟨hs, he⟩ := hagree (a, b) L ha hb
  exact ⟨(ball_subset_ball (hle (a, b))).trans hs,
    he.mono (ball_subset_ball (hle (a, b)))⟩

/-- The remaining geometric comparison on compact buffer intersections.
Each pair's radius must precede both moving anchors and every alignment.
Common source containment is supplied independently by H1. -/
def UniformBufferedPairAgreement (B : QuantitativeCover g) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ a b : B.Label, ∃ ρ > (0 : ℝ),
    ∀ x ∈ B.source.buffer a.1 ∩ B.source.buffer b.1,
    ∀ p ∈ B.target.buffer a.2 ∩ B.target.buffer b.2,
    ∀ L : CartanMap.TangentAlignment g x p,
      EqOn (map (B.interp a) ⟨x, p, L⟩) (map (B.interp b) ⟨x, p, L⟩) (ball x ρ)

/-- Finite pairwise comparison radii and H1's source radius give the exact
switch contract. This theorem does not produce the uniform comparison premise. -/
theorem exists_switchControl_of_uniformBufferedPairAgreement
    (B : QuantitativeCover g) (h : UniformBufferedPairAgreement B) :
    Nonempty (SwitchControl B) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  letI : Fintype B.Label := inferInstanceAs
    (Fintype (Fin B.source.count × Fin B.target.count))
  have hpairs := fun c : B.Label × B.Label => h c.1 c.2
  choose r hr hagree using hpairs
  obtain ⟨δ, hδ, hle⟩ := exists_positive_lower_bound r hr
  refine ⟨{
    radius := min B.step δ
    radius_pos := lt_min B.step_pos hδ
    agreement := ?_ }⟩
  intro a b s ha hb
  exact ⟨(ball_subset_ball (min_le_left _ _)).trans
      (buffered_common_source B a b s ha hb),
    (hagree (a, b) s.anchor ⟨ha.1, hb.1⟩ s.target ⟨ha.2, hb.2⟩ s.alignment).mono
      (ball_subset_ball ((min_le_right _ _).trans (hle (a, b))))⟩

end CartanSuppliedUniformPatchSwitch
end Poincare
