import Poincare.Global.FixedChartLocalSuccessorEquality
import Poincare.Global.FixedChartMovingPositionJacobi
import Poincare.Global.LCNaturality

/-!
# Differential and geodesic interfaces for uniform endpoint reanchoring

All manifold radii precede the moving anchors, alignments, and data.
-/

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
namespace FixedChartUniformEndpointReanchoring
open CartanSuppliedDifferentialSuccessor

private theorem chartMap_apply_host (Q : Interpretation g)
    (s : CartanChain.ChainState g) (y : M)
    (hy : y ∈ (extChartAt I (Q.sourceHost s.anchor)).source) :
    chartMap Q s (extChartAt I (Q.sourceHost s.anchor) y) =
      extChartAt I (Q.targetHost s.target) (map Q s y) := by
  change (chartAt E (Q.targetHost s.target))
    ((Q.targetNormal s.target).symm (linear Q s
      (Q.sourceNormal s.anchor ((chartAt E (Q.sourceHost s.anchor)).symm
        ((chartAt E (Q.sourceHost s.anchor)) y))))) = _
  rw [(chartAt E (Q.sourceHost s.anchor)).left_inv
    (by simpa only [extChartAt_source] using hy)]
  rfl

/-- The actual derivative of the supplied host map is invertible and pulls
back the target metric. No choice of derivative witnesses remains. -/
theorem chartMap_fderiv_metric (Q : Interpretation g)
    (s : CartanChain.ChainState g) (z : M) (d : CoordinateData Q s z) :
    let q := extChartAt I (Q.sourceHost s.anchor) z
    let F := chartMap Q s
    HasStrictFDerivAt F (fderiv ℝ F q) q ∧
    (fderiv ℝ F q).IsInvertible ∧
    q ∈ (extChartAt I (Q.sourceHost s.anchor)).target ∧
    F q ∈ (extChartAt I (Q.targetHost s.target)).target ∧
    ∀ a b : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner (Q.targetHost s.target)
        (F q) (fderiv ℝ F q a) (fderiv ℝ F q b) =
      CovariantDerivative.chartMetric g.inner (Q.sourceHost s.anchor) q a b := by
  dsimp only
  have hd := d.cartan_chart_derivative
  rw [← d.source_coordinate] at hd
  have hf := hd.hasFDerivAt.fderiv
  refine ⟨by simpa only [hf] using hd, ?_,
    (extChartAt I (Q.sourceHost s.anchor)).map_source d.source_mem_oldChart, ?_, ?_⟩
  · rw [hf]
    exact ⟨(d.A.symm.trans (linear Q s)).trans d.B, rfl⟩
  · rw [chartMap_apply_host Q s z d.source_mem_oldChart]
    exact (extChartAt I (Q.targetHost s.target)).map_source d.target_mem_oldChart
  · intro a b
    rw [hf, chartMap_apply_host Q s z d.source_mem_oldChart,
      d.target_coordinate, d.source_coordinate]
    exact d.metric_pullback a b

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Curvature supplies a metric-pullback germ in the fixed host coordinates
at every point of a single uniform manifold neighborhood. -/
theorem exists_uniform_chartMetric_pullback_germ
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
      let F := chartMap (patch C D) ⟨x, p, L⟩
      ∀ᶠ q in 𝓝 (extChartAt I x₀ z),
        HasStrictFDerivAt F (fderiv ℝ F q) q ∧
        (fderiv ℝ F q).IsInvertible ∧
        q ∈ (extChartAt I x₀).target ∧ F q ∈ (extChartAt I p₀).target ∧
        ∀ a b : E,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (F q) (fderiv ℝ F q a) (fderiv ℝ F q b) =
          CovariantDerivative.chartMetric g.inner x₀ q a b := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨η, hη, hdata⟩ := FixedChartMovingPositionJacobi.exists_radius g
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  refine ⟨η, hη, ?_⟩
  intro x hx p hp L z hz
  dsimp only
  have hzsrc : z ∈ (extChartAt I x₀).source := (hdata x hx p hp L z hz).1.1
  have hzt := (extChartAt I x₀).map_source hzsrc
  have he : ∀ᶠ q in 𝓝 (extChartAt I x₀ z),
      (extChartAt I x₀).symm q ∈ ball x η := by
    apply (continuousAt_extChartAt_symm'' hzt).tendsto
    rw [(extChartAt I x₀).left_inv hzsrc]
    exact isOpen_ball.mem_nhds hz
  filter_upwards [he, (isOpen_extChartAt_target x₀).mem_nhds hzt] with q hq hqt
  obtain ⟨d⟩ := (hdata x hx p hp L ((extChartAt I x₀).symm q) hq).2.2.2
  have hd := chartMap_fderiv_metric (patch C D) ⟨x, p, L⟩
    ((extChartAt I x₀).symm q) d.toCoordinateData
  dsimp only [patch] at hd
  rw [(extChartAt I x₀).right_inv hqt] at hd
  exact hd

omit [CompactSpace M] [ConnectedSpace M] in
/-- A differentiable derivative at the point suffices for the signed
Christoffel law. Symmetry follows from the nearby first derivatives. -/
theorem christoffel_transition_of_metric_germ
    (x₀ : M) (p₀ : RoundSphere3) (F : E → E) (q : E)
    (hgerm : ∀ᶠ w in 𝓝 q,
      HasStrictFDerivAt F (fderiv ℝ F w) w ∧
      (fderiv ℝ F w).IsInvertible ∧
      w ∈ (extChartAt I x₀).target ∧ F w ∈ (extChartAt I p₀).target ∧
      ∀ a b : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          (F w) (fderiv ℝ F w a) (fderiv ℝ F w b) =
        CovariantDerivative.chartMetric g.inner x₀ w a b)
    (hD : DifferentiableAt ℝ (fderiv ℝ F) q)
    (hcut₀ : ∀ᶠ w in 𝓝 q, GeodesicTransport.cutoff (n := 3) x₀ w = 1)
    (hcut₁ : ∀ᶠ w in 𝓝 (F q), GeodesicTransport.cutoff (n := 3) p₀ w = 1)
    (v : E) :
    GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀ (F q)
        (fderiv ℝ F q v) (fderiv ℝ F q v) =
      fderiv ℝ F q (GeodesicTransport.chartChristoffelField g x₀ q v v) -
        fderiv ℝ (fderiv ℝ F) q v v := by
  obtain ⟨hF, hinv, hq, hFq, hpull⟩ := hgerm.self_of_nhds
  let G₀ := CovariantDerivative.chartMetric g.inner x₀
  let G₁ := CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
  have hnear : ∀ᶠ w in 𝓝 q, HasFDerivAt F (fderiv ℝ F w) w :=
    hgerm.mono (fun _ hw => hw.1.hasFDerivAt)
  have hsymm := second_derivative_symmetric_of_eventually hnear hD.hasFDerivAt
  have hp : ∀ a b : E,
      (fun w => G₁ (F w) (fderiv ℝ F w a) (fderiv ℝ F w b)) =ᶠ[𝓝 q]
      (fun w => G₀ w a b) := fun a b => hgerm.mono (fun _ hw => hw.2.2.2.2 a b)
  have hdiff := GeodesicTransport.differentiated_pullback_hdiff_of_eventuallyEq
    G₀ G₁ F (fderiv ℝ F) hF.hasFDerivAt hD.hasFDerivAt
    (UniformAnchoredFTransition.chartMetric_hasFDerivAt_of_mem_target g x₀ hq)
    (UniformAnchoredFTransition.chartMetric_hasFDerivAt_of_mem_target
      roundSphereMetric3 p₀ hFq) hp
  let b₀ := UniformAnchoredFTransition.chartMetricBilin (G₀ q)
  let b₁ := UniformAnchoredFTransition.chartMetricBilin (G₁ (F q))
  have hb₀ : b₀.Nondegenerate :=
    UniformAnchoredFTransition.chartMetricBilin_nondegenerate_of_mem_target g x₀ hq
  have hb₁ : b₁.Nondegenerate :=
    UniformAnchoredFTransition.chartMetricBilin_nondegenerate_of_mem_target
      roundSphereMetric3 p₀ hFq
  have hraw := GeodesicTransport.christoffelAt_map_eq_signed_transport_of_differentiated_pullback
    G₀ G₁ F (fderiv ℝ F) hinv hsymm hdiff hpull
    (CovariantDerivative.chartMetric_symm roundSphereMetric3.inner
      (fun z a b => roundSphereMetric3.symm z a b) p₀ (F q))
    b₀ b₁ hb₀ hb₁ (fun _ _ => rfl) (fun _ _ => rfl) v v
  exact FTransitionGeodesicMap.chartChristoffelField_self_F_transition_of_christoffelAt
    g x₀ p₀ F (fderiv ℝ F q) rfl hcut₀ hcut₁ b₀ b₁ hb₀ hb₁
    (fun _ _ => rfl) (fun _ _ => rfl) v hraw

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem anchor_cutoff {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {x : M} (hx : x ∈ C.anchors) :
    ∀ᶠ w in 𝓝 (extChartAt I x₀ x), GeodesicTransport.cutoff (n := 3) x₀ w = 1 := by
  have hq : (extChartAt I x₀ x, (0 : E)) ∈
      closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ) := by
    exact ball_subset_closedBall (by simpa using C.A_subset hx.2)
  have h := (FixedChartMovingPositionJacobi.flow_mem_target_cutoffOne C hU hq
    (show (0 : ℝ) ∈ Icc (-C.T) C.T by constructor <;> linarith [C.T_pos])).2
  rw [(C.flow_law _ hq).1] at h
  exact h

/-- On one uniform neighborhood, the only extra regularity needed for the
supplied map's Christoffel law is differentiability of its derivative. -/
theorem exists_uniform_christoffel_transition_of_differentiable_fderiv
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
      let F := chartMap (patch C D) ⟨x, p, L⟩
      let q := extChartAt I x₀ z
      DifferentiableAt ℝ (fderiv ℝ F) q → ∀ v : E,
        GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀ (F q)
            (fderiv ℝ F q v) (fderiv ℝ F q v) =
          fderiv ℝ F q (GeodesicTransport.chartChristoffelField g x₀ q v v) -
            fderiv ℝ (fderiv ℝ F) q v v := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨ηg, hηg, hgerm⟩ := exists_uniform_chartMetric_pullback_germ
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  obtain ⟨ηd, hηd, hdata⟩ := FixedChartMovingPositionJacobi.exists_radius g
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  refine ⟨min ηg ηd, lt_min hηg hηd, ?_⟩
  intro x hx p hp L z hz
  dsimp only
  intro hD v
  obtain ⟨hzC, hpD, _⟩ := hdata x hx p hp L z (hz.trans_le (min_le_right _ _))
  apply christoffel_transition_of_metric_germ x₀ p₀ _ _
    (hgerm x hx p hp L z (hz.trans_le (min_le_left _ _))) hD (anchor_cutoff C hU hzC) _ v
  have heq : chartMap (patch C D) ⟨x, p, L⟩ (extChartAt I x₀ z) =
      extChartAt I p₀ (map (patch C D) ⟨x, p, L⟩ z) :=
    chartMap_apply_host (patch C D) ⟨x, p, L⟩ z hzC.1
  rw [heq]
  exact anchor_cutoff D hV hpD

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Rescaling both time and velocity gives the same geodesic equation on
`[0,1]`, even when source and target patches have different retained times. -/
theorem normalizedFlow_hasDerivWithinAt {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let γ := fun s : ℝ => ((C.α q (C.T * s)).1, C.T • (C.α q (C.T * s)).2)
    HasDerivWithinAt γ
      (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) (γ t))
      (Icc (0 : ℝ) 1) t := by
  have htimes : MapsTo (fun s : ℝ => C.T * s) (Icc (0 : ℝ) 1) (Icc (-C.T) C.T) := by
    intro s hs
    constructor <;> nlinarith [C.T_pos, hs.1, hs.2]
  have hscale : HasDerivWithinAt (fun s : ℝ => C.T * s) C.T (Icc (0 : ℝ) 1) t := by
    simpa using ((hasDerivAt_id t).const_mul C.T).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  have hd := ((C.flow_law q hq).2 (C.T * t) (htimes ht)).scomp t hscale htimes
  have hp := HasFDerivWithinAt.hasDerivWithinAt (HasFDerivWithinAt.fst hd.hasFDerivWithinAt)
  have hv := HasFDerivWithinAt.hasDerivWithinAt (HasFDerivWithinAt.snd hd.hasFDerivWithinAt)
  have hpair := hp.prodMk (hv.const_smul C.T)
  simpa [geodesicFlowField, smul_smul] using hpair

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Smooth chart geodesic fields have uniqueness on the entire unit interval.
The Lipschitz bound is taken on a compact ball containing both trajectories. -/
theorem geodesic_eqOn_unitInterval
    (p₀ : RoundSphere3) {β γ : ℝ → E × E}
    (hβ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt β
      (geodesicFlowField (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) (β t))
      (Icc (0 : ℝ) 1) t)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ
      (geodesicFlowField (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) (γ t))
      (Icc (0 : ℝ) 1) t)
    (h0 : β 0 = γ 0) : EqOn β γ (Icc (0 : ℝ) 1) := by
  have hcβ := HasDerivWithinAt.continuousOn hβ
  have hcγ := HasDerivWithinAt.continuousOn hγ
  have hcompact := (isCompact_Icc.image_of_continuousOn hcβ).union
    (isCompact_Icc.image_of_continuousOn hcγ)
  obtain ⟨a, ha⟩ := hcompact.isBounded.subset_closedBall (0 : E × E)
  have hF := GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff_two
    roundSphereMetric3 p₀
  obtain ⟨B, hB⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E × E) a) (isCompact_closedBall (0 : E × E) a)
  apply ODE_solution_unique_of_mem_Icc_right (fun _ _ => hB) hcβ _ _ hcγ _ _ h0
  · intro t ht
    exact (hβ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact ha (Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
  · intro t ht
    exact (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact ha (Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩)

/-- A single velocity radius bounds endpoint displacement at every compact
anchor. The displacement tolerance is prescribed before choosing the radius. -/
theorem exists_uniform_endpoint_displacement_radius {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    {ε : ℝ} (hε : 0 < ε) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ v : E, ‖v‖ < ρ →
      dist (C.endpoint x v) x < ε := by
  letI : MetricSpace M := g.toMetricSpace
  have he : ∀ᶠ v : E in 𝓝 0, ∀ x ∈ K, dist (C.endpoint x v) x < ε := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hxC := hKC hx
    let f : E × M → E × E := fun q => (extChartAt I x₀ q.2, C.T⁻¹ • q.1)
    have hf : ContinuousAt f (0, x) :=
      ((continuousAt_extChartAt' hxC.1).comp continuousAt_snd).prodMk
        (continuousAt_const.smul continuousAt_fst)
    have hf0 : f (0, x) = (extChartAt I x₀ x, 0) := by simp [f]
    have hsrc : f (0, x) ∈ C.P.source := by
      rw [hf0]
      exact C.zero_mem_source _ hxC.2
    have hp : ContinuousAt (fun q => (C.P (f q)).2) (0, x) :=
      ((C.P.continuousAt hsrc).comp hf).snd
    have hp0 : (C.P (f (0, x))).2 = extChartAt I x₀ x := by
      rw [hf0, C.stationary _ hxC.2]
    have htarget : (C.P (f (0, x))).2 ∈ (chartAt E x₀).target := by
      rw [hp0]
      exact (chartAt E x₀).map_source (by simpa only [extChartAt_source] using hxC.1)
    have hc : ContinuousAt (fun q : E × M => C.endpoint q.2 q.1) (0, x) :=
      ((chartAt E x₀).continuousAt_symm htarget).comp (f := fun q => (C.P (f q)).2) hp
    apply (hc.dist continuousAt_snd).eventually (gt_mem_nhds _)
    simpa only [C.endpoint_zero x hxC, dist_self] using hε
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨ρ, hρ, fun x hx v hv => hball (by simpa using hv) x hx⟩

/-- The remaining analytic requirement: the actual derivative-mapped,
time-normalized source trajectory solves the target geodesic equation with
the actual successor velocity. Both radii precede every moving parameter. -/
def UniformMappedGeodesicEquation
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
      (d : Data (patch C D) ⟨x, p, L⟩ z), dist z x < η →
      ∀ v : E, ‖v‖ < ρ → v ∈ (C.endpoint z).source →
        let F := chartMap (patch C D) ⟨x, p, L⟩
        let q := (extChartAt I x₀ z, C.T⁻¹ • v)
        let γ := fun t : ℝ => ((C.α q (C.T * t)).1, C.T • (C.α q (C.T * t)).2)
        let β := FTransitionGeodesicMap.mappedState F γ
        β 0 = (extChartAt I p₀ (map (patch C D) ⟨x, p, L⟩ z),
          linear (patch C D) d.successor v) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt β
          (geodesicFlowField (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) (β t))
          (Icc (0 : ℝ) 1) t

/-- Full-interval uniqueness and common-source control turn the remaining
mapped geodesic equation into the frozen endpoint identity. -/
theorem target_of_uniformMappedGeodesicEquation
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors)
    (he : UniformMappedGeodesicEquation C D K H) :
    FixedChartLocalSuccessorEquality.UniformEndpointReanchoring (patch C D) K H := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨ηe, hηe, ρe, hρe, heq⟩ := he
  obtain ⟨ηc, hηc, εc, hεc, hcommon⟩ :=
    FixedChartLocalSuccessorEquality.exists_uniform_common_source_radii C D K H hK hKC hH hHD
  obtain ⟨K', hK', hKK', hK'C⟩ := exists_compact_between hK C.isOpen_anchors hKC
  obtain ⟨δ, hδ, hδK'⟩ := hK.exists_cthickening_subset_open isOpen_interior hKK'
  obtain ⟨ρd, hρd, hdisplace⟩ := exists_uniform_endpoint_displacement_radius C K' hK' hK'C hεc
  refine ⟨min ηe (min ηc δ), lt_min hηe (lt_min hηc hδ),
    min ρe ρd, lt_min hρe hρd, ?_⟩
  intro x hx p hp L z d hz v hv hvsrc
  have hze := hz.trans_le (min_le_left _ _)
  have hzc := (hz.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hzδ := (hz.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hzK' : z ∈ K' := interior_subset
    (hδK' (mem_cthickening_of_dist_le z x δ K hx hzδ.le))
  let Q := patch C D
  let s : CartanChain.ChainState g := ⟨x, p, L⟩
  let y := C.endpoint z v
  have hvsrc' : v ∈ (C.endpoint z).source := hvsrc
  have hyz : dist y z < εc := hdisplace z hzK' v (hv.trans_le (min_le_right _ _))
  obtain ⟨hyold, hynew⟩ := hcommon x hx p hp L z d hzc hyz
  have hinv : C.normal z y = v := (C.endpoint z).left_inv hvsrc'
  have hvt : linear Q d.successor v ∈ (D.endpoint (map Q s z)).source := by
    have h := hynew.2.2
    change linear Q d.successor (C.normal z y) ∈ (D.endpoint (map Q s z)).source at h
    rw [hinv] at h
    exact h
  let qt := (extChartAt I p₀ (map Q s z), D.T⁻¹ • linear Q d.successor v)
  let γt := fun t : ℝ => ((D.α qt (D.T * t)).1, D.T • (D.α qt (D.T * t)).2)
  have hqt := D.endpoint_source_initial_mem hvt
  have hγt : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γt
      (geodesicFlowField (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) (γt t))
      (Icc (0 : ℝ) 1) t := fun _ ht => normalizedFlow_hasDerivWithinAt D hqt ht
  have hγ0 : γt 0 = (extChartAt I p₀ (map Q s z), linear Q d.successor v) := by
    dsimp only [γt]
    rw [mul_zero, (D.flow_law qt hqt).1]
    simp [qt, smul_smul, D.T_pos.ne']
  obtain ⟨hβ0, hβ⟩ := heq x hx p hp L z d hze v (hv.trans_le (min_le_left _ _)) hvsrc'
  have hstates := geodesic_eqOn_unitInterval p₀ hβ hγt (hβ0.trans hγ0.symm)
  have hend := congrArg Prod.fst (hstates (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp))
  simp only [FTransitionGeodesicMap.mappedState, γt, mul_one] at hend
  change chartMap Q s (FixedChartUniformDifferentialPullback.normalizedEndpoint C
      (extChartAt I x₀ z, v)) =
    FixedChartUniformDifferentialPullback.normalizedEndpoint D
      (extChartAt I p₀ (map Q s z), linear Q d.successor v) at hend
  have hysrc : y ∈ (extChartAt I x₀).source := by
    have h := (C.endpoint z).map_source hvsrc'
    change y ∈ (C.normal z).source at h
    rw [C.normal_source] at h
    exact h.1
  have hmpsrc : map Q s y ∈ (extChartAt I p₀).source := by
    have h := (D.endpoint p).map_source hyold.2.2
    change map Q s y ∈ (D.normal p).source at h
    rw [D.normal_source] at h
    exact h.1
  have htesrc : D.endpoint (map Q s z) (linear Q d.successor v) ∈
      (extChartAt I p₀).source := by
    have h := (D.endpoint (map Q s z)).map_source hvt
    change D.endpoint (map Q s z) (linear Q d.successor v) ∈ (D.normal (map Q s z)).source at h
    rw [D.normal_source] at h
    exact h.1
  have hcs : extChartAt I x₀ y =
      FixedChartUniformDifferentialPullback.normalizedEndpoint C (extChartAt I x₀ z, v) :=
    FixedChartUniformDifferentialPullback.coordinateEndpoint_eq_normalizedEndpoint C z v hvsrc'
  have hct : extChartAt I p₀ (D.endpoint (map Q s z) (linear Q d.successor v)) =
      FixedChartUniformDifferentialPullback.normalizedEndpoint D
        (extChartAt I p₀ (map Q s z), linear Q d.successor v) :=
    FixedChartUniformDifferentialPullback.coordinateEndpoint_eq_normalizedEndpoint
      D (map Q s z) (linear Q d.successor v) hvt
  have hm : chartMap Q s (extChartAt I x₀ y) = extChartAt I p₀ (map Q s y) :=
    chartMap_apply_host Q s y hysrc
  rw [← hcs, hm, ← hct] at hend
  exact (extChartAt I p₀).injOn hmpsrc htesrc hend

end FixedChartUniformEndpointReanchoring
end Poincare
