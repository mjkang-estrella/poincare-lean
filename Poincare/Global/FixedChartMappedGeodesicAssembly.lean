import Poincare.Global.FixedChartAugmentedSystemRegularity
import Poincare.Global.FixedChartUniformEndpointReanchoring

/-!
# Regularity and geodesic assembly for the supplied fixed-chart map

The retained endpoint time and the order of all uniform radii are preserved.
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
namespace FixedChartMappedGeodesicAssembly
open CartanSuppliedDifferentialSuccessor FixedChartUniformEndpointReanchoring

/-- The actual coordinate endpoint is C2 at every point of its retained source. -/
theorem coordinateEndpoint_contDiffAt_two {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (v : E) (hv : v ∈ (C.endpoint x).source) :
    ContDiffAt ℝ 2 ((C.endpoint x).trans (chartAt E x₀)) v := by
  have hq : (extChartAt I x₀ x, C.T⁻¹ • v) ∈
      ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) := C.P_source_subset hv.1.2
  have h := ((FixedChartAugmentedSystemRegularity.patch_endpoint_contDiffOn_two C).contDiffAt (isOpen_ball.mem_nhds hq)).fst
  have hi : ContDiffAt ℝ 2 (fun w : E => (extChartAt I x₀ x, C.T⁻¹ • w)) v :=
    contDiffAt_const.prodMk ((contDiffAt_const (c := C.T⁻¹)).smul contDiffAt_id)
  apply (h.comp v hi).congr_of_eventuallyEq
  filter_upwards [(C.endpoint x).open_source.mem_nhds hv] with w hw
  exact FixedChartUniformDifferentialPullback.coordinateEndpoint_eq_normalizedEndpoint C x w hw

/-- Stored endpoint derivatives give C2 regularity of the exact supplied map. -/
theorem chartMap_contDiffAt_two_of_coordinateData
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (s : CartanChain.ChainState g) (z : M)
    (d : CoordinateData (patch C D) s z) :
    ContDiffAt ℝ 2 (chartMap (patch C D) s) (extChartAt I x₀ z) := by
  let Q := patch C D
  have hs : ContDiffAt ℝ 2 (sourceExp Q s.anchor) d.v :=
    coordinateEndpoint_contDiffAt_two C s.anchor d.v d.source_vector_mem.1
  have ht : ContDiffAt ℝ 2 (targetExp Q s.target) (linear Q s d.v) :=
    coordinateEndpoint_contDiffAt_two D s.target _ d.target_vector_mem.1
  have hinv := (sourceExp Q s.anchor).contDiffAt_symm
    ((sourceExp Q s.anchor).map_source d.source_vector_mem)
    (show HasFDerivAt (sourceExp Q s.anchor) (d.A : E →L[ℝ] E)
      ((sourceExp Q s.anchor).symm (sourceExp Q s.anchor d.v)) by
      rw [(sourceExp Q s.anchor).left_inv d.source_vector_mem]
      exact d.source_exp_derivative.hasFDerivAt)
    (show ContDiffAt ℝ 2 (sourceExp Q s.anchor)
      ((sourceExp Q s.anchor).symm (sourceExp Q s.anchor d.v)) by
      rw [(sourceExp Q s.anchor).left_inv d.source_vector_mem]
      exact hs)
  change ContDiffAt ℝ 2 (chartMap (patch C D) s)
    (extChartAt I ((patch C D).sourceHost s.anchor) z)
  rw [d.source_coordinate]
  have ht' : ContDiffAt ℝ 2 (targetExp Q s.target)
      (linear Q s ((sourceExp Q s.anchor).symm (sourceExp Q s.anchor d.v))) := by
    rw [(sourceExp Q s.anchor).left_inv d.source_vector_mem]
    exact ht
  have hl : ContDiffAt ℝ 2 (fun q => linear Q s ((sourceExp Q s.anchor).symm q))
      (sourceExp Q s.anchor d.v) :=
    (linear Q s).contDiff.contDiffAt.comp _ hinv
  exact ht'.comp (sourceExp Q s.anchor d.v)
    (f := fun q => linear Q s ((sourceExp Q s.anchor).symm q)) hl

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

private theorem patchFrame_hasFDerivAt {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) (x : M) (hx : x ∈ C.anchors) :
    HasFDerivAt (GeodesicTransport.chartTransition x₀ x)
      (patchFrame C x : E →L[ℝ] E) (extChartAt I x₀ x) := by
  have ht := (extChartAt I x₀).map_source hx.1
  have hs : (extChartAt I x₀).symm (extChartAt I x₀ x) ∈ (extChartAt I x).source := by
    rw [(extChartAt I x₀).left_inv hx.1]
    exact mem_extChartAt_source x
  have he : (patchFrame C x : E →L[ℝ] E) =
      FixedChartUniformPreferredGermAgreement.anchorFrame x₀ x := by
    unfold patchFrame
    rw [dif_pos hx]
    exact Classical.choose_spec
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hx)
  rw [he, FixedChartUniformPreferredGermAgreement.anchorFrame,
    GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv x₀ x ht hs]
  exact GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv x₀ x ht hs

/-- Every actual datum identifies the host derivative with its successor velocity map. -/
theorem chartMap_fderiv_eq_successor_linear
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (s : CartanChain.ChainState g) (z : M) (d : Data (patch C D) s z)
    (hz : z ∈ C.anchors) (hp : map (patch C D) s z ∈ D.anchors) :
    fderiv ℝ (chartMap (patch C D) s) (extChartAt I x₀ z) =
      (linear (patch C D) d.successor : E →L[ℝ] E) := by
  let Q := patch C D
  let F := chartMap Q s
  let p := map Q s z
  let q := extChartAt I x₀ z
  have hFq : F q = extChartAt I p₀ p := chartMap_apply_host Q s z hz.1
  have hSq : GeodesicTransport.chartTransition x₀ z q = extChartAt I z z := by
    change extChartAt I z ((extChartAt I x₀).symm (extChartAt I x₀ z)) = _
    rw [(extChartAt I x₀).left_inv hz.1]
  have hF : HasFDerivAt F (fderiv ℝ F q) q := by
    exact (chartMap_contDiffAt_two_of_coordinateData C D s z d.toCoordinateData).differentiableAt (by norm_num) |>.hasFDerivAt
  have hleft := (patchFrame_hasFDerivAt D p hp)
  rw [← hFq] at hleft
  have hl := hleft.comp q hF
  have hright := d.hasFDerivAt_reanchoredChartMap
  rw [← hSq] at hright
  have hr := hright.comp q (patchFrame_hasFDerivAt C z hz)
  have hqt := (extChartAt I x₀).map_source hz.1
  have hi : Tendsto (extChartAt I x₀).symm (𝓝 q) (𝓝 z) := by
    have h := (continuousAt_extChartAt_symm'' hqt).tendsto
    rwa [(extChartAt I x₀).left_inv hz.1] at h
  have hm := ((germ Q s).continuousAt d.source_mem).tendsto
  have he : (GeodesicTransport.chartTransition p₀ p ∘ F) =ᶠ[𝓝 q]
      (reanchoredChartMap Q s z ∘ GeodesicTransport.chartTransition x₀ z) := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hqt,
      hi ((show IsOpen (extChartAt I z).source from isOpen_extChartAt_source z).mem_nhds (mem_extChartAt_source z)),
      hi (hm ((isOpen_extChartAt_source p₀).mem_nhds hp.1))] with w hw hzw hpw
    change extChartAt I p ((extChartAt I p₀).symm (F w)) =
      extChartAt I p (map Q s ((extChartAt I z).symm
        (extChartAt I z ((extChartAt I x₀).symm w))))
    rw [(extChartAt I z).left_inv hzw]
    have hfw : F w = extChartAt I p₀ (map Q s ((extChartAt I x₀).symm w)) := by
      have h := chartMap_apply_host Q s ((extChartAt I x₀).symm w)
        ((extChartAt I x₀).map_target hw)
      change F (extChartAt I x₀ ((extChartAt I x₀).symm w)) = _ at h
      simpa only [(extChartAt I x₀).right_inv hw] using h
    change map Q s ((extChartAt I x₀).symm w) ∈ (extChartAt I p₀).source at hpw
    rw [hfw, (extChartAt I p₀).left_inv hpw]
  have hd := (hl.congr_of_eventuallyEq he.symm).unique hr
  apply ContinuousLinearMap.ext
  intro v
  apply (patchFrame D p).injective
  have hdv := congrArg (fun A : E →L[ℝ] E => A v) hd
  change patchFrame D p (fderiv ℝ F q v) =
    patchFrame D p ((patchFrame D p).symm (d.alignment (patchFrame C z v)))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hdv

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- H1 chooses the C2 neighborhood before all moving anchors and alignments. -/
theorem exists_uniform_chartMap_contDiffAt_two
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
        ContDiffAt ℝ 2 (chartMap (patch C D) ⟨x, p, L⟩) (extChartAt I x₀ z) := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨η, hη, hdata⟩ := FixedChartMovingPositionJacobi.exists_radius g
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  refine ⟨η, hη, ?_⟩
  intro x hx p hp L z hz
  obtain ⟨d⟩ := (hdata x hx p hp L z hz).2.2.2
  exact chartMap_contDiffAt_two_of_coordinateData C D ⟨x, p, L⟩ z d.toCoordinateData

/-- Curvature now gives the uniform transition law without a regularity premise. -/
theorem exists_uniform_christoffel_transition
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
      ContDiffAt ℝ 2 F q ∧ ∀ v : E,
        GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀ (F q)
            (fderiv ℝ F q v) (fderiv ℝ F q v) =
          fderiv ℝ F q (GeodesicTransport.chartChristoffelField g x₀ q v v) -
            fderiv ℝ (fderiv ℝ F) q v v := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨ηc, hηc, hc⟩ := exists_uniform_chartMap_contDiffAt_two
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  obtain ⟨ηt, hηt, ht⟩ := exists_uniform_christoffel_transition_of_differentiable_fderiv
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  refine ⟨min ηc ηt, lt_min hηc hηt, ?_⟩
  intro x hx p hp L z hz
  have hC2 := hc x hx p hp L z (hz.trans_le (min_le_left _ _))
  exact ⟨hC2, ht x hx p hp L z (hz.trans_le (min_le_right _ _))
    ((hC2.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
      (by norm_num))⟩

/-- Small normalized velocities keep the entire retained trajectory uniformly
close to each anchor in a compact set, with its actual chart domain. -/
theorem exists_uniform_flow_displacement_radius {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    {ε : ℝ} (hε : 0 < ε) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ v : E, ‖v‖ < ρ →
      (extChartAt I x₀ x, C.T⁻¹ • v) ∈
        closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ) ∧
      ∀ t ∈ Icc (-C.T) C.T,
        (C.α (extChartAt I x₀ x, C.T⁻¹ • v) t).1 ∈ (extChartAt I x₀).target ∧
        dist ((extChartAt I x₀).symm
          (C.α (extChartAt I x₀ x, C.T⁻¹ • v) t).1) x < ε := by
  letI : MetricSpace M := g.toMetricSpace
  let J := Icc (-C.T) C.T
  let f : E × (M × J) → E × E := fun a => (extChartAt I x₀ a.2.1, C.T⁻¹ • a.1)
  let S : Set (E × (M × J)) := {a | a.2.1 ∈ (extChartAt I x₀).source ∧ f a ∈ C.P.source}
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hf : ContinuousAt f a :=
      ((continuousAt_extChartAt' ha.1).comp
        (f := fun b : E × (M × J) => b.2.1) continuousAt_snd.fst).prodMk
        (continuousAt_const.smul continuousAt_fst)
    exact inter_mem
      ((continuous_snd.fst.isOpen_preimage _ (isOpen_extChartAt_source x₀)).mem_nhds ha.1)
      (hf (C.P.open_source.mem_nhds ha.2))
  have hc : ContinuousOn (fun a : E × (M × J) => (C.α (f a) a.2.2).1) S := by
    apply C.continuous_flow.fst.comp
      (f := fun a : E × (M × J) => (f a, (a.2.2 : ℝ))) (s := S) _
      (fun a ha => ⟨ball_subset_closedBall (C.P_source_subset ha.2), a.2.2.property⟩)
    apply ContinuousOn.prodMk
    · apply ContinuousOn.prodMk
      · exact (continuousOn_extChartAt x₀).comp continuous_snd.fst.continuousOn
          (fun a ha => ha.1)
      · exact (continuous_const.smul continuous_fst).continuousOn
    · exact (continuous_subtype_val.comp continuous_snd.snd).continuousOn
  have he : ∀ᶠ v : E in 𝓝 0, ∀ a ∈ K ×ˢ (univ : Set J),
      f (v, a) ∈ C.P.source ∧
      (C.α (f (v, a)) a.2).1 ∈ (extChartAt I x₀).target ∧
      dist ((extChartAt I x₀).symm (C.α (f (v, a)) a.2).1) a.1 < ε := by
    apply (hK.prod isCompact_univ).eventually_forall_of_forall_eventually
    intro a ha
    have hx := hKC ha.1
    have hf0 : f (0, a) = (extChartAt I x₀ a.1, 0) := by simp [f]
    have hsrc : f (0, a) ∈ C.P.source := by rw [hf0]; exact C.zero_mem_source _ hx.2
    have hS : ((0 : E), a) ∈ S := ⟨hx.1, hsrc⟩
    have hq := ball_subset_closedBall (C.P_source_subset hsrc)
    have hstat := FixedChartUniformNormalRadius.flow_zero_velocity
      (contDiff_geodesicFlowField (GeodesicTransport.chartChristoffelField_contDiff g x₀))
      C.T_pos (by simpa only [hf0] using (C.flow_law _ hq).1)
      (by simpa only [hf0] using (C.flow_law _ hq).2) a.2 a.2.property
    have hpos : (C.α (f (0, a)) a.2).1 = extChartAt I x₀ a.1 := by
      rw [hf0, hstat]
    have ht : (C.α (f (0, a)) a.2).1 ∈ (extChartAt I x₀).target := by
      rw [hpos]; exact (extChartAt I x₀).map_source hx.1
    have hca := hc.continuousAt (hopen.mem_nhds hS)
    have hdist := ((continuousAt_extChartAt_symm'' ht).comp
      (f := fun a : E × (M × J) => (C.α (f a) a.2.2).1) hca).dist continuousAt_snd.fst
    have heps : dist ((extChartAt I x₀).symm (C.α (f (0, a)) a.2).1) a.1 < ε := by
      rw [hpos, (extChartAt I x₀).left_inv hx.1, dist_self]
      exact hε
    filter_upwards [hopen.mem_nhds hS,
      hca ((isOpen_extChartAt_target x₀).mem_nhds ht),
      hdist.eventually (gt_mem_nhds heps)] with b hb hbt hbd
    exact ⟨hb.2, hbt, hbd⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ρ, hρ, ?_⟩
  intro x hx v hv
  have h := hball (show v ∈ ball (0 : E) ρ by simpa using hv)
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith [C.T_pos], C.T_pos.le⟩
  refine ⟨ball_subset_closedBall (C.P_source_subset (h (x, ⟨0, hzero⟩) ⟨hx, mem_univ _⟩).1), ?_⟩
  intro t ht
  exact (h (x, ⟨t, ht⟩) ⟨hx, mem_univ _⟩).2

end FixedChartMappedGeodesicAssembly

namespace FixedChartUniformEndpointReanchoring
open CartanSuppliedDifferentialSuccessor FixedChartMappedGeodesicAssembly
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The derivative-mapped retained geodesic solves the target initial-value
problem on the full unit interval, with both radii chosen uniformly first. -/
theorem uniformMappedGeodesicEquation_of_constantCurvature
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    FixedChartUniformEndpointReanchoring.UniformMappedGeodesicEquation C D K H := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨ηt, hηt, htransition⟩ := exists_uniform_christoffel_transition
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  obtain ⟨ηd, hηd, hdata⟩ := FixedChartMovingPositionJacobi.exists_radius g
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  obtain ⟨K', hK', hKK', hK'C⟩ := exists_compact_between hK C.isOpen_anchors hKC
  obtain ⟨δ, hδ, hδK'⟩ := hK.exists_cthickening_subset_open isOpen_interior hKK'
  obtain ⟨ρ, hρ, hflow⟩ := exists_uniform_flow_displacement_radius C K' hK' hK'C (half_pos hηt)
  refine ⟨min ηd (min δ (ηt / 2)), lt_min hηd (lt_min hδ (half_pos hηt)), ρ, hρ, ?_⟩
  intro x hx p hp L z d hz v hv _
  have hzd := hz.trans_le (min_le_left _ _)
  have hzδ := (hz.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hzt := (hz.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hzK' : z ∈ K' := interior_subset
    (hδK' (mem_cthickening_of_dist_le z x δ K hx hzδ.le))
  obtain ⟨hq, hpositions⟩ := hflow z hzK' v hv
  obtain ⟨hzC, hpD, _⟩ := hdata x hx p hp L z hzd
  let F := chartMap (patch C D) ⟨x, p, L⟩
  let q := (extChartAt I x₀ z, C.T⁻¹ • v)
  let γ := fun t : ℝ => ((C.α q (C.T * t)).1, C.T • (C.α q (C.T * t)).2)
  change FTransitionGeodesicMap.mappedState F γ 0 = _ ∧ _
  constructor
  · have hγ0 : γ 0 = (extChartAt I x₀ z, v) := by
      have h0 : C.α q 0 = q := (C.flow_law _ hq).1
      simp only [γ, mul_zero, h0]
      simp only [q, smul_smul, mul_inv_cancel₀ C.T_pos.ne', one_smul]
    change (F (γ 0).1, fderiv ℝ F (γ 0).1 (γ 0).2) = _
    rw [hγ0]
    exact Prod.ext (FixedChartMappedGeodesicAssembly.chartMap_apply_host (patch C D) ⟨x, p, L⟩ z hzC.1)
      (congrArg (fun A : E →L[ℝ] E => A v)
        (chartMap_fderiv_eq_successor_linear C D ⟨x, p, L⟩ z d hzC hpD))
  · intro t ht
    have htime : C.T * t ∈ Icc (-C.T) C.T := by
      constructor <;> nlinarith [C.T_pos, ht.1, ht.2]
    obtain ⟨hct, hdist⟩ := hpositions (C.T * t) htime
    let y := (extChartAt I x₀).symm (γ t).1
    have hyx : dist y x < ηt := by
      calc
        dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
        _ < ηt := by change dist y z < ηt / 2 at hdist; linarith
    have hcy : extChartAt I x₀ y = (γ t).1 := (extChartAt I x₀).right_inv hct
    obtain ⟨hC2, htrans⟩ := htransition x hx p hp L y hyx
    rw [hcy] at hC2 htrans
    exact mappedState_hasDerivWithinAt_of_differentiable_fderiv F _ _
      (normalizedFlow_hasDerivWithinAt C hq ht)
      (hC2.differentiableAt (by norm_num))
      ((hC2.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
        (by norm_num)) (htrans (γ t).2)

/-- Curvature alone gives the exact uniform supplied endpoint reanchoring law. -/
theorem uniformEndpointReanchoring_of_constantCurvature
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    FixedChartLocalSuccessorEquality.UniformEndpointReanchoring (patch C D) K H :=
  target_of_uniformMappedGeodesicEquation C D K H hK hKC hH hHD
    (uniformMappedGeodesicEquation_of_constantCurvature
      x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD)

end FixedChartUniformEndpointReanchoring
end Poincare
