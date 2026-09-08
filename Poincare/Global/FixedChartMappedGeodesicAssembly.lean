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

end FixedChartMappedGeodesicAssembly
end Poincare
