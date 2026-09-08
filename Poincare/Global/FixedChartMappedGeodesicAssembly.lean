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

end FixedChartMappedGeodesicAssembly
end Poincare
