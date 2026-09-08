import Poincare.Global.FixedChartLocalSuccessorEquality
import Poincare.Global.FixedChartMovingPositionJacobi
import Poincare.Global.LCNaturality

/-!
# Differential and geodesic interfaces for uniform endpoint reanchoring

All manifold radii precede the moving anchors, alignments, and data.
-/

noncomputable section
set_option maxHeartbeats 1200000
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

end FixedChartUniformEndpointReanchoring
end Poincare
