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

end FixedChartUniformEndpointReanchoring
end Poincare
