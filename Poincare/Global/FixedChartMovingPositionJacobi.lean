import Poincare.Global.FixedChartUniformJacobiComparison

/-!
# Metric invariants along retained moving-position geodesics

The initial state ranges over the original patch ball. Time is never shrunk.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartMovingPositionJacobi
open GeodesicTransport
open FixedChartUniformJacobiComparison

/-- Every retained position lies in the chart target and has cutoff one on a
neighborhood, including at both endpoint times. -/
theorem flow_mem_target_cutoffOne {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    (C.α q t).1 ∈ (extChartAt I x₀).target ∧
      (∀ᶠ z in 𝓝 (C.α q t).1, cutoff (n := 3) x₀ z = 1) := by
  have hcut := hU (C.position_mem q hq t ht)
  refine ⟨?_, hcut⟩
  exact cutoff_tsupport x₀ (subset_tsupport _
    (Function.mem_support.mpr (by rw [hcut.self_of_nhds]; exact one_ne_zero)))

/-- Speed preservation on the entire retained interval, at arbitrary initial
position and velocity in the original closed state ball. -/
theorem flow_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    chartGeodesicMetric g x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2 =
      chartGeodesicMetric g x₀ q.1 q.2 q.2 := by
  have hder := (C.flow_law q hq).2
  have hcont := HasDerivWithinAt.continuousOn hder
  have hmetric : Continuous (chartGeodesicMetric g x₀) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z).continuousAt)
  have heq : EqOn
      (fun t => chartGeodesicMetric g x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2)
      (fun _ => chartGeodesicMetric g x₀ q.1 q.2 q.2) (Ioo (-C.T) C.T) := by
    intro s hs
    have h := chart_geodesic_speed_constantOn_Ioo g x₀
      (fun τ hτ => (hder τ (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2)) hs
      (show (0 : ℝ) ∈ Ioo (-C.T) C.T from ⟨by linarith [C.T_pos], C.T_pos⟩)
    simpa only [(C.flow_law q hq).1] using h
  exact heq.of_subset_closure
    (((hmetric.comp_continuousOn hcont.fst).clm_apply hcont.snd).clm_apply hcont.snd)
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (show -C.T ≠ C.T by linarith [C.T_pos])]) ht

/-- On a cutoff-one patch the same invariant is the actual chart metric,
measured at the moving initial position. -/
theorem flow_chartMetric_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    CovariantDerivative.chartMetric g.inner x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2 =
      CovariantDerivative.chartMetric g.inner x₀ q.1 q.2 q.2 := by
  have h0 : (0 : ℝ) ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos.le⟩
  have hc0 := (flow_mem_target_cutoffOne C hU hq h0).2.self_of_nhds
  rw [(C.flow_law q hq).1] at hc0
  have h := flow_speed_eq_initial C hq ht
  dsimp only [chartGeodesicMetric] at h
  rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) (flow_mem_target_cutoffOne C hU hq ht).2.self_of_nhds,
    blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀) hc0] at h
  exact h

end FixedChartMovingPositionJacobi
end Poincare
