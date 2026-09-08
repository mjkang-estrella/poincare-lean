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

end FixedChartMovingPositionJacobi
end Poincare
