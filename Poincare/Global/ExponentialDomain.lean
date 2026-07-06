import Poincare.Global.ExponentialGerm

/-!
# Uniform local geodesic domains

This file records the first quantitative domain statement for the geodesic
layer: a common existence time for all sufficiently small initial chart
velocities at a fixed base point.

The fixed-time exponential map is not defined here yet.  The available
germ-level homogeneity theorem is only an eventual statement near time `0`;
turning the uniform chart solutions below into endpoint values at one common
positive time needs an interval-uniqueness or closed-ball flow statement
exposed from the Picard-Lindelöf construction.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Uniform local chart-geodesic existence near the zero velocity.

For a fixed metric and base point, Mathlib's quantitative Picard-Lindelöf
theorem supplies one velocity radius `δ` and one time radius `ε` such that
every chart velocity with `‖v₀‖ < δ` has a chart solution on
`Ioo (-ε) ε`.
-/
theorem exists_uniform_local_geodesic_chart_solution
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ v₀ : E, ‖v₀‖ < δ →
      ∃ γ : ℝ → E × E,
        γ 0 = (extChartAt I x₀ x₀, v₀) ∧
        ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt γ
            (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t := by
  let p₀ : E × E := (extChartAt I x₀ x₀, 0)
  have hflow :
      ContDiffAt ℝ 1
        (geodesicFlowField (chartChristoffelField g x₀)) p₀ := by
    simpa [p₀] using
      (geodesicFlowField_chartChristoffelField_contDiffAt
        (g := g) (x₀ := x₀) (v₀ := (0 : E)))
  rcases hflow.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
      0 with
    ⟨δ, hδ, ε, hε, hsol⟩
  refine ⟨δ, hδ, ε, hε, fun v₀ hv₀ ↦ ?_⟩
  have hp :
      (extChartAt I x₀ x₀, v₀) ∈
        Metric.closedBall p₀ δ := by
    rw [Metric.mem_closedBall]
    change dist (extChartAt I x₀ x₀, v₀) (extChartAt I x₀ x₀, (0 : E)) ≤ δ
    rw [dist_prod_same_left]
    simpa [dist_eq_norm] using le_of_lt hv₀
  rcases hsol (extChartAt I x₀ x₀, v₀) hp with
    ⟨γ, hγ0, hγder⟩
  refine ⟨γ, hγ0, ?_⟩
  simpa only [sub_eq_add_neg, zero_sub, zero_add] using hγder

end GeodesicTransport
end Poincare
