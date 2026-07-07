import Poincare.Global.GeodesicReanchorClose
import Poincare.Global.GeodesicSpeed

/-!
# Transported compatibility strict partial

This module records the metric-transition input for transported compatibility:
on an honest overlap where both blending cutoffs are `1`, the target blended
chart metric is the pullback of the source blended chart metric by the chart
transition differential.
-/

noncomputable section

open Filter Set
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
On an honest overlap where both blending cutoffs are `1`, the target blended
chart metric is the pullback of the source blended chart metric by the chart
transition differential.
-/
theorem chartGeodesicMetric_chartTransitionDeriv_of_cutoff_eq_one
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source)
    (hχx : cutoff (n := n) x₀ z = 1)
    (hχy : cutoff (n := n) y₀ (chartTransition x₀ y₀ z) = 1)
    (u w : E) :
    chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
        (chartTransitionDeriv x₀ y₀ z u)
        (chartTransitionDeriv x₀ y₀ z w) =
      chartGeodesicMetric g x₀ z u w := by
  have htargetMetric :
      chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z) =
        CovariantDerivative.chartMetric g.inner y₀ (chartTransition x₀ y₀ z) := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := y₀) (z := chartTransition x₀ y₀ z) hχy)
  have hsourceMetric :
      chartGeodesicMetric g x₀ z =
        CovariantDerivative.chartMetric g.inner x₀ z := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := x₀) (z := z) hχx)
  rw [htargetMetric, hsourceMetric]
  exact chartMetric_chartTransitionDeriv
    (g := g) (x₀ := x₀) (y₀ := y₀) hz hy u w

end GeodesicTransport
end Poincare
