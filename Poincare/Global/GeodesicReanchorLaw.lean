import Poincare.Global.GeodesicReanchor

/-!
# Double-good chart metric transport for geodesic re-anchoring

This module records the part of the double-good transition law that can be
proved directly from the existing chart-transport API: on a chart overlap,
the two chart representations of the same closed metric agree after pushing
model tangent vectors through the chart transition differential.

The remaining geodesic ODE transition law also needs the corresponding
Christoffel/acceleration transformation.  That requires an additional
second-derivative chain-rule bridge for the total transition map
`chartTransition x₀ y₀`; it is documented in the accompanying harness report.
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

section MetricTransport

variable (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)

/--
The chart-transition differential in the form naturally used by
`CovariantDerivative.chartMetric`: first move a model vector at the `x₀`
chart point back to the manifold by the inverse-chart differential, then push
it forward by the `y₀` chart differential.
-/
def chartTransitionMFDeriv (z : E) : E →L[ℝ] E :=
  (mfderiv I 𝓘(ℝ, E) (extChartAt I y₀)
      ((extChartAt I x₀).symm z)).comp
    (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z)

/--
Whenever the point read by the `x₀` inverse chart lies in the `y₀` chart
source, the two chart metrics are the same tensor: both sides evaluate
`g.inner` at the underlying manifold point `(extChartAt I x₀).symm z`.

This is the transport identity needed by the Koszul-pairing route.  It is
stated with `chartTransitionMFDeriv`, the manifold differential expression
that is definitionally compatible with the current `chartMetric` API.
-/
theorem chartMetric_chartTransitionMFDeriv
    {z : E}
    (hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source)
    (u v : E) :
    CovariantDerivative.chartMetric g.inner y₀ (chartTransition x₀ y₀ z)
        (chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z u)
        (chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z v) =
      CovariantDerivative.chartMetric g.inner x₀ z u v := by
  have hleft :=
    CovariantDerivative.chartMetric_apply_chart g.inner y₀ hy
      ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z) u)
      ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z) v)
  simp only [chartTransition, chartTransitionMFDeriv]
  change
    CovariantDerivative.chartMetric g.inner y₀
        (extChartAt I y₀ ((extChartAt I x₀).symm z))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I y₀)
            ((extChartAt I x₀).symm z))
          ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
              (range I) z) u))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I y₀)
            ((extChartAt I x₀).symm z))
          ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
              (range I) z) v)) =
      CovariantDerivative.chartMetric g.inner x₀ z u v
  rw [hleft]
  rw [CovariantDerivative.chartMetric_apply]

end MetricTransport

end GeodesicTransport
end Poincare
