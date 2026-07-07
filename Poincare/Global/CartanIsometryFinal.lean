import Poincare.Global.CartanLocalIsometry

/-!
# Cartan isometry final boundary

This module records the unconditional anchor case of the Cartan local-isometry
assembly.  The nonzero normal-ball case is reduced in `CartanLocalIsometry` to
the endpoint expansion bundle.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanIsometryFinal

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
At the anchor, the Cartan chart map is unconditionally metric-preserving:
the strict derivative is the tangent alignment and the chart metrics agree by
the defining alignment law.
-/
theorem cartanChartMap_anchor_isLocalIsometry
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) (u u' : E) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (L.toContinuousLinearEquiv : E →L[ℝ] E)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) (0 : E)) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L (0 : E)))
          (L.toContinuousLinearEquiv u)
          (L.toContinuousLinearEquiv u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) (0 : E))
          u u' := by
  constructor
  · exact
      CartanDifferential.cartanChartMap_hasStrictFDerivAt_anchor
        (g := g) (x₀ := x₀) (p₀ := p₀) L
  · simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric,
      CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor] using
      CartanMap.TangentAlignment.map_app L u u'

end CartanIsometryFinal
end Poincare
