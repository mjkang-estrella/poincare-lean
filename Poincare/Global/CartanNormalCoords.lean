import Poincare.Global.CartanLocalIsometry

/-!
# Cartan map in exponential normal coordinates

This module records the strict normal-coordinate reroute boundary: after
conjugating the local Cartan chart map by the source and target exponential
charts, the map is exactly the tangent alignment `L`.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanNormalCoords

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
In exponential normal coordinates, the local Cartan chart map is the tangent
alignment `L`.

This is the formal `exp⁻¹_{p₀} ∘ Φ ∘ exp_{x₀} = L` statement for the charted
exponential partial homeomorphisms.  The two membership hypotheses are the
non-junk local-chart conditions required by `OpenPartialHomeomorph.left_inv`.
-/
theorem expChart_symm_cartanChartMap_expChart_eq_tangentAlignment
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) {v : E}
    (hvsrc :
      v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hvtgt :
      L v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀).source) :
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀).symm
      (CartanDifferential.cartanChartMap g x₀ p₀ L
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)) =
      L v := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀
  have hleft : eM.symm (eM v) = v := eM.left_inv hvsrc
  have hchart :
      CartanDifferential.cartanChartMap g x₀ p₀ L (eM v) = eS (L v) := by
    change eS (L (eM.symm (eM v))) = eS (L v)
    rw [hleft]
  rw [hchart]
  exact eS.left_inv hvtgt

end CartanNormalCoords
end Poincare
