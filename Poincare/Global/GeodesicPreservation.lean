import Poincare.Global.ExpNaturality

/-!
# Anchor-based Cartan geodesic preservation identity

This module isolates the charted exponential-naturality identity available
directly from the strict Cartan partial homeomorphism.  The remaining global
re-anchoring step is to identify the old carried germ with this re-anchored
Cartan map on the common source.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace GeodesicPreservation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
On the strict source of the anchor-based Cartan partial homeomorphism, applying
the target anchor chart to the Cartan map gives exactly the target exponential
chart of the aligned source exponential coordinate.
-/
theorem cartanMap_target_chart_exp_naturality
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) {x : M}
    (hx : x ∈ (CartanMap.openPartialHomeomorph g x₀ p₀ L).source) :
    GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀
        (L ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) x₀).symm ((chartAt E x₀) x))) =
      (chartAt E p₀) (CartanMap.cartanMap g x₀ p₀ L x) := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀
  let y : E := eS (L (eM.symm ((chartAt E x₀) x)))
  have hsource :
      x ∈ (chartAt E x₀).source ∧
        (chartAt E x₀) x ∈ eM.target ∧
          eM.symm ((chartAt E x₀) x) ∈
              (CartanMap.tangentAlignmentOpenPartialHomeomorph L).source ∧
            L (eM.symm ((chartAt E x₀) x)) ∈ eS.source ∧
              (chartAt E p₀) (GeodesicTransport.expAt roundSphereMetric3 p₀
                (L (eM.symm ((chartAt E x₀) x)))) ∈ (chartAt E p₀).target := by
    simpa [eM, eS, CartanMap.openPartialHomeomorph] using hx
  have hy : y ∈ (chartAt E p₀).target := by
    simpa [y, eS, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
      hsource.2.2.2.2
  change y = (chartAt E p₀) ((chartAt E p₀).symm y)
  exact ((chartAt E p₀).right_inv hy).symm

end GeodesicPreservation
end Poincare
