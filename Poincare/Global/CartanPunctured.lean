import Poincare.Global.CartanExpansionBridge
import Poincare.Global.CartanIsometryFinal

/-!
# Punctured Cartan endpoint expansion consumer

The weighted source endpoint expansion is inconsistent at the zero normal
vector with the current `transverseScale`.  This file records the corrected
consumer split: nonzero normal vectors use the punctured weighted expansion,
while the zero vector is discharged by the unconditional anchor theorem.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanPunctured

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Corrected Cartan local-isometry consumer with the quantifier punctured at the
source side.  The conclusion is an explicit case split: at `v = 0` it returns
the anchor local-isometry theorem, and at `v ≠ 0` it returns the weighted
normal-coordinate conclusion from the punctured source expansion plus the
round-sphere target expansion.
-/
theorem cartanMap_anchor_or_punctured_localIsometry_of_sourceExpansion_and_roundSphere
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v))
    (u u' : E)
    (hDu :
      CartanLocalIsometry.cartanChartDifferential L A B u =
        CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u)
    (hDu' :
      CartanLocalIsometry.cartanChartDifferential L A B u' =
        CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u')
    (hsourceExpansion :
      CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀
        (fun v : E =>
          CartanExpansionBridge.roundSphereEndpointChartWeight p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v)))) :
    (v = 0 ∧
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
            u u') ∨
      (v ≠ 0 ∧
        HasStrictFDerivAt
            (CartanDifferential.cartanChartMap g x₀ p₀ L)
            (CartanLocalIsometry.cartanChartDifferential L A B)
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) p₀) (L v))
              (CartanLocalIsometry.cartanChartDifferential L A B u)
              (CartanLocalIsometry.cartanChartDifferential L A B u') =
            CovariantDerivative.chartMetric g.inner x₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
              u u') := by
  by_cases hvzero : v = 0
  · left
    exact ⟨hvzero,
      CartanIsometryFinal.cartanChartMap_anchor_isLocalIsometry
        (g := g) (x₀ := x₀) (p₀ := p₀) L u u'⟩
  · right
    exact ⟨hvzero,
      CartanExpansionBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceExpansion_and_roundSphere
        (g := g) (x₀ := x₀) (p₀ := p₀) L
        hvsrc hvzero hsourceDeriv htargetDeriv u u' hDu hDu'
        hsourceExpansion⟩

end CartanPunctured
end Poincare
