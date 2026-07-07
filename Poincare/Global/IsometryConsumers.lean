import Poincare.Global.RigidityComplete
import Poincare.Global.CartanChain
import Poincare.Global.CoveringSkeleton

/-!
# Consumers of the completed Cartan local isometry theorem

This module records the first strict-partial consumer of
`RigidityComplete.cartanMap_isLocalIsometry`: the chart-level Cartan map has an
inverse-function-theorem partial homeomorphism at every nonzero point in the
shrunk normal ball, and the pullback identity is expressed through the
equivalence-valued differential used for that IFT application.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Poincare
namespace IsometryConsumers

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The completed Cartan local-isometry theorem supplies an inverse-function
theorem witness for the chart-level Cartan map on the punctured shrunk normal
ball.

The returned `OpenPartialHomeomorph` is strict-partial: its coerced function is
the chart Cartan map, and the indicated source exponential coordinate lies in
its source.  The differential is bundled as a continuous linear equivalence,
obtained from the source endpoint differential, tangent alignment, and target
endpoint differential.
-/
theorem exists_cartanChartMap_ift_partialHomeomorph_on_punctured_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ), ∀ v : E3, ‖v‖ < ρ → v ≠ 0 →
      ∃ D : E3 ≃L[ℝ] E3, ∃ U : OpenPartialHomeomorph E3 E3,
        (U : E3 → E3) = CartanDifferential.cartanChartMap g x₀ p₀ L ∧
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∈
            U.source ∧
          HasStrictFDerivAt
            (CartanDifferential.cartanChartMap g x₀ p₀ L)
            (D : E3 →L[ℝ] E3)
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
          ∀ u u' : E3,
            CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) p₀) (L v))
                (D u) (D u') =
              CovariantDerivative.chartMetric g.inner x₀
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
                u u' := by
  rcases
      RigidityComplete.cartanMap_isLocalIsometry
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ_pos, _T, _hT_pos, hlocal⟩
  refine ⟨ρ, hρ_pos, ?_⟩
  intro v hv hvne
  rcases hlocal v hv hvne with ⟨A, B, hderiv, hpullback⟩
  let D : E3 ≃L[ℝ] E3 := (A.symm.trans L.toContinuousLinearEquiv).trans B
  have hD :
      (D : E3 →L[ℝ] E3) =
        CartanLocalIsometry.cartanChartDifferential L A B := by
    ext u
    simp [D, CartanLocalIsometry.cartanChartDifferential]
  have hderivD :
      HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (D : E3 →L[ℝ] E3)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) := by
    rw [hD]
    exact hderiv
  let U : OpenPartialHomeomorph E3 E3 :=
    hderivD.toOpenPartialHomeomorph
      (CartanDifferential.cartanChartMap g x₀ p₀ L)
  refine ⟨D, U, ?_, ?_, hderivD, ?_⟩
  · rfl
  · simpa [U] using hderivD.mem_toOpenPartialHomeomorph_source
  · intro u u'
    simpa [hD] using hpullback u u'

end IsometryConsumers
end Poincare
