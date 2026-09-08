import Poincare.Global.CartanSuppliedSourceMap

/-!
# Neighborhood transport for supplied source Cartan germs

Agreement of supplied normal coordinates near an anchor transfers to the
Cartan maps and to the inverse normal coordinates near zero. The inverse
comparison uses the partial inverse laws only on their open domains.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanSuppliedSourceGermTransfer

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Normal-coordinate agreement near the anchor gives Cartan germ agreement. -/
theorem germ_eventuallyEq_of_normal_eventuallyEq
    (S S' : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E)
    (h : (S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E)) :
    (CartanSuppliedSourceMap.germ S F x p K : M → RoundSphere3)
      =ᶠ[𝓝 x]
    (CartanSuppliedSourceMap.germ S' F x p K : M → RoundSphere3) := by
  rw [CartanSuppliedSourceMap.germ_apply, CartanSuppliedSourceMap.germ_apply]
  filter_upwards [h] with z hz
  rw [hz]

end CartanSuppliedSourceGermTransfer
end Poincare
