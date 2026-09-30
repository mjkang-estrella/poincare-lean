import Poincare.Global.BufferedTensorGraphTransportDefinitions

noncomputable section
set_option autoImplicit false

namespace Poincare

/-- Buffer-localized tensor coefficient before destination partition weighting.
The source buffer and both actual differential slots are retained. -/
def BufferedUnweightedGraphTransport.weight
    (θ ψ ξ : ClosedSmoothModel 3 → ℝ)
    (F : ClosedSmoothModel 3 → ClosedSmoothModel 3)
    (a b c d : Fin 3) (z : ClosedSmoothModel 3) : ℝ :=
  θ z * (ψ z * ξ (F z) *
    (fderiv ℝ F z ((EuclideanSpace.basisFun (Fin 3) ℝ) c)) a *
    (fderiv ℝ F z ((EuclideanSpace.basisFun (Fin 3) ℝ) d)) b)

end Poincare
