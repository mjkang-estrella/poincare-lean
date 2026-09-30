import Poincare.Global.FiniteAtlasParabolicTensorSpace

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Poincare.BufferedTensorGraphTransport
open FiniteAtlasParabolicTensorSpace
universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Destination-partition transport coefficient from source slot `(a,b)`
to destination slot `(c,d)`. The gate prevents off-chart extension values
from contributing. The source entries already carry their own partition. -/
def weight (A : AtlasData M) (i : Fin A.cover.chartCount)
    (θ ξ : ClosedSmoothModel 3 → ℝ) (F : ClosedSmoothModel 3 → ClosedSmoothModel 3)
    (a b c d : Fin 3) (z : ClosedSmoothModel 3) : ℝ :=
  θ z * ((A.partition i) ((chart A i).symm z) * ξ (F z) *
    (fderiv ℝ F z ((EuclideanSpace.basisFun (Fin 3) ℝ) c)) a *
    (fderiv ℝ F z ((EuclideanSpace.basisFun (Fin 3) ℝ) d)) b)

end Poincare.BufferedTensorGraphTransport
