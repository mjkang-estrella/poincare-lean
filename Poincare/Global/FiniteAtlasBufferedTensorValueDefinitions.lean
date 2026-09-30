import Poincare.Global.FiniteAtlasJacobianCocycle

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Poincare.FiniteAtlasBufferedTensorValue
open FiniteAtlasParabolicTensorSpace
universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Sum actual source tensors in a destination chart, retaining its partition
and each source buffer. Off-source values of total charts are excluded. -/
def value (A : AtlasData M)
    (ξ : Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ)
    (W : Fin A.cover.chartCount → Fin 3 → Fin 3 → ClosedSmoothModel 3 → ℝ)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (x : M) : ℝ :=
  A.partition i x * ∑ j : Fin A.cover.chartCount,
    @ite ℝ (x ∈ (chart A j).source) (Classical.propDecidable _)
      (ξ j (chart A j x) * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) * W j c d (chart A j x)) 0

end Poincare.FiniteAtlasBufferedTensorValue
