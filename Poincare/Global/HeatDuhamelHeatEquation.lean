import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

end Poincare.HeatDuhamelHeatEquation
