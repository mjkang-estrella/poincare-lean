import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
import Poincare.Global.DeTurckPrincipalIdentity

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.IntrinsicLaplacianCoordinateForm

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The intrinsic Hessian trace contracts with the inverse Gram matrix in any basis. -/
theorem laplacianAt_eq_inverseGram_hessian
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ (TM x)) :
    g.laplacianAt f x = ∑ i, ∑ j,
      (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [Poincare.laplacianAt_eq_sum_hessianAt_basis g f x b]
  apply Finset.sum_congr rfl
  intro i _
  rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
  change g.hessianDualAt f x (b i) (∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j • b j) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

end Poincare.IntrinsicLaplacianCoordinateForm
