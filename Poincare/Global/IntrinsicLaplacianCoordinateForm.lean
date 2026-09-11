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

/-- In the inverse-chart frame the Laplacian uses the genuine inverse Gram field. -/
theorem laplacianAt_eq_chart_hessian
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (p : M)
    (z : (extChartAt I p).target) :
    g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
      ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
        g.hessianAt f ((extChartAt I p).symm z)
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
            (EuclideanSpace.basisFun (Fin n) ℝ i))
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
            (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p z.2
  have hG : g.metricMatrixInBasisAt ((extChartAt I p).symm z) b =
      inverseChartPullbackGramMatrixField g p z := by
    ext i j
    simp only [ClosedSmoothRiemannianMetric.metricMatrixInBasisAt_apply,
      ClosedSmoothRiemannianMetric.metricBilinAt_apply, b,
      ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
    rfl
  change g.laplacianAt f ((extChartAt I p).symm z) = _
  rw [laplacianAt_eq_inverseGram_hessian g f _ b, hG]
  simp only [b, ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]

end Poincare.IntrinsicLaplacianCoordinateForm
