import Poincare.Global.ScalarVariation

/-!
# The intrinsic Hessian square in the scalar-gradient quotient

The metric trace below is the genuine squared norm of the covariant derivative
of a gradient.  Completing its square against the rank-one gradient map gives
the Hessian/mixed-gradient estimate without a curvature or flow hypothesis.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare.HamiltonScalarGradientHessianBound

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- A metric trace of a nonnegative bilinear form is nonnegative. -/
theorem metricTraceInBasisAt_nonneg
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (B : LinearMap.BilinForm ℝ (TM x))
    (hB : ∀ v, 0 ≤ B v v)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) :
    0 ≤ metricTraceInBasisAt g x B b := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x)
  rw [metricTraceInBasisAt_eq_metricTraceInBasisAt g x B b c]
  unfold metricTraceInBasisAt
  apply Finset.sum_nonneg
  intro i _
  rw [metricDualVectorAt_orthogonalBasis_coord_eq g x c hc i]
  simp only [map_smul, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (g.metricBilinAt_pos x (c.ne_zero i)).le) (hB _)

/-- The intrinsic squared norm of a linear map controls its gradient rank-one
mixed term by the actual nonnegative square of their difference. -/
theorem linearMap_rankOne_square_completion
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (D : TM x →ₗ[ℝ] TM x) (V : TM x) (a : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) :
    0 ≤ a ^ 2 * (∑ i, g.inner x (D (b i))
        (D (metricDualVectorAt g x (b.coord i)))) -
      2 * a * g.inner x (D V) V + (g.inner x V V) ^ 2 := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let B : LinearMap.BilinForm ℝ (TM x) := (g.metricBilinAt x).compl₁₂ D D
  obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x)
  let d := fun i ↦ g.inner x (c i) (c i)
  have hd : ∀ i, 0 < d i := fun i ↦ g.inner_pos x (c.ne_zero i)
  have hH : (∑ i, g.inner x (D (b i))
        (D (metricDualVectorAt g x (b.coord i)))) =
      ∑ i, (d i)⁻¹ * g.inner x (D (c i)) (D (c i)) := by
    change metricTraceInBasisAt g x B b = _
    rw [metricTraceInBasisAt_eq_metricTraceInBasisAt g x B b c]
    unfold metricTraceInBasisAt
    apply Finset.sum_congr rfl
    intro i _
    rw [metricDualVectorAt_orthogonalBasis_coord_eq g x c hc i]
    simp [B, d, g.metricBilinAt_apply]
  have hcoord : ∀ i, c.coord i V = (d i)⁻¹ * g.inner x (c i) V := by
    intro i
    rw [coord_eq_inner_metricDualVectorAt_of_basis g x c i V,
      metricDualVectorAt_orthogonalBasis_coord_eq g x c hc i]
    simp only [map_smul, smul_eq_mul]
    rw [g.inner_symm x V (c i)]
    rfl
  have hcV : (∑ i, c.coord i V • c i) = V := by
    simpa only [Module.Basis.coord_apply] using c.sum_repr V
  have hmix : (∑ i, (d i)⁻¹ * g.inner x (c i) V *
        g.inner x (D (c i)) V) = g.inner x (D V) V := by
    simp_rw [← hcoord]
    calc
      (∑ i, c.coord i V * g.inner x (D (c i)) V) =
          g.inner x (D (∑ i, c.coord i V • c i)) V := by
            simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
              ContinuousLinearMap.smul_apply, smul_eq_mul]
      _ = g.inner x (D V) V := by rw [hcV]
  have hrank : (∑ i, (d i)⁻¹ * (g.inner x (c i) V) ^ 2) =
      g.inner x V V := by
    calc
      (∑ i, (d i)⁻¹ * (g.inner x (c i) V) ^ 2) =
          ∑ i, c.coord i V * g.inner x (c i) V := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hcoord]
            ring
      _ = g.inner x V V := sum_basis_coord_inner_eq_inner g x c V V
  have hnonneg : 0 ≤ ∑ i, (d i)⁻¹ *
      g.inner x (a • D (c i) - g.inner x (c i) V • V)
        (a • D (c i) - g.inner x (c i) V • V) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (inv_nonneg.mpr (hd i).le) (g.inner_nonneg x _)
  have hexpand : (∑ i, (d i)⁻¹ *
      g.inner x (a • D (c i) - g.inner x (c i) V • V)
        (a • D (c i) - g.inner x (c i) V • V)) =
      a ^ 2 * (∑ i, (d i)⁻¹ * g.inner x (D (c i)) (D (c i))) -
      2 * a * (∑ i, (d i)⁻¹ * g.inner x (c i) V * g.inner x (D (c i)) V) +
      (∑ i, (d i)⁻¹ * (g.inner x (c i) V) ^ 2) * g.inner x V V := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.inner_symm x V (D (c i))]
    ring
  rw [hexpand, hmix, hrank, ← hH] at hnonneg
  nlinarith only [hnonneg]

/-- Metric compatibility identifies the derivative of the gradient norm. -/
theorem inner_gradient_gradientNormSq
    (g : ClosedSmoothRiemannianMetric n M) {f : M → ℝ} (x : M)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    g.inner x (g.gradientAt f x)
        (g.gradientAt (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) x) =
      2 * g.inner x (g.leviCivita (g.gradient f) x (g.gradientAt f x))
        (g.gradientAt f x) := by
  have hgrad := g.mdifferentiableAt_gradient hf
  rw [g.inner_symm, g.inner_gradientAt]
  have h := g.leviCivita_metricCompatibleAt x hgrad hgrad (g.gradientAt f x)
  change extDerivFun (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y))
    x (g.gradientAt f x) = _ at h
  dsimp only [ClosedSmoothRiemannianMetric.gradient] at h
  rw [g.inner_symm x (g.gradientAt f x)] at h
  linarith only [h]

end Poincare.HamiltonScalarGradientHessianBound

namespace Poincare.HamiltonScalarGradientHessianBound

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The genuine Hessian square needed by the scalar-gradient quotient, for an
arbitrary real coefficient and any locally twice differentiable scalar. -/
theorem hessian_gradient_square_completion
    (g : ClosedSmoothRiemannianMetric 3 M) {f : M → ℝ} (x : M)
    (hf : ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f x) (a : ℝ) :
    let S := fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)
    let H := ∑ i, g.inner x
      (g.leviCivita (g.gradient f) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
      (g.leviCivita (g.gradient f) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
    0 ≤ a ^ 2 * H - a * g.inner x (g.gradientAt f x) (g.gradientAt S x) + (S x) ^ 2 := by
  dsimp only
  rw [inner_gradient_gradientNormSq g x hf]
  have h := linearMap_rankOne_square_completion g x
    (g.leviCivita (g.gradient f) x).toLinearMap (g.gradientAt f x) a
    (Module.finBasis ℝ (ClosedSmoothModel 3))
  simpa only [ContinuousLinearMap.coe_coe, mul_assoc, mul_comm, mul_left_comm] using h

end Poincare.HamiltonScalarGradientHessianBound
