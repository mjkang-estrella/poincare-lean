/-
The Laplacian on the model space.

Every evolution equation of the Ricci flow (`∂R/∂t = ΔR + 2|Ric|²`, the
heat flows of Perelman's functionals) is driven by the metric Laplacian.
This module defines the Laplacian of a scalar function with respect to a
metric on the model space — the trace of the second derivative against the
inverse metric — and verifies it on quadratic forms.
-/

import Poincare.KoszulExistence
import Poincare.MaximumPrinciple
import Mathlib.LinearAlgebra.QuadraticForm.Basic

noncomputable section

open CovariantDerivative

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The metric Laplacian of a scalar function on the model space: the
trace of the Hessian against the inverse metric. -/
def modelLaplacian (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (f : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E
    ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
      (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
        ((fderiv ℝ (fderiv ℝ f) x).toLinearMap)))

theorem modelLaplacian_add (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) {f g : E → ℝ} {x : E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    modelLaplacian b hb (f + g) x =
      modelLaplacian b hb f x + modelLaplacian b hb g x := by
  unfold modelLaplacian
  have h1 : fderiv ℝ (fderiv ℝ (f + g)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    have hdf : fderiv ℝ (f + g) = fderiv ℝ f + fderiv ℝ g := by
      funext y
      exact fderiv_add ((hf.differentiable (by norm_num)) y)
        ((hg.differentiable (by norm_num)) y)
    rw [hdf]
    rw [show (fderiv ℝ f + fderiv ℝ g) =
      fun y ↦ fderiv ℝ f y + fderiv ℝ g y from rfl]
    exact fderiv_add
      (((hf.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)) x)
      (((hg.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)) x)
  rw [h1]
  simp only [ContinuousLinearMap.coe_add, LinearMap.comp_add, map_add]

theorem modelLaplacian_smul (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) {f : E → ℝ} {x : E} (c : ℝ)
    (hf : ContDiff ℝ 2 f) :
    modelLaplacian b hb (fun y ↦ c * f y) x =
      c * modelLaplacian b hb f x := by
  unfold modelLaplacian
  have h1 : fderiv ℝ (fderiv ℝ (fun y ↦ c * f y)) x =
      c • fderiv ℝ (fderiv ℝ f) x := by
    have hdf : fderiv ℝ (fun y ↦ c * f y) = fun y ↦ c • fderiv ℝ f y := by
      funext y
      exact fderiv_const_mul ((hf.differentiable (by norm_num)) y) c
    rw [hdf]
    rw [show (fun y ↦ c • fderiv ℝ f y) = fun y ↦ c • (fderiv ℝ f) y
      from rfl]
    exact fderiv_const_smul
      (((hf.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)) x) c
  rw [h1]
  simp only [ContinuousLinearMap.coe_smul, LinearMap.comp_smul, map_smul,
    LinearMap.smul_comp, smul_eq_mul]

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The Laplacian of the metric's own quadratic form is twice the
dimension** — the verification computation anchoring `modelLaplacian`
(`Δ|x|² = 2n` in the Euclidean case).
-/
theorem modelLaplacian_quadratic (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate)
    (hbs : ∀ v w : E, b v w = b w v) (x : E) :
    modelLaplacian b hb (fun y ↦ b y y) x =
      2 * Module.finrank ℝ E := by
  set bC : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ b) with hbC
  have hbCapp : ∀ v w : E, bC v w = b v w := fun v w ↦ rfl
  -- First derivative: `D f y = bC y + bC.flip y` (with symmetry, `2 bC y`).
  have hf1 : ∀ y : E, HasFDerivAt (fun z ↦ b z z)
      (bC y + bC.flip y) y := by
    intro y
    have hc : HasFDerivAt (fun z : E ↦ bC z) bC y := bC.hasFDerivAt
    have h := hc.clm_apply (hasFDerivAt_id y)
    have heq : (fun z : E ↦ bC z z) = fun z ↦ b z z := by
      funext z
      exact hbCapp z z
    rw [← heq]
    convert h using 1
  -- The first-derivative map is the continuous linear map `bC + bC.flip`,
  -- so the second derivative is constant equal to it.
  have hdf : fderiv ℝ (fun z ↦ b z z) = ⇑(bC + bC.flip) := by
    funext y
    rw [(hf1 y).fderiv]
    rfl
  have hf2 : fderiv ℝ (fderiv ℝ (fun z ↦ b z z)) x = bC + bC.flip := by
    rw [hdf]
    exact (bC + bC.flip).fderiv
  -- Symmetry collapses the flip.
  have hflip : bC.flip = bC := by
    ext v w
    rw [ContinuousLinearMap.flip_apply, hbCapp, hbCapp, hbs]
  unfold modelLaplacian
  rw [hf2, hflip]
  have htwo : bC + bC = (2 : ℝ) • bC := by
    ext v w
    simp [two_mul]
  rw [htwo]
  -- The remaining composition is twice the identity.
  have hassemble : (LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
      (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
        (((2 : ℝ) • bC).toLinearMap)) = (2 : ℝ) • LinearMap.id := by
    apply LinearMap.ext
    intro v
    have hbv : LinearMap.toContinuousLinearMap.symm
        (bC.toLinearMap v) = b v := by
      have h2 : bC.toLinearMap v = LinearMap.toContinuousLinearMap (b v) :=
        rfl
      rw [h2, LinearEquiv.symm_apply_apply]
    have hΦv : (b v : Module.Dual ℝ E) =
        LinearMap.BilinForm.toDual b hb v := by
      apply LinearMap.ext
      intro w
      rw [LinearMap.BilinForm.toDual_def]
    simp only [LinearMap.comp_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.id_apply, ContinuousLinearMap.coe_smul,
      LinearMap.smul_apply, map_smul]
    have hpoint : (LinearMap.BilinForm.toDual b hb).symm
        (LinearMap.toContinuousLinearMap.symm (bC.toLinearMap v)) = v := by
      rw [hbv, hΦv, LinearEquiv.symm_apply_apply]
    exact congrArg (fun t ↦ (2 : ℝ) • t) hpoint
  rw [hassemble, map_smul, LinearMap.trace_id, smul_eq_mul]

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Affine functions are harmonic**: the Laplacian of `L y + c`
vanishes. -/
theorem modelLaplacian_affine (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    modelLaplacian b hb (fun y ↦ L y + c) x = 0 := by
  unfold modelLaplacian
  have hdf : fderiv ℝ (fun y ↦ L y + c) = fun _ ↦ L := by
    funext y
    rw [fderiv_add_const]
    exact L.fderiv
  rw [hdf]
  rw [show fderiv ℝ (fun _ : E ↦ L) x = 0 from fderiv_const_apply L]
  simp

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Trace positivity**: the trace of a positive-semidefinite form against a
positive-definite metric is nonnegative — computed in a `b`-orthogonal
basis, where each diagonal coefficient is `H(vᵢ,vᵢ)/b(vᵢ,vᵢ) ≥ 0`.
-/
theorem trace_dual_comp_nonneg (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : ∀ v : E, 0 ≤ H v v) :
    0 ≤ LinearMap.trace ℝ E
      ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          (H.toLinearMap))) := by
  obtain ⟨v, hortho⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := b) hbs
  set L : E →ₗ[ℝ] E :=
    (LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
      (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
        (H.toLinearMap)) with hL
  -- The key pairing identity: `b (L w) u = H w u`.
  have hpair : ∀ w u : E, b (L w) u = H w u := by
    intro w u
    have h1 : LinearMap.toContinuousLinearMap.symm (H.toLinearMap w) =
        ((H w : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) := by
      apply (LinearEquiv.symm_apply_eq _).mpr
      rfl
    have h2 : b ((LinearMap.BilinForm.toDual b hb).symm
        ((H w : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ)) u =
        (((H w : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ)) u := by
      have := LinearEquiv.apply_symm_apply
        (LinearMap.BilinForm.toDual b hb)
        (((H w : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ))
      have h3 := congrArg (fun ψ ↦ ψ u) this
      simpa [LinearMap.BilinForm.toDual_def] using h3
    simp only [hL, LinearMap.comp_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, h1]
    exact h2
  -- Trace as the sum of diagonal coefficients in the orthogonal basis.
  rw [LinearMap.trace_eq_matrix_trace ℝ v, Matrix.trace]
  apply Finset.sum_nonneg
  intro i _
  -- The diagonal entry is `H vᵢ vᵢ / b vᵢ vᵢ`.
  have hvi : v i ≠ 0 := v.ne_zero i
  have hbvi : 0 < b (v i) (v i) := hbpos (v i) hvi
  -- Extract the coefficient by pairing with `v i`.
  have hexpand : b (L (v i)) (v i) =
      (LinearMap.toMatrix v v L i i) * b (v i) (v i) := by
    conv_lhs => rw [← v.sum_repr (L (v i))]
    have hsum : b (∑ j, v.repr (L (v i)) j • v j) (v i) =
        ∑ j, v.repr (L (v i)) j * b (v j) (v i) := by
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      simp [smul_eq_mul]
    rw [hsum]
    rw [Finset.sum_eq_single i]
    · rw [LinearMap.toMatrix_apply]
    · intro j _ hji
      rw [hortho hji]
      ring
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hHvi := hH (v i)
  rw [hpair] at hexpand
  have : LinearMap.toMatrix v v L i i =
      H (v i) (v i) / b (v i) (v i) := by
    field_simp at hexpand ⊢
    linarith
  rw [Matrix.diag_apply, this]
  positivity

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The Laplacian is nonnegative at a local minimum** — the spatial maximum
principle, fusing the second-derivative test with trace positivity. This
is the mechanism by which spatial minima of evolving geometric quantities
obey the scalar ODE comparisons: the heart of the parabolic maximum
principle.
-/
theorem modelLaplacian_nonneg_of_isLocalMin
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E}
    (hmin : IsLocalMin f x₀) :
    0 ≤ modelLaplacian b hb f x₀ :=
  trace_dual_comp_nonneg b hb hbs hbpos
    (fderiv ℝ (fderiv ℝ f) x₀)
    (fun v ↦ hessian_nonneg_of_isLocalMin hf hmin v)

end RicciFlow
