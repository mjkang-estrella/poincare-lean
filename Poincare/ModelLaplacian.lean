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
import Poincare.ModelChristoffel
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.Chebyshev

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

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Hamilton's touching-point inequality**: at a spatial local minimum with
value zero, a reaction–diffusion supersolution has nonnegative time
derivative — the single inequality at the heart of the parabolic maximum
principle, glued from the spatial sign of the Laplacian.
-/
theorem touching_point_nonneg (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E}
    (hmin : IsLocalMin f x₀) (hval : f x₀ = 0) {ut' c : ℝ}
    (hsuper : modelLaplacian b hb f x₀ + c * f x₀ ≤ ut') : 0 ≤ ut' := by
  have hlap := modelLaplacian_nonneg_of_isLocalMin b hb hbs hbpos hf hmin
  rw [hval] at hsuper
  linarith

end RicciFlow

namespace RicciFlow

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The parabolic maximum principle on a compact domain** (strict
supersolutions): a quantity strictly positive at time `0`, evolving by a
strict reaction–diffusion supersolution inequality whose spatial minima
over the compact `K` are interior, stays strictly positive on `[0, T]`.
The proof tracks the spatial minimum to its first zero, where the
left-derivative is nonpositive while the strict supersolution inequality
and the spatial sign of the Laplacian force it positive.
-/
theorem parabolic_min_principle_strict
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {u u' : ℝ → E → ℝ} {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {T c : ℝ}
    (hu_cont : Continuous ↿u)
    (hud : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u t))
    (hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (u t) x + c * u t x < u' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (u t) K x → IsLocalMin (u t) x)
    (h0 : ∀ x ∈ K, 0 < u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, 0 < u t x := by
  by_contra hviol
  push_neg at hviol
  obtain ⟨t₁, ht₁, x₁, hx₁, hux₁⟩ := hviol
  -- The evolving spatial minimum.
  set m : ℝ → ℝ := fun t ↦ sInf (u t '' K) with hm
  have hmcont : Continuous m := hK.continuous_sInf hu_cont
  have hattain : ∀ t, ∃ x ∈ K, IsMinOn (u t) K x ∧ m t = u t x := by
    intro t
    obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hKne
      ((hu_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    refine ⟨x, hxK, hxmin, ?_⟩
    apply le_antisymm
    · exact csInf_le ⟨u t x, fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz⟩
        ⟨x, hxK, rfl⟩
    · exact le_csInf ((hKne.image (u t))) fun y ⟨z, hz, hzy⟩ ↦
        hzy ▸ hxmin hz
  have hmle : ∀ t (x : E), x ∈ K → m t ≤ u t x := by
    intro t x hx
    exact csInf_le ⟨m t, fun y ⟨z, hz, hzy⟩ ↦ by
      obtain ⟨x', hx', hmin', hmx'⟩ := hattain t
      rw [← hzy, hmx']
      exact hmin' hz⟩ ⟨x, hx, rfl⟩
  -- Initial positivity and the violation, at the level of `m`.
  have hm0 : 0 < m 0 := by
    obtain ⟨x, hxK, _, hmx⟩ := hattain 0
    rw [hmx]
    exact h0 x hxK
  have hmbad : ∃ t ∈ Icc (0 : ℝ) T, m t ≤ 0 :=
    ⟨t₁, ht₁, le_trans (hmle t₁ x₁ hx₁) hux₁⟩
  -- The first crossing of the minimum.
  obtain ⟨t₀, ht₀, hmt₀, hbefore⟩ :=
    exists_first_zero (hmcont.continuousOn) hm0 hmbad
  have ht₀Icc : t₀ ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht₀.1, ht₀.2⟩
  obtain ⟨x₀, hx₀K, hx₀min, hmx₀⟩ := hattain t₀
  have hux₀ : u t₀ x₀ = 0 := by rw [← hmx₀, hmt₀]
  -- Left-nonpositivity of the time derivative at the touching point.
  have hder := hud x₀ hx₀K t₀ ht₀Icc
  have hleft : u' t₀ x₀ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hslope := hasDerivAt_iff_tendsto_slope.mp hder
    have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ,
        0 < slope (fun s ↦ u s x₀) t₀ s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hlt : ∀ᶠ s in nhdsWithin t₀ (Iio t₀),
        0 < slope (fun s ↦ u s x₀) t₀ s := by
      apply hev.filter_mono
      apply nhdsWithin_mono
      intro s hs
      exact ne_of_lt hs
    have hIoo : ∀ᶠ s in nhdsWithin t₀ (Iio t₀), s ∈ Ioo (0 : ℝ) t₀ :=
      Filter.eventually_of_mem (Ioo_mem_nhdsLT ht₀.1) fun s hs ↦ hs
    obtain ⟨s, hsl, hsIoo⟩ := (hlt.and hIoo).exists
    have hneg : u s x₀ < 0 := by
      have hde : slope (fun s ↦ u s x₀) t₀ s =
          (u s x₀ - u t₀ x₀) / (s - t₀) := by
        rw [slope_def_field]
      rw [hde, hux₀, sub_zero] at hsl
      have hst : s - t₀ < 0 := by linarith [hsIoo.2]
      by_contra hge
      push_neg at hge
      have : u s x₀ / (s - t₀) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hge
        (le_of_lt hst)
      linarith
    have hmpos := hbefore s ⟨le_of_lt hsIoo.1, hsIoo.2⟩
    have := hmle s x₀ hx₀K
    linarith
  -- The strict supersolution inequality forces positivity instead.
  have hloc := hmin_int t₀ ht₀Icc x₀ hx₀K hx₀min
  have hsup := hsuper t₀ ht₀Icc x₀ hx₀K
  have hlap := modelLaplacian_nonneg_of_isLocalMin b hb hbs hbpos
    (hspace t₀ ht₀Icc) hloc
  rw [hux₀] at hsup
  linarith

end RicciFlow

namespace RicciFlow

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Adding a constant does not change the Laplacian. -/
theorem modelLaplacian_add_const (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (f : E → ℝ) (k : ℝ) (x : E) :
    modelLaplacian b hb (fun y ↦ f y + k) x = modelLaplacian b hb f x := by
  unfold modelLaplacian
  congr 2
  have : fderiv ℝ (fun y ↦ f y + k) = fderiv ℝ f := by
    funext y
    exact fderiv_add_const k
  rw [this]

/--
**The parabolic maximum principle** (non-strict form): a quantity
nonnegative at time `0`, evolving by a reaction–diffusion supersolution
inequality with interior compact spatial minima, stays nonnegative — by
`ε`-perturbation with an exponential slack reducing to the strict
principle.
-/
theorem parabolic_min_principle
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {u u' : ℝ → E → ℝ} {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {T c : ℝ}
    (hu_cont : Continuous ↿u)
    (hud : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u t))
    (hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (u t) x + c * u t x ≤ u' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (u t) K x → IsLocalMin (u t) x)
    (h0 : ∀ x ∈ K, 0 ≤ u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, 0 ≤ u t x := by
  intro t ht x hx
  -- It suffices to dominate `-ε e^{Mt}` for every `ε > 0`.
  set M : ℝ := |c| + 1 with hM
  by_contra hneg
  push_neg at hneg
  set ε : ℝ := -u t x / (2 * Real.exp (M * t)) with hε
  have hexp : (0 : ℝ) < Real.exp (M * t) := Real.exp_pos _
  have hεpos : 0 < ε := by
    rw [hε]
    apply div_pos (by linarith) (by positivity)
  -- The perturbed quantity is a strict supersolution, positive at `0`.
  set v : ℝ → E → ℝ := fun s y ↦ u s y + ε * Real.exp (M * s) with hv
  set v' : ℝ → E → ℝ := fun s y ↦ u' s y + ε * M * Real.exp (M * s)
    with hv'
  have hvpos := parabolic_min_principle_strict b hb hbs hbpos
    (u := v) (u' := v') hK hKne (T := T) (c := c)
    (by
      apply Continuous.add hu_cont
      exact (continuous_const.mul ((continuous_const.mul
        continuous_fst).rexp)).comp (continuous_id))
    (by
      intro y hy s hs
      have h1 := hud y hy s hs
      have h2 : HasDerivAt (fun r ↦ ε * Real.exp (M * r))
          (ε * M * Real.exp (M * s)) s := by
        have h3 := (((hasDerivAt_id s).const_mul M).exp).const_mul ε
        simp only [id_eq] at h3
        convert h3 using 1
        ring
      simpa [hv, hv'] using h1.add h2)
    (by
      intro s hs
      exact (hspace s hs).add contDiff_const)
    (by
      intro s hs y hy
      have hsup := hsuper s hs y hy
      have hlap : modelLaplacian b hb (v s) y =
          modelLaplacian b hb (u s) y :=
        modelLaplacian_add_const b hb (u s) _ y
      simp only [hv, hv']
      rw [hlap]
      have hcM : c < M := by
        rw [hM]
        rcases le_or_gt 0 c with h | h
        · rw [abs_of_nonneg h]; linarith
        · rw [abs_of_neg h]; linarith
      have heps : 0 < ε * Real.exp (M * s) := by positivity
      have hkey : c * (ε * Real.exp (M * s)) <
          ε * M * Real.exp (M * s) := by
        have h2 : c * (ε * Real.exp (M * s)) <
            M * (ε * Real.exp (M * s)) :=
          mul_lt_mul_of_pos_right hcM heps
        nlinarith
      nlinarith)
    (by
      intro s hs y hy
      intro hminv
      have hminu : IsMinOn (u s) K y := by
        intro z hz
        have := hminv hz
        simp only [hv] at this
        simpa using this
      have hloc := hmin_int s hs y hy hminu
      have : IsLocalMin (fun z ↦ u s z + ε * Real.exp (M * s)) y :=
        hloc.add isMinFilter_const
      simpa [hv] using this)
    (by
      intro y hy
      simp only [hv]
      have := h0 y hy
      positivity)
  -- Contradiction at `(t, x)`.
  have := hvpos t ht x hx
  simp only [hv] at this
  rw [hε] at this
  have hne : Real.exp (M * t) ≠ 0 := ne_of_gt hexp
  field_simp at this
  linarith
end RicciFlow

namespace RicciFlow

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Preserved nonnegativity in flow form**: any quantity satisfying a
heat-type evolution inequality `∂R/∂t ≥ ΔR` (as the scalar curvature does
under the Ricci flow, where `∂R/∂t = ΔR + 2|Ric|² ≥ ΔR`) with nonnegative
initial data stays nonnegative. Hamilton's "nonnegative scalar curvature
is preserved", modulo the evolution equation itself.
-/
theorem heat_supersolution_nonneg_preserved
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {R R' : ℝ → E → ℝ} {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {T : ℝ}
    (hR_cont : Continuous ↿R)
    (hRd : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (R t))
    (hevol : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (R t) x ≤ R' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (R t) K x → IsLocalMin (R t) x)
    (h0 : ∀ x ∈ K, 0 ≤ R 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, 0 ≤ R t x := by
  apply parabolic_min_principle b hb hbs hbpos hK hKne hR_cont hRd hspace
    (c := 0) ?_ hmin_int h0
  intro t ht x hx
  have := hevol t ht x hx
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The curved Laplacian of a constant metric is the flat Laplacian**: the
Christoffel corrector vanishes and the covariant Hessian collapses to the
flat second derivative — anchoring the Laplace–Beltrami operator to the
analytic stratum.
-/
theorem curvedLaplacian_const (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate) (f : E → ℝ) (x : E) :
    curvedLaplacian (fun _ ↦ G₀) b hb f x =
      modelLaplacian (b x) (hb x) f x := by
  unfold curvedLaplacian modelLaplacian
  congr 1
  apply LinearMap.ext
  intro v
  show (LinearMap.BilinForm.toDual (b x) (hb x)).symm _ =
    (LinearMap.BilinForm.toDual (b x) (hb x)).symm _
  apply congrArg
  apply LinearMap.ext
  intro w
  have hΓ : christoffelAt (fun _ : E ↦ G₀) x (b x) (hb x) v w = 0 :=
    christoffelAt_const G₀ x (b x) (hb x) v w
  simp only [covariantHessianLin, LinearMap.mk₂_apply, covariantHessian,
    hΓ, map_zero, sub_zero, LinearMap.comp_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe]
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The curved Laplacian is additive on `C²` functions. -/
theorem curvedLaplacian_add (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {f g : E → ℝ} {x : E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    curvedLaplacian G b hb (f + g) x =
      curvedLaplacian G b hb f x + curvedLaplacian G b hb g x := by
  unfold curvedLaplacian
  rw [← map_add, ← LinearMap.comp_add]
  congr 2
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  have hdf : fderiv ℝ (f + g) = fun y ↦ fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_add ((hf.differentiable (by norm_num)) y)
      ((hg.differentiable (by norm_num)) y)
  have hd2 : fderiv ℝ (fderiv ℝ (f + g)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    rw [hdf]
    exact fderiv_add
      (((hf.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)) x)
      (((hg.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)) x)
  simp only [covariantHessianLin, LinearMap.mk₂_apply, covariantHessian,
    LinearMap.add_apply, hd2, ContinuousLinearMap.add_apply]
  have hdfx : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x := by
    rw [hdf]
  rw [hdfx]
  simp only [ContinuousLinearMap.add_apply]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The curved Laplacian is homogeneous on `C²` functions. -/
theorem curvedLaplacian_smul (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {f : E → ℝ} {x : E} (c : ℝ) (hf : ContDiff ℝ 2 f) :
    curvedLaplacian G b hb (fun y ↦ c * f y) x =
      c * curvedLaplacian G b hb f x := by
  unfold curvedLaplacian
  rw [← smul_eq_mul, ← map_smul, ← LinearMap.comp_smul]
  congr 2
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  have hdf : fderiv ℝ (fun y ↦ c * f y) = fun y ↦ c • fderiv ℝ f y := by
    funext y
    exact fderiv_const_mul ((hf.differentiable (by norm_num)) y) c
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ c * f y)) x =
      c • fderiv ℝ (fderiv ℝ f) x := by
    rw [hdf]
    rw [show (fun y ↦ c • fderiv ℝ f y) = fun y ↦ c • (fderiv ℝ f) y
      from rfl]
    exact fderiv_const_smul
      (((hf.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)) x) c
  simp only [covariantHessianLin, LinearMap.mk₂_apply, covariantHessian,
    LinearMap.smul_apply, hd2, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  have hdfx : fderiv ℝ (fun y ↦ c * f y) x = c • fderiv ℝ f x := by
    rw [hdf]
  rw [hdfx]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Constant functions are harmonic for the curved Laplacian. -/
theorem curvedLaplacian_const_fn (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate) (k : ℝ) (x : E) :
    curvedLaplacian G b hb (fun _ ↦ k) x = 0 := by
  unfold curvedLaplacian
  have hzero : covariantHessianLin G b hb (fun _ ↦ k) x = 0 := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    simp only [covariantHessianLin, LinearMap.mk₂_apply, covariantHessian,
      LinearMap.zero_apply]
    rw [fderiv_fun_const]
    simp [fderiv_zero]
  rw [hzero]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The metric gradient: the dual of the differential. -/
noncomputable def metricGradient (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (f : E → ℝ) (x : E) : E :=
  (LinearMap.BilinForm.toDual b hb).symm
    (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))

/-- **Defining property of the gradient**: `b (∇f) v = Df(v)`. -/
theorem b_metricGradient (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (f : E → ℝ) (x : E) (v : E) :
    b (metricGradient b hb f x) v = fderiv ℝ f x v := by
  unfold metricGradient
  have h := LinearEquiv.apply_symm_apply
    (LinearMap.BilinForm.toDual b hb)
    (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))
  have h2 := congrArg (fun ψ ↦ ψ v) h
  simpa [LinearMap.BilinForm.toDual_def] using h2

/-- The gradient vanishes exactly where the differential does; in
particular it vanishes at local extrema of differentiable functions. -/
theorem metricGradient_eq_zero_of_isLocalMin (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hmin : IsLocalMin f x) :
    metricGradient b hb f x = 0 := by
  unfold metricGradient
  rw [hmin.fderiv_eq_zero]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The curved Laplacian agrees with the flat one at critical points**: the
corrector term carries a factor of the differential, which vanishes.
-/
theorem curvedLaplacian_eq_modelLaplacian_of_critical
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {f : E → ℝ} {x : E} (hcrit : fderiv ℝ f x = 0) :
    curvedLaplacian G b hb f x = modelLaplacian (b x) (hb x) f x := by
  unfold curvedLaplacian modelLaplacian
  congr 1
  apply LinearMap.ext
  intro v
  show (LinearMap.BilinForm.toDual (b x) (hb x)).symm _ =
    (LinearMap.BilinForm.toDual (b x) (hb x)).symm _
  apply congrArg
  apply LinearMap.ext
  intro w
  simp only [covariantHessianLin, LinearMap.mk₂_apply, covariantHessian,
    hcrit, ContinuousLinearMap.zero_apply, sub_zero,
    LinearMap.comp_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]
  rfl

/--
**The curved spatial maximum principle**: at a local minimum the
Laplace–Beltrami operator is nonnegative — the gradient vanishes, the
corrector dies with it, and the flat spatial maximum principle applies.
The parabolic comparison machinery extends to curved backgrounds.
-/
theorem curvedLaplacian_nonneg_of_isLocalMin
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate) {x : E}
    (hbs : LinearMap.IsSymm (b x))
    (hbpos : ∀ v : E, v ≠ 0 → 0 < (b x) v v)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hmin : IsLocalMin f x) :
    0 ≤ curvedLaplacian G b hb f x := by
  rw [curvedLaplacian_eq_modelLaplacian_of_critical G b hb
    (hmin.fderiv_eq_zero)]
  exact modelLaplacian_nonneg_of_isLocalMin (b x) (hb x) hbs hbpos hf hmin

end RicciFlow

namespace RicciFlow

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The parabolic maximum principle on curved backgrounds** (strict form):
the compact-domain minimum-tracking argument with the Laplace–Beltrami
operator of an arbitrary metric family — the corrector dies at the
touching point, so the flat argument carries over verbatim.
-/
theorem curved_parabolic_min_principle_strict
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    (hbs : ∀ x, LinearMap.IsSymm (b x))
    (hbpos : ∀ x (v : E), v ≠ 0 → 0 < (b x) v v)
    {u u' : ℝ → E → ℝ} {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {T c : ℝ}
    (hu_cont : Continuous ↿u)
    (hud : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u t))
    (hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      curvedLaplacian G b hb (u t) x + c * u t x < u' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (u t) K x → IsLocalMin (u t) x)
    (h0 : ∀ x ∈ K, 0 < u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, 0 < u t x := by
  by_contra hviol
  push_neg at hviol
  obtain ⟨t₁, ht₁, x₁, hx₁, hux₁⟩ := hviol
  set m : ℝ → ℝ := fun t ↦ sInf (u t '' K) with hm
  have hmcont : Continuous m := hK.continuous_sInf hu_cont
  have hattain : ∀ t, ∃ x ∈ K, IsMinOn (u t) K x ∧ m t = u t x := by
    intro t
    obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hKne
      ((hu_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    refine ⟨x, hxK, hxmin, le_antisymm ?_ ?_⟩
    · exact csInf_le ⟨u t x, fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz⟩
        ⟨x, hxK, rfl⟩
    · exact le_csInf ((hKne.image (u t))) fun y ⟨z, hz, hzy⟩ ↦
        hzy ▸ hxmin hz
  have hmle : ∀ t (x : E), x ∈ K → m t ≤ u t x := by
    intro t x hx
    exact csInf_le ⟨m t, fun y ⟨z, hz, hzy⟩ ↦ by
      obtain ⟨x', hx', hmin', hmx'⟩ := hattain t
      rw [← hzy, hmx']
      exact hmin' hz⟩ ⟨x, hx, rfl⟩
  have hm0 : 0 < m 0 := by
    obtain ⟨x, hxK, _, hmx⟩ := hattain 0
    rw [hmx]
    exact h0 x hxK
  have hmbad : ∃ t ∈ Icc (0 : ℝ) T, m t ≤ 0 :=
    ⟨t₁, ht₁, le_trans (hmle t₁ x₁ hx₁) hux₁⟩
  obtain ⟨t₀, ht₀, hmt₀, hbefore⟩ :=
    exists_first_zero (hmcont.continuousOn) hm0 hmbad
  have ht₀Icc : t₀ ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht₀.1, ht₀.2⟩
  obtain ⟨x₀, hx₀K, hx₀min, hmx₀⟩ := hattain t₀
  have hux₀ : u t₀ x₀ = 0 := by rw [← hmx₀, hmt₀]
  have hder := hud x₀ hx₀K t₀ ht₀Icc
  have hleft : u' t₀ x₀ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hslope := hasDerivAt_iff_tendsto_slope.mp hder
    have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ,
        0 < slope (fun s ↦ u s x₀) t₀ s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hlt : ∀ᶠ s in nhdsWithin t₀ (Iio t₀),
        0 < slope (fun s ↦ u s x₀) t₀ s := by
      apply hev.filter_mono
      apply nhdsWithin_mono
      intro s hs
      exact ne_of_lt hs
    have hIoo : ∀ᶠ s in nhdsWithin t₀ (Iio t₀), s ∈ Ioo (0 : ℝ) t₀ :=
      Filter.eventually_of_mem (Ioo_mem_nhdsLT ht₀.1) fun s hs ↦ hs
    obtain ⟨s, hsl, hsIoo⟩ := (hlt.and hIoo).exists
    have hneg : u s x₀ < 0 := by
      have hde : slope (fun s ↦ u s x₀) t₀ s =
          (u s x₀ - u t₀ x₀) / (s - t₀) := by
        rw [slope_def_field]
      rw [hde, hux₀, sub_zero] at hsl
      have hst : s - t₀ < 0 := by linarith [hsIoo.2]
      by_contra hge
      push_neg at hge
      have : u s x₀ / (s - t₀) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hge
        (le_of_lt hst)
      linarith
    have hmpos := hbefore s ⟨le_of_lt hsIoo.1, hsIoo.2⟩
    have := hmle s x₀ hx₀K
    linarith
  -- The touching point: the curved Laplacian is nonnegative there.
  have hloc := hmin_int t₀ ht₀Icc x₀ hx₀K hx₀min
  have hsup := hsuper t₀ ht₀Icc x₀ hx₀K
  have hlap := curvedLaplacian_nonneg_of_isLocalMin G b hb (hbs x₀)
    (hbpos x₀) (hspace t₀ ht₀Icc) hloc
  rw [hux₀] at hsup
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The Laplacian product rule**: `Δ(fg) = f Δg + g Δf + 2 b(∇f, ∇g)` — the
identity underlying every Bochner formula and every integration-by-parts
computation in Perelman's functionals.
-/
theorem modelLaplacian_mul (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    modelLaplacian b hb (fun y ↦ f y * g y) x =
      f x * modelLaplacian b hb g x + g x * modelLaplacian b hb f x
        + 2 * b (metricGradient b hb f x) (metricGradient b hb g x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- First derivative of the product.
  have hd1 : fderiv ℝ (fun y ↦ f y * g y) =
      fun y ↦ f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    funext y
    exact fderiv_mul (hfd y) (hgd y)
  -- Second derivative of the product.
  have hA : fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) x =
      f x • fderiv ℝ (fderiv ℝ g) x
        + (fderiv ℝ f x).smulRight (fderiv ℝ g x) :=
    fderiv_smul (hfd x) (hg1 x)
  have hB : fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) x =
      g x • fderiv ℝ (fderiv ℝ f) x
        + (fderiv ℝ g x).smulRight (fderiv ℝ f x) :=
    fderiv_smul (hgd x) (hf1 x)
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ f y * g y)) x =
      (f x • fderiv ℝ (fderiv ℝ g) x
        + (fderiv ℝ f x).smulRight (fderiv ℝ g x))
      + (g x • fderiv ℝ (fderiv ℝ f) x
        + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
    rw [hd1]
    refine Eq.trans ((((hfd x).smul (hg1 x)).hasFDerivAt.add
      ((hgd x).smul (hf1 x)).hasFDerivAt).fderiv) ?_
    rw [show fderiv ℝ (f • fderiv ℝ g) x =
      fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) x from rfl,
      show fderiv ℝ (g • fderiv ℝ f) x =
      fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) x from rfl, hA, hB]
  -- Rank-one cross terms trace to gradient pairings.
  have hcross : ∀ (φ ψ : E →L[ℝ] ℝ),
      LinearMap.trace ℝ E
        ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
          (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
            ((φ.smulRight ψ).toLinearMap))) =
      φ ((LinearMap.BilinForm.toDual b hb).symm
        (LinearMap.toContinuousLinearMap.symm ψ)) := by
    intro φ ψ
    have hcomp : (LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          ((φ.smulRight ψ).toLinearMap)) =
        LinearMap.smulRight (φ.toLinearMap)
          ((LinearMap.BilinForm.toDual b hb).symm
            (LinearMap.toContinuousLinearMap.symm ψ)) := by
      apply LinearMap.ext
      intro v
      have h1 : (φ.smulRight ψ).toLinearMap v = φ v • ψ := rfl
      simp only [LinearMap.comp_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe]
    rw [hcomp, LinearMap.trace_smulRight]
    rfl
  -- Assemble the four traces.
  unfold modelLaplacian
  rw [hd2]
  simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul,
    LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, map_add, map_smul, smul_eq_mul]
  have hT2 := hcross (fderiv ℝ f x) (fderiv ℝ g x)
  have hT4 := hcross (fderiv ℝ g x) (fderiv ℝ f x)
  rw [hT2, hT4]
  -- Identify the pairings with the gradient inner products.
  have hfg : fderiv ℝ f x ((LinearMap.BilinForm.toDual b hb).symm
      (LinearMap.toContinuousLinearMap.symm (fderiv ℝ g x))) =
      b (metricGradient b hb f x) (metricGradient b hb g x) := by
    rw [← b_metricGradient b hb f x]
    rfl
  have hgf : fderiv ℝ g x ((LinearMap.BilinForm.toDual b hb).symm
      (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) =
      b (metricGradient b hb f x) (metricGradient b hb g x) := by
    rw [← b_metricGradient b hb g x]
    have hsy := hbs.eq (metricGradient b hb g x) (metricGradient b hb f x)
    simp only [RingHom.id_apply] at hsy
    rw [← hsy]
    rfl
  rw [hfg, hgf]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- `Δ(f²) = 2 f Δf + 2 |∇f|²` — the square form of the product rule. -/
theorem modelLaplacian_sq (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    modelLaplacian b hb (fun y ↦ f y * f y) x =
      2 * f x * modelLaplacian b hb f x
        + 2 * b (metricGradient b hb f x) (metricGradient b hb f x) := by
  rw [modelLaplacian_mul b hb hbs hf hf x]
  ring

/-- The gradient's squared length is nonnegative for a positive-definite
metric. -/
theorem gradient_sq_nonneg (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v) (f : E → ℝ) (x : E) :
    0 ≤ b (metricGradient b hb f x) (metricGradient b hb f x) := by
  by_cases hzero : metricGradient b hb f x = 0
  · rw [hzero]
    simp
  · exact le_of_lt (hbpos _ hzero)

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The curved Laplacian product rule**: the corrector term distributes over
the product through the differential, so the Bochner identity
`Δ(fg) = fΔg + gΔf + 2b(∇f,∇g)` holds verbatim for the Laplace–Beltrami
operator of any metric.
-/
theorem curvedLaplacian_mul (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {x : E} (hbs : LinearMap.IsSymm (b x))
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    curvedLaplacian G b hb (fun y ↦ f y * g y) x =
      f x * curvedLaplacian G b hb g x
        + g x * curvedLaplacian G b hb f x
        + 2 * (b x) (metricGradient (b x) (hb x) f x)
            (metricGradient (b x) (hb x) g x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- The Hessian of the product decomposes.
  have hA : fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) x =
      f x • fderiv ℝ (fderiv ℝ g) x
        + (fderiv ℝ f x).smulRight (fderiv ℝ g x) :=
    fderiv_smul (hfd x) (hg1 x)
  have hB : fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) x =
      g x • fderiv ℝ (fderiv ℝ f) x
        + (fderiv ℝ g x).smulRight (fderiv ℝ f x) :=
    fderiv_smul (hgd x) (hf1 x)
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ f y * g y)) x =
      (f x • fderiv ℝ (fderiv ℝ g) x
        + (fderiv ℝ f x).smulRight (fderiv ℝ g x))
      + (g x • fderiv ℝ (fderiv ℝ f) x
        + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
    rw [show fderiv ℝ (fun y ↦ f y * g y) =
      fun y ↦ f y • fderiv ℝ g y + g y • fderiv ℝ f y from
      funext fun y ↦ fderiv_mul (hfd y) (hgd y)]
    refine Eq.trans ((((hfd x).smul (hg1 x)).hasFDerivAt.add
      ((hgd x).smul (hf1 x)).hasFDerivAt).fderiv) ?_
    rw [show fderiv ℝ (f • fderiv ℝ g) x =
      fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) x from rfl,
      show fderiv ℝ (g • fderiv ℝ f) x =
      fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) x from rfl, hA, hB]
  -- The covariant Hessian decomposition.
  have hHess : covariantHessianLin G b hb (fun y ↦ f y * g y) x =
      f x • covariantHessianLin G b hb g x
        + g x • covariantHessianLin G b hb f x
        + ((fderiv ℝ f x : E →ₗ[ℝ] ℝ).smulRight
            (LinearMap.toContinuousLinearMap.symm (fderiv ℝ g x))
          + (fderiv ℝ g x : E →ₗ[ℝ] ℝ).smulRight
            (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    have hdmul : fderiv ℝ (fun y ↦ f y * g y) x =
        f x • fderiv ℝ g x + g x • fderiv ℝ f x := fderiv_mul (hfd x) (hgd x)
    simp only [covariantHessianLin, LinearMap.mk₂_apply, covariantHessian,
      hd2, hdmul, LinearMap.add_apply, LinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply,
      smul_eq_mul]
    have hcoe : ∀ (φ : E →L[ℝ] ℝ) (u : E),
        (LinearMap.toContinuousLinearMap.symm φ : E →ₗ[ℝ] ℝ) u = φ u :=
      fun φ u ↦ rfl
    rw [hcoe, hcoe]
    simp only [ContinuousLinearMap.coe_coe]
    ring
  -- Trace the decomposition.
  unfold curvedLaplacian
  rw [hHess]
  simp only [LinearMap.comp_add, LinearMap.comp_smul, map_add, map_smul,
    smul_eq_mul]
  -- The rank-one traces are the gradient pairings.
  have hrank : ∀ (φ ψ : E →L[ℝ] ℝ),
      LinearMap.trace ℝ E
        ((LinearMap.BilinForm.toDual (b x) (hb x)).symm.toLinearMap ∘ₗ
          ((φ : E →ₗ[ℝ] ℝ).smulRight
            (LinearMap.toContinuousLinearMap.symm ψ))) =
      φ ((LinearMap.BilinForm.toDual (b x) (hb x)).symm
        (LinearMap.toContinuousLinearMap.symm ψ)) := by
    intro φ ψ
    have hcomp : (LinearMap.BilinForm.toDual (b x) (hb x)).symm.toLinearMap
        ∘ₗ ((φ : E →ₗ[ℝ] ℝ).smulRight
          (LinearMap.toContinuousLinearMap.symm ψ)) =
        LinearMap.smulRight (φ : E →ₗ[ℝ] ℝ)
          ((LinearMap.BilinForm.toDual (b x) (hb x)).symm
            (LinearMap.toContinuousLinearMap.symm ψ)) := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.smulRight_apply, map_smul,
        ContinuousLinearMap.coe_coe]
    rw [hcomp, LinearMap.trace_smulRight]
    rfl
  rw [hrank, hrank]
  have hfg : fderiv ℝ f x ((LinearMap.BilinForm.toDual (b x)
      (hb x)).symm (LinearMap.toContinuousLinearMap.symm
        (fderiv ℝ g x))) =
      (b x) (metricGradient (b x) (hb x) f x)
        (metricGradient (b x) (hb x) g x) := by
    rw [← b_metricGradient (b x) (hb x) f x]
    rfl
  have hgf : fderiv ℝ g x ((LinearMap.BilinForm.toDual (b x)
      (hb x)).symm (LinearMap.toContinuousLinearMap.symm
        (fderiv ℝ f x))) =
      (b x) (metricGradient (b x) (hb x) f x)
        (metricGradient (b x) (hb x) g x) := by
    rw [← b_metricGradient (b x) (hb x) g x]
    have hsy := hbs.eq (metricGradient (b x) (hb x) g x)
      (metricGradient (b x) (hb x) f x)
    simp only [RingHom.id_apply] at hsy
    rw [← hsy]
    rfl
  rw [hfg, hgf]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The Laplacian chain rule**: `Δ(φ∘f) = φ'(f) Δf + φ''(f) |∇f|²` — the
identity behind every logarithmic-derivative computation in Perelman's
entropy functionals.
-/
theorem modelLaplacian_comp (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) :
    modelLaplacian b hb (fun y ↦ φ (f y)) x =
      deriv φ (f x) * modelLaplacian b hb f x
        + deriv (deriv φ) (f x)
          * b (metricGradient b hb f x) (metricGradient b hb f x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hφ1 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  -- The scalar chain identity for first derivatives.
  have hchain : ∀ (ψ : ℝ → ℝ), Differentiable ℝ ψ → ∀ y : E,
      fderiv ℝ (fun z ↦ ψ (f z)) y = deriv ψ (f y) • fderiv ℝ f y := by
    intro ψ hψ y
    rw [show (fun z ↦ ψ (f z)) = ψ ∘ f from rfl,
      fderiv_comp y (hψ (f y)) (hfd y)]
    ext v
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show fderiv ℝ ψ (f y) (fderiv ℝ f y v) =
      (fderiv ℝ f y v) • deriv ψ (f y) from by
        rw [← fderiv_deriv]
        simp [mul_comm]]
    simp [smul_eq_mul, mul_comm]
  have hd1 := hchain φ hφd
  -- Second derivative.
  have hcdiff : DifferentiableAt ℝ (fun y ↦ deriv φ (f y)) x :=
    (hφ1 (f x)).comp x (hfd x)
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ φ (f y))) x =
      deriv φ (f x) • fderiv ℝ (fderiv ℝ f) x
        + (deriv (deriv φ) (f x) • fderiv ℝ f x).smulRight
          (fderiv ℝ f x) := by
    rw [show fderiv ℝ (fun y ↦ φ (f y)) =
      fun y ↦ deriv φ (f y) • fderiv ℝ f y from funext hd1]
    refine Eq.trans (fderiv_smul hcdiff (hf1 x)) ?_
    congr 1
    rw [show fderiv ℝ (fun y ↦ deriv φ (f y)) x =
      deriv (deriv φ) (f x) • fderiv ℝ f x from hchain (deriv φ) hφ1 x]
  -- Trace the decomposition.
  unfold modelLaplacian
  rw [hd2]
  have hsm : ((deriv (deriv φ) (f x) • fderiv ℝ f x).smulRight
      (fderiv ℝ f x)) = deriv (deriv φ) (f x) •
        ((fderiv ℝ f x).smulRight (fderiv ℝ f x)) := by
    ext v
    simp [ContinuousLinearMap.smulRight_apply, smul_smul, mul_comm]
  rw [hsm]
  simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul,
    LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, map_add, map_smul, smul_eq_mul]
  -- The rank-one trace is the gradient pairing.
  have hcross : LinearMap.trace ℝ E
      ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          (((fderiv ℝ f x).smulRight (fderiv ℝ f x)).toLinearMap))) =
      fderiv ℝ f x ((LinearMap.BilinForm.toDual b hb).symm
        (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) := by
    have hcomp : (LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          (((fderiv ℝ f x).smulRight (fderiv ℝ f x)).toLinearMap)) =
        LinearMap.smulRight ((fderiv ℝ f x : E →ₗ[ℝ] ℝ))
          ((LinearMap.BilinForm.toDual b hb).symm
            (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) := by
      apply LinearMap.ext
      intro v
      have h1 : ((fderiv ℝ f x).smulRight (fderiv ℝ f x)).toLinearMap v =
          fderiv ℝ f x v • fderiv ℝ f x := rfl
      simp only [LinearMap.comp_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe]
    rw [hcomp, LinearMap.trace_smulRight]
    rfl
  rw [hcross]
  have hpair : fderiv ℝ f x ((LinearMap.BilinForm.toDual b hb).symm
      (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) =
      b (metricGradient b hb f x) (metricGradient b hb f x) := by
    rw [← b_metricGradient b hb f x]
    rfl
  rw [hpair]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The `L²` inequality `Δ(f²) ≥ 2 f Δf` for positive-definite metrics. -/
theorem modelLaplacian_sq_ge (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    2 * f x * modelLaplacian b hb f x ≤
      modelLaplacian b hb (fun y ↦ f y * f y) x := by
  rw [modelLaplacian_sq b hb hbs hf x]
  have := gradient_sq_nonneg b hb hbpos f x
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The square form of the curved product rule. -/
theorem curvedLaplacian_sq (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate) {x : E}
    (hbs : LinearMap.IsSymm (b x))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    curvedLaplacian G b hb (fun y ↦ f y * f y) x =
      2 * f x * curvedLaplacian G b hb f x
        + 2 * (b x) (metricGradient (b x) (hb x) f x)
            (metricGradient (b x) (hb x) f x) := by
  rw [curvedLaplacian_mul G b hb hbs hf hf]
  ring

/-- The `L²` inequality for the Laplace–Beltrami operator. -/
theorem curvedLaplacian_sq_ge (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate) {x : E}
    (hbs : LinearMap.IsSymm (b x))
    (hbpos : ∀ v : E, v ≠ 0 → 0 < (b x) v v)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    2 * f x * curvedLaplacian G b hb f x ≤
      curvedLaplacian G b hb (fun y ↦ f y * f y) x := by
  rw [curvedLaplacian_sq G b hb hbs hf]
  have := gradient_sq_nonneg (b x) (hb x) hbpos f x
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The local Laplacian chain rule**: `Δ(φ∘f) = φ'(f) Δf + φ''(f) |∇f|²`
with `φ` only `C²` near the value `f x` — the form usable for `log` and
other partially defined outer functions in entropy computations.
-/
theorem modelLaplacian_comp_at (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {φ : ℝ → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ (f x)) :
    modelLaplacian b hb (fun y ↦ φ (f y)) x =
      deriv φ (f x) * modelLaplacian b hb f x
        + deriv (deriv φ) (f x)
          * b (metricGradient b hb f x) (metricGradient b hb f x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- `φ` is `C²` on a neighbourhood of `f x`; pull back along `f`.
  obtain ⟨u, hu, hφu⟩ := hφ.contDiffOn (m := 2) le_rfl (by norm_num)
  have huf : ∀ᶠ y in nhds x, f y ∈ interior u :=
    (hfd x).continuousAt.preimage_mem_nhds (interior_mem_nhds.mpr hu)
  have hφd : ∀ᶠ y in nhds x, DifferentiableAt ℝ φ (f y) := by
    filter_upwards [huf] with y hy
    exact ((hφu.mono interior_subset (f y) hy).contDiffAt
      (isOpen_interior.mem_nhds hy)).differentiableAt (by norm_num)
  -- The chain identity holds near `x`.
  have hd1ev : (fun y ↦ fderiv ℝ (fun z ↦ φ (f z)) y) =ᶠ[nhds x]
      fun y ↦ deriv φ (f y) • fderiv ℝ f y := by
    filter_upwards [hφd] with y hy
    rw [show (fun z ↦ φ (f z)) = φ ∘ f from rfl,
      fderiv_comp y hy (hfd y)]
    ext v
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show fderiv ℝ φ (f y) (fderiv ℝ f y v) =
      (fderiv ℝ f y v) • deriv φ (f y) from by
        rw [← fderiv_deriv]
        simp [mul_comm]]
    simp [smul_eq_mul, mul_comm]
  -- Local regularity of `deriv φ` near `f x`.
  have hφint : ContDiffOn ℝ 2 φ (interior u) :=
    hφu.mono interior_subset
  have hfx_int : f x ∈ interior u := huf.self_of_nhds
  have hderiv1 : ContDiffOn ℝ 1 (deriv φ) (interior u) :=
    hφint.deriv_of_isOpen isOpen_interior (by norm_num)
  have hφ1At : DifferentiableAt ℝ (deriv φ) (f x) :=
    ((hderiv1 (f x) hfx_int).contDiffAt
      (isOpen_interior.mem_nhds hfx_int)).differentiableAt one_ne_zero
  have hφdAt : ∀ᶠ y in nhds x, DifferentiableAt ℝ φ (f y) := hφd
  -- Second derivative at `x` through the eventual chain identity.
  have hcdiff : DifferentiableAt ℝ (fun y ↦ deriv φ (f y)) x :=
    hφ1At.comp x (hfd x)
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ φ (f y))) x =
      deriv φ (f x) • fderiv ℝ (fderiv ℝ f) x
        + (deriv (deriv φ) (f x) • fderiv ℝ f x).smulRight
          (fderiv ℝ f x) := by
    rw [hd1ev.fderiv_eq]
    refine Eq.trans (fderiv_smul hcdiff (hf1 x)) ?_
    have hfc : fderiv ℝ (fun z ↦ deriv φ (f z)) x =
        deriv (deriv φ) (f x) • fderiv ℝ f x := by
      rw [show (fun z ↦ deriv φ (f z)) = deriv φ ∘ f from rfl,
        fderiv_comp x hφ1At (hfd x)]
      ext v
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show fderiv ℝ (deriv φ) (f x) (fderiv ℝ f x v) =
        (fderiv ℝ f x v) • deriv (deriv φ) (f x) from by
          rw [← fderiv_deriv]
          simp [mul_comm]]
      simp [smul_eq_mul, mul_comm]
    rw [hfc]
  -- Trace as in the global chain rule.
  unfold modelLaplacian
  rw [hd2]
  have hsm : ((deriv (deriv φ) (f x) • fderiv ℝ f x).smulRight
      (fderiv ℝ f x)) = deriv (deriv φ) (f x) •
        ((fderiv ℝ f x).smulRight (fderiv ℝ f x)) := by
    ext v
    simp [ContinuousLinearMap.smulRight_apply, smul_smul, mul_comm]
  rw [hsm]
  simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul,
    LinearMap.comp_add, LinearMap.comp_smul, map_add, map_smul,
    smul_eq_mul]
  have hcross : LinearMap.trace ℝ E
      ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          (((fderiv ℝ f x).smulRight (fderiv ℝ f x)).toLinearMap))) =
      fderiv ℝ f x ((LinearMap.BilinForm.toDual b hb).symm
        (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) := by
    have hcomp : (LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          (((fderiv ℝ f x).smulRight (fderiv ℝ f x)).toLinearMap)) =
        LinearMap.smulRight ((fderiv ℝ f x : E →ₗ[ℝ] ℝ))
          ((LinearMap.BilinForm.toDual b hb).symm
            (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) := by
      apply LinearMap.ext
      intro v
      have h1 : ((fderiv ℝ f x).smulRight (fderiv ℝ f x)).toLinearMap v =
          fderiv ℝ f x v • fderiv ℝ f x := rfl
      simp only [LinearMap.comp_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe]
    rw [hcomp, LinearMap.trace_smulRight]
    rfl
  rw [hcross]
  have hpair : fderiv ℝ f x ((LinearMap.BilinForm.toDual b hb).symm
      (LinearMap.toContinuousLinearMap.symm (fderiv ℝ f x))) =
      b (metricGradient b hb f x) (metricGradient b hb f x) := by
    rw [← b_metricGradient b hb f x]
    rfl
  rw [hpair]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The logarithmic Laplacian identity**:
`Δ(log f) = Δf/f − |∇f|²/f²` for positive `f` — the identity in which
Perelman's `𝓕`-functional and the conjugate heat equation are computed.
-/
theorem modelLaplacian_log (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x : E} (hpos : 0 < f x) :
    modelLaplacian b hb (fun y ↦ Real.log (f y)) x =
      modelLaplacian b hb f x / f x
        - b (metricGradient b hb f x) (metricGradient b hb f x)
          / (f x) ^ 2 := by
  rw [modelLaplacian_comp_at b hb hf
    ((Real.contDiffAt_log (n := 2)).mpr (ne_of_gt hpos))]
  rw [Real.deriv_log, Real.deriv_log', deriv_inv]
  field_simp
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The exponential Laplacian identity**:
`Δ(e^f) = e^f (Δf + |∇f|²)` — the conjugate-heat-equation side of the
logarithmic identity.
-/
theorem modelLaplacian_exp (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    modelLaplacian b hb (fun y ↦ Real.exp (f y)) x =
      Real.exp (f x) * (modelLaplacian b hb f x
        + b (metricGradient b hb f x) (metricGradient b hb f x)) := by
  rw [modelLaplacian_comp b hb hf (Real.contDiff_exp.of_le le_top) x]
  rw [Real.deriv_exp]
  rw [Real.deriv_exp]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The heat equation `∂u/∂t = Δu` at a point of space-time. -/
def IsHeatSolutionAt (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (u : ℝ → E → ℝ) (t : ℝ) (x : E) : Prop :=
  HasDerivAt (fun s ↦ u s x) (modelLaplacian b hb (u t) x) t

/--
**The fundamental quadratic solution**: `u(t,x) = b(x,x) + 2nt` solves the
heat equation exactly — the canonical anchor of the heat stratum, with
`Δ` of the quadratic form supplying the constant source.
-/
theorem quadratic_heat_solution (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : ∀ v w : E, b v w = b w v)
    (t : ℝ) (x : E) :
    IsHeatSolutionAt b hb
      (fun s y ↦ b y y + 2 * Module.finrank ℝ E * s) t x := by
  unfold IsHeatSolutionAt
  have hlap : modelLaplacian b hb
      (fun y ↦ b y y + 2 * Module.finrank ℝ E * t) x =
      2 * Module.finrank ℝ E := by
    have hshift : modelLaplacian b hb
        (fun y ↦ b y y + 2 * Module.finrank ℝ E * t) x =
        modelLaplacian b hb (fun y ↦ b y y) x := by
      unfold modelLaplacian
      congr 2
      have : fderiv ℝ (fun y ↦ b y y + 2 * Module.finrank ℝ E * t) =
          fderiv ℝ (fun y ↦ b y y) := by
        funext y
        exact fderiv_add_const _
      rw [this]
    rw [hshift, modelLaplacian_quadratic b hb hbs x]
  rw [hlap]
  simpa using ((hasDerivAt_id t).const_mul
    (2 * (Module.finrank ℝ E : ℝ))).const_add (b x x)

end RicciFlow

namespace RicciFlow

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Heat solutions preserve nonnegativity**: a solution of the heat equation
with nonnegative initial data on a compact domain stays nonnegative — the
maximum principle applied to the equation itself.
-/
theorem heat_solution_nonneg_preserved (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {u : ℝ → E → ℝ} {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {T : ℝ}
    (hu_cont : Continuous ↿u)
    (hheat : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T, IsHeatSolutionAt b hb u t x)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u t))
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (u t) K x → IsLocalMin (u t) x)
    (h0 : ∀ x ∈ K, 0 ≤ u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, 0 ≤ u t x :=
  heat_supersolution_nonneg_preserved b hb hbs hbpos hK hKne hu_cont
    (R' := fun t x ↦ modelLaplacian b hb (u t) x)
    (fun x hx t ht ↦ hheat x hx t ht)
    hspace
    (fun t ht x hx ↦ le_refl _)
    hmin_int h0

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The metric divergence of a vector field: the trace of its covariant
derivative `∇X = DX + Γ(·, X)`. -/
noncomputable def modelDivergence (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    (X : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E
    ((fderiv ℝ X x).toLinearMap
      + (christoffelLinear G x (b x) (hb x)).flip (X x))

/-- The divergence of the identity field on a constant metric is the
dimension. -/
theorem modelDivergence_id_const (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate) (x : E) :
    modelDivergence (fun _ ↦ G₀) b hb (fun y ↦ y) x =
      Module.finrank ℝ E := by
  unfold modelDivergence
  have hΓ : (christoffelLinear (fun _ : E ↦ G₀) x (b x) (hb x)).flip x =
      0 := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.flip_apply, LinearMap.zero_apply]
    exact christoffelAt_const G₀ x (b x) (hb x) v x
  rw [hΓ, add_zero, fderiv_id']
  simp [LinearMap.trace_id]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**`div ∘ grad = Δ`** (constant metrics): the divergence of the gradient is
the Laplacian — the defining cross-check tying the four Bochner operators
together.
-/
theorem modelDivergence_gradient_const (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b₀ : LinearMap.BilinForm ℝ E) (hb₀ : b₀.Nondegenerate)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    modelDivergence (fun _ ↦ G₀) (fun _ ↦ b₀) (fun _ ↦ hb₀)
      (fun y ↦ metricGradient b₀ hb₀ f y) x =
      modelLaplacian b₀ hb₀ f x := by
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- The gradient is a fixed continuous linear map applied to `Df`.
  set Lc : (E →L[ℝ] ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap
    ((LinearMap.BilinForm.toDual b₀ hb₀).symm.toLinearMap ∘ₗ
      (LinearMap.toContinuousLinearMap.symm :
        (E →L[ℝ] ℝ) ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ)).toLinearMap) with hLc
  have hgrad : (fun y ↦ metricGradient b₀ hb₀ f y) =
      fun y ↦ Lc (fderiv ℝ f y) := rfl
  unfold modelDivergence
  rw [hgrad]
  -- The corrector term vanishes for a constant metric.
  rw [show (christoffelLinear (fun _ : E ↦ G₀) x ((fun _ : E ↦ b₀) x)
      ((fun _ : E ↦ hb₀) x)).flip ((fun y ↦ Lc (fderiv ℝ f y)) x) = 0
    from by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.flip_apply, LinearMap.zero_apply]
      exact christoffelAt_const G₀ x b₀ hb₀ v _, add_zero]
  -- The derivative of `Lc ∘ Df` is `Lc ∘ D²f`.
  have hd : fderiv ℝ (fun y ↦ Lc (fderiv ℝ f y)) x =
      Lc.comp (fderiv ℝ (fderiv ℝ f) x) :=
    (Lc.hasFDerivAt.comp x (hf1 x).hasFDerivAt).fderiv
  rw [hd]
  unfold modelLaplacian
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The gradient is odd. -/
theorem metricGradient_neg (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) {f : E → ℝ} (hf : Differentiable ℝ f)
    (x : E) :
    metricGradient b hb (fun y ↦ -f y) x = -metricGradient b hb f x := by
  unfold metricGradient
  rw [show fderiv ℝ (fun y ↦ -f y) x = -fderiv ℝ f x from
    fderiv_neg (f := f)]
  simp

/--
**The conjugate-heat weight identity**:
`Δ(e^{−f}) = e^{−f}(|∇f|² − Δf)` — the pointwise identity of the weight
`e^{−f}` in Perelman's `𝓕`-functional and conjugate heat equation.
-/
theorem modelLaplacian_exp_neg (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    modelLaplacian b hb (fun y ↦ Real.exp (-f y)) x =
      Real.exp (-f x) *
        (b (metricGradient b hb f x) (metricGradient b hb f x)
          - modelLaplacian b hb f x) := by
  have hnf : ContDiff ℝ 2 (fun y ↦ -f y) := hf.neg
  have h := modelLaplacian_exp b hb hnf x
  rw [h, metricGradient_neg b hb (hf.differentiable (by norm_num)) x]
  have hsm : modelLaplacian b hb (fun y ↦ -f y) x =
      -modelLaplacian b hb f x := by
    have := modelLaplacian_smul b hb (-1 : ℝ) hf (x := x)
    simp only [neg_one_mul] at this
    rw [this]
  rw [hsm]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

open scoped Manifold in
/--
**Perelman's `𝓕`-density**: the pointwise integrand
`(R + |∇f|²) e^{−f}` of the `𝓕`-functional, defined against the genuine
scalar curvature of a connection on the model space — the first object of
the entropy stratum.
-/
noncomputable def perelmanFDensity
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (f : E → ℝ) (x : E) : ℝ :=
  (scalarCurvatureAt cov x b hb
    + b (metricGradient b hb f x) (metricGradient b hb f x))
    * Real.exp (-f x)

open scoped Manifold in
/-- The `𝓕`-density is nonnegative wherever the scalar curvature is. -/
theorem perelmanFDensity_nonneg
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    (f : E → ℝ) {x : E}
    (hscal : 0 ≤ scalarCurvatureAt cov x b hb) :
    0 ≤ perelmanFDensity cov b hb f x := by
  unfold perelmanFDensity
  have hgrad := gradient_sq_nonneg b hb hbpos f x
  have hexp : (0 : ℝ) < Real.exp (-f x) := Real.exp_pos _
  positivity

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

open scoped Manifold in
/--
**Perelman's `𝒲`-density**: the pointwise integrand
`[τ(R + |∇f|²) + f − n] (4πτ)^{−n/2} e^{−f}` of the `𝒲`-entropy — the
scale-sensitive refinement of the `𝓕`-density.
-/
noncomputable def perelmanWDensity
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (f : E → ℝ) (τ : ℝ) (x : E) : ℝ :=
  (τ * (scalarCurvatureAt cov x b hb
      + b (metricGradient b hb f x) (metricGradient b hb f x))
    + f x - Module.finrank ℝ E)
    * ((4 * Real.pi * τ) ^ (-(Module.finrank ℝ E : ℝ) / 2)
      * Real.exp (-f x))

open scoped Manifold in
/-- The `𝒲`-density refines the `𝓕`-density: at `τ = 1` the curvature
part of `𝒲` is the `𝓕`-density rescaled by the normalization. -/
theorem perelmanWDensity_tau_one
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (f : E → ℝ) (x : E) :
    perelmanWDensity cov b hb f 1 x =
      (4 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)
        * (perelmanFDensity cov b hb f x
          + (f x - Module.finrank ℝ E) * Real.exp (-f x)) := by
  unfold perelmanWDensity perelmanFDensity
  rw [mul_one]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The gradient of the quadratic form is `2x`** — the computation
behind the Gaussian shrinking soliton's potential. -/
theorem metricGradient_quadratic (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : ∀ v w : E, b v w = b w v) (x : E) :
    metricGradient b hb (fun y ↦ b y y) x = (2 : ℝ) • x := by
  -- Identify through the defining property and nondegeneracy.
  have hkey : ∀ v : E, b (metricGradient b hb (fun y ↦ b y y) x) v =
      b ((2 : ℝ) • x) v := by
    intro v
    rw [b_metricGradient]
    -- The derivative of the quadratic form.
    set bC : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ b) with hbC
    have hf1 : HasFDerivAt (fun z ↦ b z z) (bC x + bC.flip x) x := by
      have hc : HasFDerivAt (fun z : E ↦ bC z) bC x := bC.hasFDerivAt
      have h := hc.clm_apply (hasFDerivAt_id x)
      have heq : (fun z : E ↦ bC z z) = fun z ↦ b z z := by
        funext z
        rfl
      rw [← heq]
      convert h using 1
    rw [hf1.fderiv]
    have h1 : bC x v = b x v := rfl
    have h2 : bC.flip x v = b v x := rfl
    simp only [ContinuousLinearMap.add_apply, h1, h2,
      ContinuousLinearMap.flip_apply]
    rw [hbs v x]
    rw [show b ((2 : ℝ) • x) v = 2 * b x v from by
      rw [map_smul]
      simp [smul_eq_mul]]
    ring
  have hzero : ∀ v : E,
      b (metricGradient b hb (fun y ↦ b y y) x - (2 : ℝ) • x) v = 0 := by
    intro v
    rw [map_sub, LinearMap.sub_apply, hkey v, sub_self]
  exact sub_eq_zero.mp (hb.1 _ hzero)

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The gradient is homogeneous. -/
theorem metricGradient_const_mul (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) {f : E → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (x : E) :
    metricGradient b hb (fun y ↦ c * f y) x =
      c • metricGradient b hb f x := by
  unfold metricGradient
  rw [fderiv_const_mul (hf x) c]
  simp [map_smul]

/-- **The Gaussian soliton's gradient**: `∇(b(x,x)/4τ) = x/(2τ)`. -/
theorem gaussian_gradient (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : ∀ v w : E, b v w = b w v)
    {τ : ℝ} (hτ : τ ≠ 0) (x : E) :
    metricGradient b hb (fun y ↦ (1 / (4 * τ)) * b y y) x =
      (1 / (2 * τ)) • x := by
  have hq : Differentiable ℝ (fun y : E ↦ b y y) := by
    intro y
    set bC : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ b) with hbC
    have hc : HasFDerivAt (fun z : E ↦ bC z) bC y := bC.hasFDerivAt
    have h := hc.clm_apply (hasFDerivAt_id y)
    have heq : (fun z : E ↦ bC z z) = fun z ↦ b z z := by
      funext z
      rfl
    rw [← heq]
    exact h.differentiableAt
  rw [metricGradient_const_mul b hb hq _ x,
    metricGradient_quadratic b hb hbs x, smul_smul]
  congr 1
  field_simp
  ring

/-- **The Gaussian soliton's Laplacian**: `Δ(b(x,x)/4τ) = n/(2τ)`. -/
theorem gaussian_laplacian (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : ∀ v w : E, b v w = b w v)
    {τ : ℝ} (hτ : τ ≠ 0) (x : E) :
    modelLaplacian b hb (fun y ↦ (1 / (4 * τ)) * b y y) x =
      Module.finrank ℝ E / (2 * τ) := by
  have hq2 : ContDiff ℝ 2 (fun y : E ↦ b y y) := by
    set bC : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ b) with hbC
    have heq : (fun z : E ↦ bC z z) = fun z ↦ b z z := by
      funext z
      rfl
    rw [← heq]
    exact (bC.contDiff.clm_apply contDiff_id)
  rw [modelLaplacian_smul b hb _ hq2,
    modelLaplacian_quadratic b hb hbs x]
  field_simp
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The Gaussian soliton equation**: `Hess(b(x,x)/4τ) = b/(2τ)` on a
constant metric. With the flat connection Ricci-flat, this is exactly the
shrinking gradient-soliton equation `Ric + Hess f = g/(2τ)` — the model
self-similar singularity of the Ricci flow, verified pointwise.
-/
theorem gaussian_soliton_hessian (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : ∀ v w : E, b v w = b w v)
    {τ : ℝ} (hτ : τ ≠ 0) (x v w : E) :
    covariantHessian (fun _ ↦ G₀) (fun _ ↦ b) (fun _ ↦ hb)
      (fun y ↦ (1 / (4 * τ)) * b y y) x v w =
      (1 / (2 * τ)) * b v w := by
  unfold covariantHessian
  -- The corrector dies on the constant metric.
  rw [show christoffelAt (fun _ : E ↦ G₀) x ((fun _ : E ↦ b) x)
      ((fun _ : E ↦ hb) x) v w = 0 from
    christoffelAt_const G₀ x b hb v w, map_zero, sub_zero]
  -- The Hessian of the scaled quadratic form.
  set bC : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ b) with hbC
  have hf1 : ∀ y : E, HasFDerivAt (fun z ↦ (1 / (4 * τ)) * b z z)
      ((1 / (4 * τ)) • (bC y + bC.flip y)) y := by
    intro y
    have hc : HasFDerivAt (fun z : E ↦ bC z) bC y := bC.hasFDerivAt
    have h := (hc.clm_apply (hasFDerivAt_id y)).const_mul (1 / (4 * τ))
    have heq : (fun z : E ↦ (1 / (4 * τ)) * bC z z) =
        fun z ↦ (1 / (4 * τ)) * b z z := by
      funext z
      rfl
    rw [← heq]
    convert h using 1
  have hdf : fderiv ℝ (fun z ↦ (1 / (4 * τ)) * b z z) =
      fun y ↦ (1 / (4 * τ)) • (bC y + bC.flip y) :=
    funext fun y ↦ (hf1 y).fderiv
  have hd2 : fderiv ℝ (fderiv ℝ (fun z ↦ (1 / (4 * τ)) * b z z)) x =
      (1 / (4 * τ)) • (bC + bC.flip) := by
    rw [hdf]
    have hlin : HasFDerivAt
        (fun y : E ↦ (1 / (4 * τ)) • (bC y + bC.flip y))
        ((1 / (4 * τ)) • (bC + bC.flip)) x := by
      have h1 : HasFDerivAt (fun y : E ↦ bC y + bC.flip y)
          (bC + bC.flip) x := by
        simpa using bC.hasFDerivAt.add bC.flip.hasFDerivAt
      exact h1.const_smul (1 / (4 * τ))
    exact hlin.fderiv
  rw [hd2]
  have h1 : bC v w = b v w := rfl
  have h2 : bC.flip v w = b w v := rfl
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    h1, h2, ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hbs w v]
  field_simp
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The trivial steady soliton**: affine potentials on a constant metric
have vanishing covariant Hessian — with flat Ricci-flatness, the steady
gradient-soliton equation `Ric + Hess f = 0` holds. The Gaussian
(shrinking) and affine (steady) examples bracket the soliton taxonomy.
-/
theorem affine_steady_soliton (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (L : E →L[ℝ] ℝ) (c : ℝ) (x v w : E) :
    covariantHessian (fun _ ↦ G₀) (fun _ ↦ b) (fun _ ↦ hb)
      (fun y ↦ L y + c) x v w = 0 := by
  unfold covariantHessian
  rw [show christoffelAt (fun _ : E ↦ G₀) x ((fun _ : E ↦ b) x)
      ((fun _ : E ↦ hb) x) v w = 0 from
    christoffelAt_const G₀ x b hb v w, map_zero, sub_zero]
  have hdf : fderiv ℝ (fun y ↦ L y + c) = fun _ ↦ (L : E →L[ℝ] ℝ) := by
    funext y
    rw [fderiv_add_const]
    exact L.fderiv
  rw [hdf, fderiv_fun_const]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

open scoped Manifold in
/--
**The gradient-soliton equation** at a point: `Ric + Hess f = λ b`,
stated against the genuine Ricci form of a connection and the covariant
Hessian of the Christoffel data.
-/
def IsGradientSolitonAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    (f : E → ℝ) (lam : ℝ) (x : E) : Prop :=
  ∀ v w : E, ricciBilinearAt cov x v w
    + covariantHessian G b hb f x v w = lam * (b x) v w

open scoped Manifold in
/--
**The Gaussian is a shrinking gradient soliton**: on Euclidean space with
the flat connection, the potential `b(x,x)/4τ` satisfies
`Ric + Hess f = (1/2τ) b` exactly.
-/
theorem gaussian_isGradientSoliton
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b₀ : LinearMap.BilinForm ℝ E) (hb₀ : b₀.Nondegenerate)
    (hbs : ∀ v w : E, b₀ v w = b₀ w v)
    {τ : ℝ} (hτ : τ ≠ 0) (x : E) :
    IsGradientSolitonAt (flatCovariantDerivative ℝ E)
      (fun _ ↦ G₀) (fun _ ↦ b₀) (fun _ ↦ hb₀)
      (fun y ↦ (1 / (4 * τ)) * b₀ y y) (1 / (2 * τ)) x := by
  intro v w
  rw [flat_ricciBilinearAt_eq_zero x v w,
    gaussian_soliton_hessian G₀ b₀ hb₀ hbs hτ x v w]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

open scoped Manifold in
/-- **The affine potential is a steady gradient soliton** (`λ = 0`). -/
theorem affine_isGradientSoliton
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b₀ : LinearMap.BilinForm ℝ E) (hb₀ : b₀.Nondegenerate)
    (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    IsGradientSolitonAt (flatCovariantDerivative ℝ E)
      (fun _ ↦ G₀) (fun _ ↦ b₀) (fun _ ↦ hb₀)
      (fun y ↦ L y + c) 0 x := by
  intro v w
  rw [flat_ricciBilinearAt_eq_zero x v w,
    affine_steady_soliton G₀ b₀ hb₀ L c x v w]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

open scoped Manifold in
/-- The scalar curvature on the model space as an `E`-typed trace — the
instance bridge between the curvature and Bochner strata. -/
theorem scalarCurvatureAt_eq_trace_E
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (x : E) (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate) :
    scalarCurvatureAt cov x b hb = LinearMap.trace ℝ E
      (((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        ricciDualAt cov x : E →ₗ[ℝ] E)) := rfl

open scoped Manifold in
/--
**The soliton trace identity**: tracing `Ric + Hess f = λ b` gives
`R + Δf = nλ` — the first structural consequence of the soliton equation.
-/
theorem isGradientSolitonAt_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {f : E → ℝ} {lam : ℝ} {x : E}
    (hsol : IsGradientSolitonAt cov G b hb f lam x) :
    scalarCurvatureAt cov x (b x) (hb x) + curvedLaplacian G b hb f x =
      lam * Module.finrank ℝ E := by
  rw [scalarCurvatureAt_eq_trace_E cov x (b x) (hb x)]
  unfold curvedLaplacian
  rw [← map_add]
  have hcomp : (((LinearMap.BilinForm.toDual (b x) (hb x)).symm.toLinearMap
        ∘ₗ ricciDualAt cov x : E →ₗ[ℝ] E))
      + ((LinearMap.BilinForm.toDual (b x) (hb x)).symm.toLinearMap ∘ₗ
        covariantHessianLin G b hb f x) = lam • LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply (LinearMap.BilinForm.toDual (b x) (hb x)).injective
    rw [LinearMap.add_apply, map_add]
    have h1 : (LinearMap.BilinForm.toDual (b x) (hb x))
        ((((LinearMap.BilinForm.toDual (b x) (hb x)).symm.toLinearMap
          ∘ₗ ricciDualAt cov x : E →ₗ[ℝ] E)) v) = ricciDualAt cov x v :=
      LinearEquiv.apply_symm_apply _ _
    have h2 : (LinearMap.BilinForm.toDual (b x) (hb x))
        (((LinearMap.BilinForm.toDual (b x) (hb x)).symm.toLinearMap ∘ₗ
          covariantHessianLin G b hb f x) v) =
        covariantHessianLin G b hb f x v :=
      LinearEquiv.apply_symm_apply _ _
    rw [h1, h2]
    apply LinearMap.ext
    intro w
    have hval : ricciBilinearAt cov x v w
        + covariantHessian G b hb f x v w = lam * (b x) v w := hsol v w
    have hgoal : (ricciDualAt cov x v) w
        + (covariantHessianLin G b hb f x v) w = lam * (b x) v w := hval
    rw [show ((LinearMap.BilinForm.toDual (b x) (hb x))
        ((lam • LinearMap.id : E →ₗ[ℝ] E) v)) w = lam * (b x) v w from by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
        smul_eq_mul]
      rw [LinearMap.BilinForm.toDual_def]]
    exact hgoal
  rw [hcomp, map_smul, LinearMap.trace_id, smul_eq_mul]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

open scoped Manifold in
/-- **Euclidean space has zero scalar curvature** — the Ricci form
vanishes, so its trace does. -/
theorem flat_scalarCurvatureAt_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (x : E) (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate) :
    scalarCurvatureAt (flatCovariantDerivative ℝ E) x b hb = 0 := by
  rw [scalarCurvatureAt_eq_trace_E]
  have hzero : ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
      ricciDualAt (flatCovariantDerivative ℝ E) x : E →ₗ[ℝ] E) = 0 := by
    apply LinearMap.ext
    intro v
    have hv : ricciDualAt (flatCovariantDerivative ℝ E) x v = 0 := by
      apply LinearMap.ext
      intro w
      rw [show ((ricciDualAt (flatCovariantDerivative ℝ E) x) v) w =
        ricciBilinearAt (flatCovariantDerivative ℝ E) x v w from rfl,
        flat_ricciBilinearAt_eq_zero x v w]
      simp
    show (LinearMap.BilinForm.toDual b hb).symm
      (ricciDualAt (flatCovariantDerivative ℝ E) x v) = 0
    rw [hv]
    exact map_zero _
  rw [hzero]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

open scoped Manifold in
/--
**The Gaussian trace cross-check**: deriving the Gaussian's Laplacian from
the soliton trace identity (rather than direct computation) — four
theorems (soliton instance, trace identity, flat scalar-flatness, and the
direct computation) confirm each other across three strata.
-/
theorem gaussian_curvedLaplacian_via_soliton
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b₀ : LinearMap.BilinForm ℝ E) (hb₀ : b₀.Nondegenerate)
    (hbs : ∀ v w : E, b₀ v w = b₀ w v)
    {τ : ℝ} (hτ : τ ≠ 0) (x : E) :
    curvedLaplacian (fun _ ↦ G₀) (fun _ ↦ b₀) (fun _ ↦ hb₀)
      (fun y ↦ (1 / (4 * τ)) * b₀ y y) x =
      Module.finrank ℝ E / (2 * τ) := by
  have h := isGradientSolitonAt_trace (flatCovariantDerivative ℝ E)
    (fun _ ↦ G₀) (fun _ ↦ b₀) (fun _ ↦ hb₀)
    (gaussian_isGradientSoliton G₀ b₀ hb₀ hbs hτ x)
  have hscal : scalarCurvatureAt (flatCovariantDerivative ℝ E) x
      ((fun _ : E ↦ b₀) x) ((fun _ : E ↦ hb₀) x) = 0 :=
    flat_scalarCurvatureAt_eq_zero x b₀ hb₀
  rw [hscal, zero_add] at h
  rw [h]
  field_simp

end RicciFlow

namespace RicciFlow

/--
**The flat Ricci identity**: second derivatives of vector fields commute
on Euclidean space — `∇²_{v,w}X = ∇²_{w,v}X`, consistent with the proven
vanishing of the flat curvature (`R(v,w)X = 0`). The entry point of the
commutation stratum: on curved backgrounds this asymmetry IS the curvature,
which is what turns Laplacians of curvature quantities into the evolution
equations.
-/
theorem flat_second_derivative_commutes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : E → E} (hX : ContDiff ℝ 2 X) (x v w : E) :
    fderiv ℝ (fderiv ℝ X) x v w = fderiv ℝ (fderiv ℝ X) x w v :=
  (hX.contDiffAt.isSymmSndFDerivAt (by simp)) v w

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
The second covariant derivative of a vector field for the Christoffel-form
connection: `∇²_{v,w} X = ∇_v(∇_w X) − ∇_{Γ(v,w)} X`, written out in flat
+ corrector terms. Its antisymmetrization is the curvature — the object of
the Ricci identity.
-/
noncomputable def covariantSecondDerivative
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    (X : E → E) (x v w : E) : E :=
  fderiv ℝ (fun y ↦ fderiv ℝ X y w
      + christoffelAt G y (b y) (hb y) w (X y)) x v
    + christoffelAt G x (b x) (hb x) v
      (fderiv ℝ X x w + christoffelAt G x (b x) (hb x) w (X x))
    - (fderiv ℝ X x (christoffelAt G x (b x) (hb x) v w)
      + christoffelAt G x (b x) (hb x)
        (christoffelAt G x (b x) (hb x) v w) (X x))

/--
**The flat anchor**: on a constant metric the second covariant derivative
is the flat second derivative — every corrector term dies.
-/
theorem covariantSecondDerivative_const (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {X : E → E} (hX : ContDiff ℝ 2 X) (x v w : E) :
    covariantSecondDerivative (fun _ ↦ G₀) b hb X x v w =
      fderiv ℝ (fderiv ℝ X) x v w := by
  unfold covariantSecondDerivative
  have hΓ : ∀ (y u z : E), christoffelAt (fun _ : E ↦ G₀) y (b y) (hb y)
      u z = 0 := fun y u z ↦ christoffelAt_const G₀ y (b y) (hb y) u z
  simp only [hΓ, add_zero, map_zero, zero_add, sub_zero]
  -- The inner function is evaluation of the derivative at `w`.
  have hf1 : Differentiable ℝ (fderiv ℝ X) :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have happ : fderiv ℝ (fun y ↦ fderiv ℝ X y w) x =
      (ContinuousLinearMap.apply ℝ E w).comp
        (fderiv ℝ (fderiv ℝ X) x) :=
    ((ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp x
      (hf1 x).hasFDerivAt).fderiv
  rw [happ]
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The Ricci identity on constant metrics**: second covariant derivatives
commute — `∇²_{v,w}X = ∇²_{w,v}X` — consistent with vanishing curvature.
The curved version of this asymmetry equals `R(v,w)X`: the next mountain.
-/
theorem covariantSecondDerivative_comm_const (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {X : E → E} (hX : ContDiff ℝ 2 X) (x v w : E) :
    covariantSecondDerivative (fun _ ↦ G₀) b hb X x v w =
      covariantSecondDerivative (fun _ ↦ G₀) b hb X x w v := by
  rw [covariantSecondDerivative_const G₀ b hb hX x v w,
    covariantSecondDerivative_const G₀ b hb hX x w v,
    flat_second_derivative_commutes hX x v w]

end RicciFlow

namespace RicciFlow

open CovariantDerivative FiberBundle

open scoped Manifold in
/--
**The Ricci identity in `∇²`-form**: the antisymmetrized second covariant
derivative equals the curvature — the `∇_{Γ(v,w)}`-terms cancel by
corrector symmetry against the coordinate formula.
-/
theorem covariantSecondDerivative_antisymm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    (hGd : Differentiable ℝ G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (X : E → E) {x : E} (v w : TangentSpace 𝓘(ℝ, E) x) :
    covariantSecondDerivative G b hb X x v w
      - covariantSecondDerivative G b hb X x w v =
      curvatureOp (modelLeviCivita G b hb)
        (extend E v) (extend E w) X x := by
  rw [← ricci_identity G b hb X v w]
  unfold covariantSecondDerivative
  rw [christoffelAt_symm G (b x) (hb x) (hGd x) hGsymm w v]
  abel

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The corrector functional is additive in the metric** (scalar form) — the
linearity underlying the variation formula `δΓ` for metric flows. (The
nested-CLM `DifferentiableAt.add` gremlin is resolved by pinning the
codomain explicitly.)
-/
theorem christoffelFunctional_add_apply
    {G₁ G₂ : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hG₁ : DifferentiableAt ℝ G₁ x) (hG₂ : DifferentiableAt ℝ G₂ x)
    (u v w : E) :
    christoffelFunctional (fun y ↦ G₁ y + G₂ y) x u v w =
      christoffelFunctional G₁ x u v w
        + christoffelFunctional G₂ x u v w := by
  have hdsum : DifferentiableAt ℝ (fun y ↦ G₁ y + G₂ y) x :=
    DifferentiableAt.add (𝕜 := ℝ) (E := E)
      (F := E →L[ℝ] E →L[ℝ] ℝ) hG₁ hG₂
  -- Scalar derivative additivity through evaluation functionals.
  have hterm : ∀ p q r : E,
      (fderiv ℝ (fun y ↦ G₁ y + G₂ y) x p) q r =
        (fderiv ℝ G₁ x p) q r + (fderiv ℝ G₂ x p) q r := by
    intro p q r
    set L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ r).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) q) with hL
    have happly : ∀ (G : E → E →L[ℝ] E →L[ℝ] ℝ),
        DifferentiableAt ℝ G x →
        fderiv ℝ (fun y ↦ L (G y)) x = L.comp (fderiv ℝ G x) := by
      intro G hG
      rw [show (fun y ↦ L (G y)) = L ∘ G from rfl,
        fderiv_comp x L.differentiableAt hG, L.fderiv]
    have hkey := happly (fun y ↦ G₁ y + G₂ y) hdsum
    have hsum_fn : (fun y ↦ L ((fun y' ↦ G₁ y' + G₂ y') y)) =
        fun y ↦ L (G₁ y) + L (G₂ y) := by
      funext y
      rw [map_add]
    rw [hsum_fn] at hkey
    have hd2 : fderiv ℝ (fun y ↦ L (G₁ y) + L (G₂ y)) x =
        L.comp (fderiv ℝ G₁ x) + L.comp (fderiv ℝ G₂ x) := by
      rw [fderiv_fun_add (f := fun y ↦ L (G₁ y)) (g := fun y ↦ L (G₂ y))
        (L.differentiableAt.comp x hG₁) (L.differentiableAt.comp x hG₂)]
      rw [happly G₁ hG₁, happly G₂ hG₂]
    rw [hd2] at hkey
    have := congrFun (congrArg DFunLike.coe hkey.symm) p
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, hL] at this
    simpa using this
  simp only [christoffelFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.add_apply]
  rw [hterm u v w, hterm v u w, hterm w u v]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional is homogeneous in the metric — the scalar
twin of the `δΓ`-linearity. -/
theorem christoffelFunctional_smul_apply
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (c : ℝ)
    (hG : DifferentiableAt ℝ G x) (u v w : E) :
    christoffelFunctional (fun y ↦ c • G y) x u v w =
      c * christoffelFunctional G x u v w := by
  have hterm : ∀ p q r : E,
      (fderiv ℝ (fun y ↦ c • G y) x p) q r =
        c * (fderiv ℝ G x p) q r := by
    intro p q r
    set L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ r).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) q) with hL
    have happly : ∀ (H : E → E →L[ℝ] E →L[ℝ] ℝ),
        DifferentiableAt ℝ H x →
        fderiv ℝ (fun y ↦ L (H y)) x = L.comp (fderiv ℝ H x) := by
      intro H hH
      rw [show (fun y ↦ L (H y)) = L ∘ H from rfl,
        fderiv_comp x L.differentiableAt hH, L.fderiv]
    have hdsmul : DifferentiableAt ℝ (fun y ↦ c • G y) x :=
      DifferentiableAt.const_smul (𝕜 := ℝ) (E := E)
        (F := E →L[ℝ] E →L[ℝ] ℝ) hG c
    have hkey := happly (fun y ↦ c • G y) hdsmul
    have hsmul_fn : (fun y ↦ L ((fun y' ↦ c • G y') y)) =
        fun y ↦ c * L (G y) := by
      funext y
      rw [show L (c • G y) = c • L (G y) from map_smul L c (G y)]
      simp [smul_eq_mul]
    rw [hsmul_fn] at hkey
    have hd2 : fderiv ℝ (fun y ↦ c * L (G y)) x =
        c • L.comp (fderiv ℝ G x) := by
      rw [fderiv_const_mul (a := fun y ↦ L (G y))
        (L.differentiableAt.comp x hG) c, happly G hG]
    rw [hd2] at hkey
    have := congrFun (congrArg DFunLike.coe hkey.symm) p
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, hL, smul_eq_mul] at this
    simpa using this
  simp only [christoffelFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hterm u v w, hterm v u w, hterm w u v]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The time-derivative of the corrector functional**: along a metric flow
`t ↦ Gₜ`, if the mixed space–time derivatives commute (the three slot
hypotheses), the corrector functional differentiates to the functional of
`∂G/∂t` — the `δΓ` variation formula at the functional level.
-/
theorem hasDerivAt_christoffelFunctional
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u v w : E)
    (h1 : HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x u) v w)
      ((fderiv ℝ H x u) v w) t₀)
    (h2 : HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x v) u w)
      ((fderiv ℝ H x v) u w) t₀)
    (h3 : HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x w) u v)
      ((fderiv ℝ H x w) u v) t₀) :
    HasDerivAt (fun t ↦ christoffelFunctional (Gt t) x u v w)
      (christoffelFunctional H x u v w) t₀ := by
  have hsum := ((h1.add h2).sub h3).const_mul (1 / 2 : ℝ)
  have heq : (fun t ↦ christoffelFunctional (Gt t) x u v w) =
      fun t ↦ (1 / 2 : ℝ) * ((fderiv ℝ (Gt t) x u) v w
        + (fderiv ℝ (Gt t) x v) u w - (fderiv ℝ (Gt t) x w) u v) := by
    funext t
    rfl
  rw [heq]
  convert hsum using 1

end RicciFlow

namespace RicciFlow

open ContinuousLinearMap

/--
**The derivative of the operator inverse**: along a differentiable path of
invertible operators, `d(A⁻¹) = −A⁻¹ A' A⁻¹` — obtained by
differentiating `A⁻¹ ∘ A = id` and solving with the inverse identities.
The formula behind `∂(g⁻¹)/∂t = 2 g⁻¹ Ric g⁻¹` in the evolution equations.
-/
theorem hasDerivAt_clm_inverse
    {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace M]
    {A : ℝ → M →L[ℝ] N} {A' : M →L[ℝ] N} {t₀ : ℝ}
    (hd : HasDerivAt A A' t₀)
    (hev : ∀ᶠ t in nhds t₀, (A t).IsInvertible) :
    HasDerivAt (fun t ↦ (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  have hinv : (A t₀).IsInvertible := hev.self_of_nhds
  -- Differentiability of the inverse path.
  have hBdiff : DifferentiableAt ℝ (fun t ↦ (A t).inverse) t₀ :=
    ((hinv.contDiffAt_map_inverse (n := 1)).differentiableAt
      one_ne_zero).comp t₀ hd.differentiableAt
  set B' := deriv (fun t ↦ (A t).inverse) t₀ with hB'
  have hB : HasDerivAt (fun t ↦ (A t).inverse) B' t₀ :=
    hBdiff.hasDerivAt
  -- The composite is eventually the identity.
  have hid : (fun t ↦ ((A t).inverse).comp (A t)) =ᶠ[nhds t₀]
      fun _ ↦ ContinuousLinearMap.id ℝ M := by
    filter_upwards [hev] with t ht
    obtain ⟨e, he⟩ := ht
    rw [← he, inverse_equiv]
    ext m
    simp
  -- Differentiate both sides.
  have hcomp : HasDerivAt (fun t ↦ ((A t).inverse).comp (A t))
      (B'.comp (A t₀) + ((A t₀).inverse).comp A') t₀ :=
    hB.clm_comp hd
  have hzero : B'.comp (A t₀) + ((A t₀).inverse).comp A' = 0 := by
    have hconst : HasDerivAt
        (fun _ : ℝ ↦ ContinuousLinearMap.id ℝ M) 0 t₀ :=
      hasDerivAt_const t₀ _
    have hcomp' : HasDerivAt (fun _ : ℝ ↦ ContinuousLinearMap.id ℝ M)
        (B'.comp (A t₀) + ((A t₀).inverse).comp A') t₀ :=
      hcomp.congr_of_eventuallyEq hid.symm
    exact (hcomp'.unique hconst)
  -- Solve for `B'` with the inverse identities.
  obtain ⟨e, he⟩ := hinv
  have hBA : B'.comp (A t₀) = -(((A t₀).inverse).comp A') := by
    linear_combination (norm := abel) hzero
  have hsolve : B' = -(((A t₀).inverse).comp (A'.comp (A t₀).inverse)) := by
    have h1 := congrArg (fun L ↦ L.comp ((A t₀).inverse)) hBA
    simp only at h1
    rw [ContinuousLinearMap.comp_assoc] at h1
    have hAinv : (A t₀).comp ((A t₀).inverse) =
        ContinuousLinearMap.id ℝ N := by
      rw [← he, inverse_equiv]
      ext n
      simp
    rw [hAinv, ContinuousLinearMap.comp_id] at h1
    rw [h1, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
  rw [← hsolve]
  exact hB

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Derivative reconstruction for functional-valued paths**: in finite
dimension, a path of functionals whose every evaluation differentiates has
a derivative — reconstructed through a basis. The bridge from the scalar
`δΓ`-derivatives to the vector-level variation of the connection.
-/
theorem hasDerivAt_clm_of_forall_apply
    {φ : ℝ → E →L[ℝ] ℝ} {ψ : E →L[ℝ] ℝ} {t₀ : ℝ}
    (h : ∀ w : E, HasDerivAt (fun t ↦ φ t w) (ψ w) t₀) :
    HasDerivAt φ ψ t₀ := by
  set bE := Module.finBasis ℝ E with hbE
  set coordC : (Fin (Module.finrank ℝ E)) → (E →L[ℝ] ℝ) :=
    fun i ↦ LinearMap.toContinuousLinearMap (bE.coord i) with hcoord
  -- Reconstruction: every functional is the coordinate sum.
  have hrepr : ∀ ρ : E →L[ℝ] ℝ,
      ρ = ∑ i, ρ (bE i) • coordC i := by
    intro ρ
    ext w
    have hw := bE.sum_repr w
    conv_lhs => rw [← hw]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (coordC i) w = bE.coord i w from rfl,
      Module.Basis.coord_apply]
    ring
  -- Differentiate the coordinate sum.
  have hsum : HasDerivAt (fun t ↦ ∑ i, φ t (bE i) • coordC i)
      (∑ i, ψ (bE i) • coordC i) t₀ := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (h (bE i)).smul_const (coordC i)
  have hfun : (fun t ↦ φ t) = fun t ↦ ∑ i, φ t (bE i) • coordC i := by
    funext t
    exact hrepr (φ t)
  rw [show φ = fun t ↦ φ t from rfl, hfun, hrepr ψ]
  exact hsum

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The variation of the Christoffel symbols along a metric flow** (`δΓ`):
the closed-form corrector `Γₜ = Gₜ⁻¹ Φₜ` differentiates by the product
rule into the inverse-derivative and functional-derivative terms —
`∂Γ/∂t = G⁻¹ Φ_{∂G} − G⁻¹ (∂G) G⁻¹ Φ_G`. The variation of the connection:
the direct precursor of the curvature evolution equation.
-/
theorem hasDerivAt_christoffel_flow
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u v : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀) :
    HasDerivAt (fun t ↦ (Gt t x).inverse
        (LinearMap.toContinuousLinearMap
          (christoffelFunctional (Gt t) x u v)))
      ((-((Gt t₀ x).inverse.comp ((H x).comp (Gt t₀ x).inverse)))
          (LinearMap.toContinuousLinearMap
            (christoffelFunctional (Gt t₀) x u v))
        + (Gt t₀ x).inverse (LinearMap.toContinuousLinearMap
          (christoffelFunctional H x u v))) t₀ := by
  have hΦ : HasDerivAt (fun t ↦ LinearMap.toContinuousLinearMap
      (christoffelFunctional (Gt t) x u v))
      (LinearMap.toContinuousLinearMap
        (christoffelFunctional H x u v)) t₀ := by
    apply hasDerivAt_clm_of_forall_apply
    intro w
    exact hasDerivAt_christoffelFunctional u v w
      (hmix u v w) (hmix v u w) (hmix w u v)
  have hInv : HasDerivAt (fun t ↦ (Gt t x).inverse)
      (-((Gt t₀ x).inverse.comp ((H x).comp (Gt t₀ x).inverse))) t₀ :=
    hasDerivAt_clm_inverse hdG hev
  exact hInv.clm_apply hΦ

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional scales with the metric (CLM-valued form). -/
theorem christoffelFunctional_smul_clm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (c : ℝ)
    (hG : DifferentiableAt ℝ G x) (u v : E) :
    LinearMap.toContinuousLinearMap
        (christoffelFunctional (fun y ↦ c • G y) x u v) =
      c • LinearMap.toContinuousLinearMap
        (christoffelFunctional G x u v) := by
  ext w
  have h := christoffelFunctional_smul_apply c hG u v w
  simpa [smul_eq_mul] using h

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The named `δΓ`**: the variation of the Christoffel symbols at a
metric `G` in the direction `H` — the value the flow-derivative takes. -/
noncomputable def christoffelDeriv (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) : E :=
  (-((G x).inverse.comp ((H x).comp (G x).inverse)))
      (LinearMap.toContinuousLinearMap (christoffelFunctional G x u v))
    + (G x).inverse (LinearMap.toContinuousLinearMap
      (christoffelFunctional H x u v))

/-- The flow-derivative of the closed-form corrector is the named `δΓ`. -/
theorem hasDerivAt_christoffel_flow'
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u v : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀) :
    HasDerivAt (fun t ↦ (Gt t x).inverse
        (LinearMap.toContinuousLinearMap
          (christoffelFunctional (Gt t) x u v)))
      (christoffelDeriv (Gt t₀) H x u v) t₀ :=
  hasDerivAt_christoffel_flow u v hdG hev hmix

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional is symmetric in its two directions, for a
differentiable symmetric metric. -/
theorem christoffelFunctional_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p) (u v : E) :
    christoffelFunctional G x u v = christoffelFunctional G x v u := by
  apply LinearMap.ext
  intro w
  show (1 / 2 : ℝ) * ((fderiv ℝ G x u) v w + (fderiv ℝ G x v) u w
      - (fderiv ℝ G x w) u v) = (1 / 2 : ℝ) *
    ((fderiv ℝ G x v) u w + (fderiv ℝ G x u) v w
      - (fderiv ℝ G x w) v u)
  rw [fderiv_metric_symm G hGd hGsymm w u v]
  ring

/-- **`δΓ` is symmetric** — the variation of a torsion-free connection is
a symmetric 2-tensor, as Hamilton's evolution equations require. -/
theorem christoffelDeriv_symm
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x) (hHd : DifferentiableAt ℝ H x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hHsymm : ∀ (y : E) (p q : E), H y p q = H y q p) (u v : E) :
    christoffelDeriv G H x u v = christoffelDeriv G H x v u := by
  unfold christoffelDeriv
  rw [christoffelFunctional_symm hGd hGsymm u v,
    christoffelFunctional_symm hHd hHsymm u v]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional of a constant metric vanishes. -/
theorem christoffelFunctional_const (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) :
    christoffelFunctional (fun _ : E ↦ G₀) x u v = 0 := by
  apply LinearMap.ext
  intro w
  show (1 / 2 : ℝ) * ((fderiv ℝ (fun _ : E ↦ G₀) x u) v w
      + (fderiv ℝ (fun _ : E ↦ G₀) x v) u w
      - (fderiv ℝ (fun _ : E ↦ G₀) x w) u v) = 0
  rw [fderiv_fun_const]
  simp

/--
**`δΓ` at a flat background**: varying from a constant metric, the
quadratic term dies and `δΓ = G₀⁻¹ Φ_H` — the linearized Christoffel
symbols, the operator at the heart of DeTurck's linearization of the
Ricci flow.
-/
theorem christoffelDeriv_const_base (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) :
    christoffelDeriv (fun _ ↦ G₀) H x u v =
      ContinuousLinearMap.inverse G₀
        (LinearMap.toContinuousLinearMap
          (christoffelFunctional H x u v)) := by
  unfold christoffelDeriv
  rw [christoffelFunctional_const G₀ x u v]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The paired linearized Christoffel symbols**: at a flat background,
`b(δΓ(u,v), w) = Φ_H(u,v)(w)` — the symbol of DeTurck's linearized
operator in its metric pairing.
-/
theorem b_christoffelDeriv_const_base (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbg : ∀ v w : E, b v w = G₀ v w)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v w : E) :
    b (christoffelDeriv (fun _ ↦ G₀) H x u v) w =
      christoffelFunctional H x u v w := by
  rw [christoffelDeriv_const_base G₀ H x u v]
  have hinv := metric_isInvertible (fun _ : E ↦ G₀) (x := x) b hb hbg
  obtain ⟨e, he⟩ := hinv
  have he' : (e : E →L[ℝ] E →L[ℝ] ℝ) = G₀ := he
  rw [← he', ContinuousLinearMap.inverse_equiv]
  -- Pair through the dual identity.
  have hkey : ∀ ρ : E →L[ℝ] ℝ, b (e.symm ρ) w = ρ w := by
    intro ρ
    have happ : e (e.symm ρ) = ρ := e.apply_symm_apply ρ
    have hb_eq : (e (e.symm ρ) : E →L[ℝ] ℝ) w = G₀ (e.symm ρ) w := by
      rw [show (e (e.symm ρ) : E →L[ℝ] ℝ) =
        (e : E →L[ℝ] E →L[ℝ] ℝ) (e.symm ρ) from rfl, he']
    rw [happ] at hb_eq
    rw [hbg]
    exact hb_eq.symm
  exact hkey _

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The covariant Hessian product rule**:
`Hess(fg) = f·Hess g + g·Hess f + df⊗dg + dg⊗df` — the corrector
distributes through the differential, so the classical formula holds on
any metric background.
-/
theorem covariantHessian_mul (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x v w : E) :
    covariantHessian G b hb (fun y ↦ f y * g y) x v w =
      f x * covariantHessian G b hb g x v w
        + g x * covariantHessian G b hb f x v w
        + fderiv ℝ f x v * fderiv ℝ g x w
        + fderiv ℝ g x v * fderiv ℝ f x w := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hA : fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) x =
      f x • fderiv ℝ (fderiv ℝ g) x
        + (fderiv ℝ f x).smulRight (fderiv ℝ g x) :=
    fderiv_smul (hfd x) (hg1 x)
  have hB : fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) x =
      g x • fderiv ℝ (fderiv ℝ f) x
        + (fderiv ℝ g x).smulRight (fderiv ℝ f x) :=
    fderiv_smul (hgd x) (hf1 x)
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ f y * g y)) x =
      (f x • fderiv ℝ (fderiv ℝ g) x
        + (fderiv ℝ f x).smulRight (fderiv ℝ g x))
      + (g x • fderiv ℝ (fderiv ℝ f) x
        + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
    rw [show fderiv ℝ (fun y ↦ f y * g y) =
      fun y ↦ f y • fderiv ℝ g y + g y • fderiv ℝ f y from
      funext fun y ↦ fderiv_mul (hfd y) (hgd y)]
    refine Eq.trans ((((hfd x).smul (hg1 x)).hasFDerivAt.add
      ((hgd x).smul (hf1 x)).hasFDerivAt).fderiv) ?_
    rw [show fderiv ℝ (f • fderiv ℝ g) x =
      fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) x from rfl,
      show fderiv ℝ (g • fderiv ℝ f) x =
      fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) x from rfl, hA, hB]
  have hdmul : fderiv ℝ (fun y ↦ f y * g y) x =
      f x • fderiv ℝ g x + g x • fderiv ℝ f x := fderiv_mul (hfd x) (hgd x)
  unfold covariantHessian
  rw [hd2, hdmul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The covariant Hessian chain rule**:
`Hess(φ∘f) = φ'(f)·Hess f + φ''(f)·df⊗df` on any metric background — the
tensorial form behind every soliton-potential computation.
-/
theorem covariantHessian_comp (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (b : Π x : E, LinearMap.BilinForm ℝ E)
    (hb : ∀ x, (b x).Nondegenerate)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (x v w : E) :
    covariantHessian G b hb (fun y ↦ φ (f y)) x v w =
      deriv φ (f x) * covariantHessian G b hb f x v w
        + deriv (deriv φ) (f x) * (fderiv ℝ f x v * fderiv ℝ f x w) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hφ1 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  have hchain : ∀ (ψ : ℝ → ℝ), Differentiable ℝ ψ → ∀ y : E,
      fderiv ℝ (fun z ↦ ψ (f z)) y = deriv ψ (f y) • fderiv ℝ f y := by
    intro ψ hψ y
    rw [show (fun z ↦ ψ (f z)) = ψ ∘ f from rfl,
      fderiv_comp y (hψ (f y)) (hfd y)]
    ext u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show fderiv ℝ ψ (f y) (fderiv ℝ f y u) =
      (fderiv ℝ f y u) • deriv ψ (f y) from by
        rw [← fderiv_deriv]
        simp [mul_comm]]
    simp [smul_eq_mul, mul_comm]
  have hcdiff : DifferentiableAt ℝ (fun y ↦ deriv φ (f y)) x :=
    (hφ1 (f x)).comp x (hfd x)
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ φ (f y))) x =
      deriv φ (f x) • fderiv ℝ (fderiv ℝ f) x
        + (deriv (deriv φ) (f x) • fderiv ℝ f x).smulRight
          (fderiv ℝ f x) := by
    rw [show fderiv ℝ (fun y ↦ φ (f y)) =
      fun y ↦ deriv φ (f y) • fderiv ℝ f y from funext (hchain φ hφd)]
    refine Eq.trans (fderiv_smul hcdiff (hf1 x)) ?_
    have hfc : fderiv ℝ (fun z ↦ deriv φ (f z)) x =
        deriv (deriv φ) (f x) • fderiv ℝ f x := hchain (deriv φ) hφ1 x
    rw [hfc]
  have hd1 : fderiv ℝ (fun y ↦ φ (f y)) x =
      deriv φ (f x) • fderiv ℝ f x := hchain φ hφd x
  unfold covariantHessian
  rw [hd2, hd1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The differential of the gradient-square**:
`d|∇f|²(v) = 2·Hess f(v, ∇f)` (constant metric) — the first component of
the Bochner formula `Δ|∇f|² = 2|Hess f|² + 2⟨∇f, ∇Δf⟩ + 2Ric(∇f,∇f)`.
-/
theorem fderiv_gradient_sq (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    fderiv ℝ (fun y ↦ b (metricGradient b hb f y)
        (metricGradient b hb f y)) x v =
      2 * fderiv ℝ (fderiv ℝ f) x v (metricGradient b hb f x) := by
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- The gradient path is a fixed CLM applied to `Df`.
  set Lc : (E →L[ℝ] ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap
    ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
      (LinearMap.toContinuousLinearMap.symm :
        (E →L[ℝ] ℝ) ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ)).toLinearMap) with hLc
  have hgrad : (fun y ↦ metricGradient b hb f y) =
      fun y ↦ Lc (fderiv ℝ f y) := rfl
  have hgd : DifferentiableAt ℝ (fun y ↦ metricGradient b hb f y) x := by
    rw [hgrad]
    exact (Lc.differentiableAt).comp x (hf1 x)
  have hdgrad : fderiv ℝ (fun y ↦ metricGradient b hb f y) x =
      Lc.comp (fderiv ℝ (fderiv ℝ f) x) := by
    rw [hgrad]
    exact (Lc.hasFDerivAt.comp x (hf1 x).hasFDerivAt).fderiv
  -- The pairing of `Lc ψ` against anything is `ψ`-evaluation.
  have hpair : ∀ (ψ : E →L[ℝ] ℝ) (u : E), b (Lc ψ) u = ψ u := by
    intro ψ u
    have h := congrArg (fun ρ : Module.Dual ℝ E ↦ ρ u)
      (LinearEquiv.apply_symm_apply (LinearMap.BilinForm.toDual b hb)
        (LinearMap.toContinuousLinearMap.symm ψ))
    simp only [LinearMap.BilinForm.toDual_def] at h
    exact h
  -- Differentiate the diagonal pairing.
  have hquad : fderiv ℝ (fun y ↦ b (metricGradient b hb f y)
      (metricGradient b hb f y)) x v =
      b (metricGradient b hb f x)
        (fderiv ℝ (fun y ↦ metricGradient b hb f y) x v)
      + b (fderiv ℝ (fun y ↦ metricGradient b hb f y) x v)
        (metricGradient b hb f x) := by
    set bC : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ b) with hbC
    have hfn : (fun y ↦ b (metricGradient b hb f y)
        (metricGradient b hb f y)) =
        fun y ↦ bC (metricGradient b hb f y)
          (metricGradient b hb f y) := rfl
    rw [hfn]
    have hcl : DifferentiableAt ℝ
        (fun y ↦ bC (metricGradient b hb f y)) x :=
      (bC.differentiableAt).comp x hgd
    have h := (fderiv_clm_apply hcl hgd)
    have h2 := congrFun (congrArg DFunLike.coe h) v
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
      at h2
    rw [h2]
    have hdc : fderiv ℝ (fun y ↦ bC (metricGradient b hb f y)) x =
        bC.comp (fderiv ℝ (fun y ↦ metricGradient b hb f y) x) :=
      (bC.hasFDerivAt.comp x hgd.hasFDerivAt).fderiv
    rw [hdc]
    rfl
  rw [hquad, hdgrad]
  -- Collapse both terms with the pairing identity and symmetry.
  have hsy := hbs.eq (metricGradient b hb f x)
    (Lc.comp (fderiv ℝ (fderiv ℝ f) x) v)
  simp only [RingHom.id_apply] at hsy
  rw [hsy]
  rw [show b (Lc.comp (fderiv ℝ (fderiv ℝ f) x) v)
      (metricGradient b hb f x) =
    (fderiv ℝ (fderiv ℝ f) x v) (metricGradient b hb f x) from by
      rw [show (Lc.comp (fderiv ℝ (fderiv ℝ f) x)) v =
        Lc ((fderiv ℝ (fderiv ℝ f) x) v) from rfl]
      exact hpair _ _]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The musical isomorphism `♯`: functionals to vectors through the
metric. -/
noncomputable def sharp (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (ψ : E →L[ℝ] ℝ) : E :=
  (LinearMap.BilinForm.toDual b hb).symm
    (LinearMap.toContinuousLinearMap.symm ψ)

/-- The defining property of `♯`: `b(ψ♯, v) = ψ(v)`. -/
theorem b_sharp (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (ψ : E →L[ℝ] ℝ) (v : E) : b (sharp b hb ψ) v = ψ v := by
  have h := congrArg (fun ρ : Module.Dual ℝ E ↦ ρ v)
    (LinearEquiv.apply_symm_apply (LinearMap.BilinForm.toDual b hb)
      (LinearMap.toContinuousLinearMap.symm ψ))
  simp only [LinearMap.BilinForm.toDual_def] at h
  exact h

/-- The gradient is the sharp of the differential. -/
theorem metricGradient_eq_sharp (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (f : E → ℝ) (x : E) :
    metricGradient b hb f x = sharp b hb (fderiv ℝ f x) := rfl

/--
**The gradient of the gradient-square**: `∇|∇f|² = 2·(Hess f(·,∇f))♯` —
the vector form of the first Bochner component.
-/
theorem metricGradient_gradient_sq (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    metricGradient b hb (fun y ↦ b (metricGradient b hb f y)
        (metricGradient b hb f y)) x =
      (2 : ℝ) • sharp b hb
        ((fderiv ℝ (fderiv ℝ f) x).flip (metricGradient b hb f x)) := by
  -- Identify through nondegeneracy.
  have hkey : ∀ v : E,
      b (metricGradient b hb (fun y ↦ b (metricGradient b hb f y)
        (metricGradient b hb f y)) x) v =
      b ((2 : ℝ) • sharp b hb
        ((fderiv ℝ (fderiv ℝ f) x).flip (metricGradient b hb f x))) v := by
    intro v
    rw [b_metricGradient, fderiv_gradient_sq b hb hbs hf x v]
    rw [map_smul, LinearMap.smul_apply, b_sharp, smul_eq_mul,
      ContinuousLinearMap.flip_apply]
  have hzero : ∀ v : E,
      b (metricGradient b hb (fun y ↦ b (metricGradient b hb f y)
          (metricGradient b hb f y)) x
        - (2 : ℝ) • sharp b hb ((fderiv ℝ (fderiv ℝ f) x).flip
          (metricGradient b hb f x))) v = 0 := by
    intro v
    rw [map_sub, LinearMap.sub_apply, hkey v, sub_self]
  exact sub_eq_zero.mp (hb.1 _ hzero)

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The `(1,1)`-Hessian: the Hessian with one index raised — the
endomorphism whose trace is the Laplacian and whose square's trace is
`|Hess f|²`. -/
noncomputable def hessianOperator (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (f : E → ℝ) (x : E) : E →ₗ[ℝ] E :=
  (LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
    (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
      ((fderiv ℝ (fderiv ℝ f) x).toLinearMap))

/-- The Laplacian is the trace of the `(1,1)`-Hessian. -/
theorem modelLaplacian_eq_trace_hessianOperator
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (f : E → ℝ) (x : E) :
    modelLaplacian b hb f x =
      LinearMap.trace ℝ E (hessianOperator b hb f x) := rfl

/-- **`|Hess f|²`**: the squared norm of the Hessian — the trace of the
squared `(1,1)`-Hessian, the positive term of the Bochner formula. -/
noncomputable def hessianNormSq (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (f : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E
    (hessianOperator b hb f x ∘ₗ hessianOperator b hb f x)

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The pairing identity of the `(1,1)`-Hessian:
`b(Hess♯ v, w) = Hess(v,w)`. -/
theorem b_hessianOperator (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (f : E → ℝ) (x v w : E) :
    b (hessianOperator b hb f x v) w =
      fderiv ℝ (fderiv ℝ f) x v w := by
  have h := congrArg (fun ρ : Module.Dual ℝ E ↦ ρ w)
    (LinearEquiv.apply_symm_apply (LinearMap.BilinForm.toDual b hb)
      (LinearMap.toContinuousLinearMap.symm
        ((fderiv ℝ (fderiv ℝ f) x) v)))
  simp only [LinearMap.BilinForm.toDual_def] at h
  exact h

/--
**`|Hess f|² ≥ 0`**: the trace of the squared `(1,1)`-Hessian is
nonnegative for a positive-definite metric — by self-adjointness (Schwarz)
in a `b`-orthogonal basis. The sign that makes the Bochner formula yield
gradient estimates.
-/
theorem hessianNormSq_nonneg (b : LinearMap.BilinForm ℝ E)
    (hb : b.Nondegenerate) (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    0 ≤ hessianNormSq b hb f x := by
  obtain ⟨v, hortho⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := b) hbs
  set A := hessianOperator b hb f x with hA
  -- Self-adjointness from Schwarz symmetry.
  have hselfadj : ∀ p q : E, b (A p) q = b p (A q) := by
    intro p q
    rw [b_hessianOperator]
    have hsy := hbs.eq p (A q)
    simp only [RingHom.id_apply] at hsy
    rw [hsy, b_hessianOperator]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) p q
  unfold hessianNormSq
  rw [← hA, LinearMap.trace_eq_matrix_trace ℝ v, Matrix.trace]
  apply Finset.sum_nonneg
  intro i _
  have hvi : v i ≠ 0 := v.ne_zero i
  have hbvi : 0 < b (v i) (v i) := hbpos (v i) hvi
  -- The diagonal entry of `A²` is `b(A vᵢ, A vᵢ)/b(vᵢ,vᵢ) ≥ 0`.
  have hexpand : b ((A ∘ₗ A) (v i)) (v i) =
      (LinearMap.toMatrix v v (A ∘ₗ A) i i) * b (v i) (v i) := by
    conv_lhs => rw [← v.sum_repr ((A ∘ₗ A) (v i))]
    have hsum : b (∑ j, v.repr ((A ∘ₗ A) (v i)) j • v j) (v i) =
        ∑ j, v.repr ((A ∘ₗ A) (v i)) j * b (v j) (v i) := by
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      simp [smul_eq_mul]
    rw [hsum]
    rw [Finset.sum_eq_single i]
    · rw [LinearMap.toMatrix_apply]
    · intro j _ hji
      rw [hortho hji]
      ring_nf
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hAA : b ((A ∘ₗ A) (v i)) (v i) = b (A (v i)) (A (v i)) := by
    rw [show (A ∘ₗ A) (v i) = A (A (v i)) from rfl]
    rw [hselfadj (A (v i)) (v i)]
  have hAvnn : 0 ≤ b (A (v i)) (A (v i)) := by
    by_cases hz : A (v i) = 0
    · rw [hz]
      simp
    · exact le_of_lt (hbpos _ hz)
  have := hexpand.symm.trans hAA
  have hdiag : LinearMap.toMatrix v v (A ∘ₗ A) i i =
      b (A (v i)) (A (v i)) / b (v i) (v i) := by
    field_simp at this ⊢
    linarith
  rw [Matrix.diag_apply, hdiag]
  positivity

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Cauchy–Schwarz for a positive-definite form**:
`b(u,w)² ≤ b(u,u)·b(w,w)` — by the discriminant of the quadratic
`t ↦ b(u − tw, u − tw)`. -/
theorem bilin_cauchy_schwarz (b : LinearMap.BilinForm ℝ E)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v) (u w : E) :
    b u w ^ 2 ≤ b u u * b w w := by
  by_cases hw : w = 0
  · simp [hw]
  · have hww : 0 < b w w := hbpos w hw
    set t := b u w / b w w with ht
    have hquad : 0 ≤ b (u - t • w) (u - t • w) := by
      by_cases hz : u - t • w = 0
      · rw [hz]
        simp
      · exact le_of_lt (hbpos _ hz)
    have hexpand : b (u - t • w) (u - t • w) =
        b u u - 2 * t * b u w + t ^ 2 * b w w := by
      have hsy := hbs.eq w u
      simp only [RingHom.id_apply] at hsy
      simp only [map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [← hsy]
      ring
    rw [hexpand, ht] at hquad
    -- `0 ≤ buu − 2(buw²/bww) + (buw²/bww) = buu − buw²/bww`.
    have hkey : b u w ^ 2 / b w w ≤ b u u := by
      have hq2 : 0 ≤ (b u u - 2 * (b u w / b w w) * b u w
          + (b u w / b w w) ^ 2 * b w w) * b w w :=
        mul_nonneg hquad (le_of_lt hww)
      have hq3 : 0 ≤ b u u * b w w - b u w ^ 2 := by
        have hexp : (b u u - 2 * (b u w / b w w) * b u w
            + (b u w / b w w) ^ 2 * b w w) * b w w =
            b u u * b w w - b u w ^ 2 := by
          field_simp
          ring
        linarith [hexp ▸ hq2]
      rw [div_le_iff₀ hww]
      linarith
    calc b u w ^ 2 = (b u w ^ 2 / b w w) * b w w := by
          field_simp
      _ ≤ b u u * b w w := by
          apply mul_le_mul_of_nonneg_right hkey (le_of_lt hww)

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The trace Cauchy–Schwarz inequality**: for a `b`-self-adjoint operator,
`(tr A)² ≤ n · tr(A²)` — applied to the Hessian this is
`(Δf)² ≤ n|Hess f|²`, and applied to the Ricci endomorphism it is
`R² ≤ n|Ric|²`: the inequality that turns the scalar-curvature evolution
into the Riccati supersolution behind finite-time singularities.
-/
theorem trace_sq_le_card_mul_trace_comp_self
    (b : LinearMap.BilinForm ℝ E) (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    (A : E →ₗ[ℝ] E) (hsa : ∀ p q : E, b (A p) q = b p (A q)) :
    (LinearMap.trace ℝ E A) ^ 2 ≤
      Module.finrank ℝ E * LinearMap.trace ℝ E (A ∘ₗ A) := by
  obtain ⟨v, hortho⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := b) hbs
  -- Diagonal extraction in the orthogonal basis.
  have hdiag : ∀ (B : E →ₗ[ℝ] E) (i : Fin (Module.finrank ℝ E)),
      LinearMap.toMatrix v v B i i =
        b (B (v i)) (v i) / b (v i) (v i) := by
    intro B i
    have hvi : v i ≠ 0 := v.ne_zero i
    have hbvi : 0 < b (v i) (v i) := hbpos (v i) hvi
    have hexpand : b (B (v i)) (v i) =
        (LinearMap.toMatrix v v B i i) * b (v i) (v i) := by
      conv_lhs => rw [← v.sum_repr (B (v i))]
      have hsum : b (∑ j, v.repr (B (v i)) j • v j) (v i) =
          ∑ j, v.repr (B (v i)) j * b (v j) (v i) := by
        rw [map_sum, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        simp [smul_eq_mul]
      rw [hsum]
      rw [Finset.sum_eq_single i]
      · rw [LinearMap.toMatrix_apply]
      · intro j _ hji
        rw [hortho hji]
        ring_nf
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [eq_div_iff (ne_of_gt hbvi)]
    linarith [hexpand]
  -- Pointwise: `dᵢ² ≤ eᵢ` by Cauchy–Schwarz.
  have hpt : ∀ i, (LinearMap.toMatrix v v A i i) ^ 2 ≤
      LinearMap.toMatrix v v (A ∘ₗ A) i i := by
    intro i
    have hvi : v i ≠ 0 := v.ne_zero i
    have hbvi : 0 < b (v i) (v i) := hbpos (v i) hvi
    rw [hdiag A i, hdiag (A ∘ₗ A) i]
    have hAA : b ((A ∘ₗ A) (v i)) (v i) = b (A (v i)) (A (v i)) := by
      rw [show (A ∘ₗ A) (v i) = A (A (v i)) from rfl,
        hsa (A (v i)) (v i)]
    rw [hAA]
    -- Cauchy–Schwarz on the numerator.
    have hcs := bilin_cauchy_schwarz b hbs hbpos (A (v i)) (v i)
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity) hbvi]
    have hsy := hbs.eq (A (v i)) (v i)
    simp only [RingHom.id_apply] at hsy
    calc b (A (v i)) (v i) ^ 2 * b (v i) (v i)
        ≤ (b (A (v i)) (A (v i)) * b (v i) (v i)) * b (v i) (v i) := by
          nlinarith [hcs, sq_nonneg (b (A (v i)) (v i))]
      _ = b (A (v i)) (A (v i)) * b (v i) (v i) ^ 2 := by ring
  -- Sum and apply the scalar Chebyshev bound.
  rw [LinearMap.trace_eq_matrix_trace ℝ v A,
    LinearMap.trace_eq_matrix_trace ℝ v (A ∘ₗ A), Matrix.trace,
    Matrix.trace]
  calc (∑ i, (LinearMap.toMatrix v v A).diag i) ^ 2
      ≤ (Finset.univ.card : ℝ) *
        ∑ i, ((LinearMap.toMatrix v v A).diag i) ^ 2 := by
        have hcheb : (∑ i : Fin (Module.finrank ℝ E),
            (LinearMap.toMatrix v v A).diag i) ^ 2 ≤
            ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ)
              * ∑ i : Fin (Module.finrank ℝ E),
                ((LinearMap.toMatrix v v A).diag i) ^ 2 := by
          exact sq_sum_le_card_mul_sum_sq
        exact hcheb
    _ ≤ Module.finrank ℝ E *
        ∑ i, (LinearMap.toMatrix v v (A ∘ₗ A)).diag i := by
        have hcard : (((Finset.univ :
              Finset (Fin (Module.finrank ℝ E))).card : ℕ) : ℝ) =
            (Module.finrank ℝ E : ℝ) := by
          simp
        rw [hcard]
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        exact hpt i

end RicciFlow

namespace RicciFlow

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The parabolic minimum principle with variable coefficient** (strict):
the touching-point argument kills the `c·u` term regardless of `c`, so the
strict principle holds for arbitrary space-time-dependent coefficients —
the form needed for Hamilton's nonlinear comparison arguments.
-/
theorem parabolic_min_principle_strict_var
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {u u' : ℝ → E → ℝ} {c : ℝ → E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {T : ℝ}
    (hu_cont : Continuous ↿u)
    (hud : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u t))
    (hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (u t) x + c t x * u t x < u' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (u t) K x → IsLocalMin (u t) x)
    (h0 : ∀ x ∈ K, 0 < u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, 0 < u t x := by
  by_contra hviol
  push_neg at hviol
  obtain ⟨t₁, ht₁, x₁, hx₁, hux₁⟩ := hviol
  set m : ℝ → ℝ := fun t ↦ sInf (u t '' K) with hm
  have hmcont : Continuous m := hK.continuous_sInf hu_cont
  have hattain : ∀ t, ∃ x ∈ K, IsMinOn (u t) K x ∧ m t = u t x := by
    intro t
    obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hKne
      ((hu_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    refine ⟨x, hxK, hxmin, le_antisymm ?_ ?_⟩
    · exact csInf_le ⟨u t x, fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz⟩
        ⟨x, hxK, rfl⟩
    · exact le_csInf ((hKne.image (u t))) fun y ⟨z, hz, hzy⟩ ↦
        hzy ▸ hxmin hz
  have hmle : ∀ t (x : E), x ∈ K → m t ≤ u t x := by
    intro t x hx
    exact csInf_le ⟨m t, fun y ⟨z, hz, hzy⟩ ↦ by
      obtain ⟨x', hx', hmin', hmx'⟩ := hattain t
      rw [← hzy, hmx']
      exact hmin' hz⟩ ⟨x, hx, rfl⟩
  have hm0 : 0 < m 0 := by
    obtain ⟨x, hxK, _, hmx⟩ := hattain 0
    rw [hmx]
    exact h0 x hxK
  have hmbad : ∃ t ∈ Icc (0 : ℝ) T, m t ≤ 0 :=
    ⟨t₁, ht₁, le_trans (hmle t₁ x₁ hx₁) hux₁⟩
  obtain ⟨t₀, ht₀, hmt₀, hbefore⟩ :=
    exists_first_zero (hmcont.continuousOn) hm0 hmbad
  have ht₀Icc : t₀ ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht₀.1, ht₀.2⟩
  obtain ⟨x₀, hx₀K, hx₀min, hmx₀⟩ := hattain t₀
  have hux₀ : u t₀ x₀ = 0 := by rw [← hmx₀, hmt₀]
  have hder := hud x₀ hx₀K t₀ ht₀Icc
  have hleft : u' t₀ x₀ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hslope := hasDerivAt_iff_tendsto_slope.mp hder
    have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ,
        0 < slope (fun s ↦ u s x₀) t₀ s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hlt : ∀ᶠ s in nhdsWithin t₀ (Iio t₀),
        0 < slope (fun s ↦ u s x₀) t₀ s := by
      apply hev.filter_mono
      apply nhdsWithin_mono
      intro s hs
      exact ne_of_lt hs
    have hIoo : ∀ᶠ s in nhdsWithin t₀ (Iio t₀), s ∈ Ioo (0 : ℝ) t₀ :=
      Filter.eventually_of_mem (Ioo_mem_nhdsLT ht₀.1) fun s hs ↦ hs
    obtain ⟨s, hsl, hsIoo⟩ := (hlt.and hIoo).exists
    have hneg : u s x₀ < 0 := by
      have hde : slope (fun s ↦ u s x₀) t₀ s =
          (u s x₀ - u t₀ x₀) / (s - t₀) := by
        rw [slope_def_field]
      rw [hde, hux₀, sub_zero] at hsl
      have hst : s - t₀ < 0 := by linarith [hsIoo.2]
      by_contra hge
      push_neg at hge
      have : u s x₀ / (s - t₀) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hge
        (le_of_lt hst)
      linarith
    have hmpos := hbefore s ⟨le_of_lt hsIoo.1, hsIoo.2⟩
    have := hmle s x₀ hx₀K
    linarith
  have hloc := hmin_int t₀ ht₀Icc x₀ hx₀K hx₀min
  have hsup := hsuper t₀ ht₀Icc x₀ hx₀K
  have hlap := modelLaplacian_nonneg_of_isLocalMin b hb hbs hbpos
    (hspace t₀ ht₀Icc) hloc
  rw [hux₀] at hsup
  simp only [mul_zero] at hsup
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The parabolic minimum principle, variable coefficient, non-strict**: for
a coefficient bounded above by `M`, the `ε e^{(M+1)t}` slack restores
strictness — nonnegative initial data under
`∂u/∂t ≥ Δu + c·u` stays nonnegative.
-/
theorem parabolic_min_principle_var
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {u u' : ℝ → E → ℝ} {c : ℝ → E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {T M : ℝ}
    (hcM : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, c t x ≤ M)
    (hu_cont : Continuous ↿u)
    (hud : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u t))
    (hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (u t) x + c t x * u t x ≤ u' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (u t) K x → IsLocalMin (u t) x)
    (h0 : ∀ x ∈ K, 0 ≤ u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, 0 ≤ u t x := by
  intro t ht x hx
  by_contra hneg
  push_neg at hneg
  set M' : ℝ := max M 0 + 1 with hM'
  set ε : ℝ := -u t x / (2 * Real.exp (M' * t)) with hε
  have hexp : (0 : ℝ) < Real.exp (M' * t) := Real.exp_pos _
  have hεpos : 0 < ε := by
    rw [hε]
    apply div_pos (by linarith) (by positivity)
  have hvpos := parabolic_min_principle_strict_var b hb hbs hbpos
    (u := fun s y ↦ u s y + ε * Real.exp (M' * s))
    (u' := fun s y ↦ u' s y + ε * M' * Real.exp (M' * s))
    (c := c) hK hKne (T := T)
    (by
      apply Continuous.add hu_cont
      exact (continuous_const.mul ((continuous_const.mul
        continuous_fst).rexp)).comp (continuous_id))
    (by
      intro y hy s hs
      have h1 := hud y hy s hs
      have h2 : HasDerivAt (fun r ↦ ε * Real.exp (M' * r))
          (ε * M' * Real.exp (M' * s)) s := by
        have h3 := (((hasDerivAt_id s).const_mul M').exp).const_mul ε
        simp only [id_eq] at h3
        convert h3 using 1
        ring
      simpa using h1.add h2)
    (by
      intro s hs
      exact (hspace s hs).add contDiff_const)
    (by
      intro s hs y hy
      have hsup := hsuper s hs y hy
      have hlap : modelLaplacian b hb
          (fun z ↦ u s z + ε * Real.exp (M' * s)) y =
          modelLaplacian b hb (u s) y :=
        modelLaplacian_add_const b hb (u s) _ y
      simp only
      rw [hlap]
      have hcy := hcM s hs y hy
      have hM1 : c s y < M' := by
        rw [hM']
        have : M ≤ max M 0 := le_max_left M 0
        linarith
      have heps : 0 < ε * Real.exp (M' * s) := by positivity
      nlinarith [mul_lt_mul_of_pos_right hM1 heps])
    (by
      intro s hs y hy
      intro hminv
      have hminu : IsMinOn (u s) K y := by
        intro z hz
        have := hminv hz
        simpa using this
      have hloc := hmin_int s hs y hy hminu
      have : IsLocalMin (fun z ↦ u s z + ε * Real.exp (M' * s)) y :=
        hloc.add isMinFilter_const
      simpa using this)
    (by
      intro y hy
      have := h0 y hy
      positivity)
  have := hvpos t ht x hx
  simp only at this
  rw [hε] at this
  have hne : Real.exp (M' * t) ≠ 0 := ne_of_gt hexp
  field_simp at this
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Hamilton's scalar comparison**: a quantity evolving by
`∂R/∂t ≥ ΔR + aR²` with `R(0) ≥ m₀ > 0` stays above the exact Riccati
barrier `m₀/(1 − a m₀ t)` — the nonlinear comparison whose blow-up forces
the finite-time singularity, conditional only on the evolution inequality
(the link awaiting the curvature evolution equation).
-/
theorem hamilton_scalar_lower_bound
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {R R' : ℝ → E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {T a m₀ B : ℝ}
    (ha : 0 < a) (hm₀ : 0 < m₀) (hT0 : 0 ≤ T) (hT : a * m₀ * T < 1)
    (hR_cont : Continuous ↿R)
    (hRd : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (R t))
    (hevol : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (R t) x + a * (R t x) ^ 2 ≤ R' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (R t) K x → IsLocalMin (R t) x)
    (hRB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, R t x ≤ B)
    (h0 : ∀ x ∈ K, m₀ ≤ R 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      m₀ / (1 - a * m₀ * t) ≤ R t x := by
  -- A globally continuous clamp of the barrier, agreeing on `[0, T]`.
  set δ : ℝ := (1 - a * m₀ * T) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set φ : ℝ → ℝ := fun t ↦ m₀ / max (1 - a * m₀ * t) δ with hφ
  have hφeq : ∀ t ∈ Icc (0 : ℝ) T,
      φ t = m₀ / (1 - a * m₀ * t) := by
    intro t ht
    rw [hφ]
    simp only
    congr 1
    apply max_eq_left
    have h1 : a * m₀ * t ≤ a * m₀ * T := by
      apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
    rw [hδ]
    linarith
  -- The barrier's derivative and bounds on `[0, T]`.
  have hden : ∀ t ∈ Icc (0 : ℝ) T, 0 < 1 - a * m₀ * t := by
    intro t ht
    have h1 : a * m₀ * t ≤ a * m₀ * T := by
      apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith
  have hφd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt φ (a * (φ t) ^ 2) t := by
    intro t ht
    have hd := hden t ht
    have hf : HasDerivAt (fun s ↦ 1 - a * m₀ * s) (-(a * m₀)) t := by
      simpa using ((hasDerivAt_id t).const_mul (a * m₀)).const_sub 1
    have hinv : HasDerivAt (fun s ↦ (1 - a * m₀ * s)⁻¹)
        (a * m₀ / (1 - a * m₀ * t) ^ 2) t := by
      have h2 := hf.inv (ne_of_gt hd)
      convert h2 using 1
      field_simp
    have hexact := hinv.const_mul m₀
    -- Transfer to the clamp through eventual equality.
    have hopen : ∀ᶠ s in nhds t, φ s = m₀ * (1 - a * m₀ * s)⁻¹ := by
      have hcont : Continuous (fun s ↦ 1 - a * m₀ * s) := by
        continuity
      have hδlt : δ < 1 - a * m₀ * t := by
        have h1 : a * m₀ * t ≤ a * m₀ * T := by
          apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
        rw [hδ]
        linarith
      have hev : ∀ᶠ s in nhds t, δ < 1 - a * m₀ * s :=
        hcont.continuousAt.eventually_const_lt hδlt
      filter_upwards [hev] with s hs
      rw [hφ]
      simp only
      rw [max_eq_left (le_of_lt hs), div_eq_mul_inv]
    have hres : HasDerivAt φ (m₀ * (a * m₀ / (1 - a * m₀ * t) ^ 2)) t :=
      hexact.congr_of_eventuallyEq hopen
    convert hres using 1
    rw [hφeq t ht]
    field_simp
  have hφmono : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ φ T := by
    intro t ht
    rw [hφeq t ht, hφeq T ⟨hT0, le_refl T⟩]
    apply div_le_div_of_nonneg_left (le_of_lt hm₀) (hden T ⟨hT0, le_refl T⟩)
    have : a * m₀ * t ≤ a * m₀ * T := by
      apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith
  have hφpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < φ t := by
    intro t ht
    rw [hφeq t ht]
    exact div_pos hm₀ (hden t ht)
  -- Apply the variable-coefficient principle to `u := R − φ`.
  have hkey := parabolic_min_principle_var b hb hbs hbpos
    (u := fun t x ↦ R t x - φ t)
    (u' := fun t x ↦ R' t x - a * (φ t) ^ 2)
    (c := fun t x ↦ a * (R t x + φ t))
    hK hKne (T := T) (M := a * (B + φ T))
    (by
      intro t ht x hx
      have h1 := hRB t ht x hx
      have h2 := hφmono t ht
      nlinarith)
    (by
      apply hR_cont.sub
      have hφcont : Continuous φ := by
        rw [hφ]
        apply Continuous.div continuous_const
        · exact (Continuous.max (by continuity) continuous_const)
        · intro s
          have : δ ≤ max (1 - a * m₀ * s) δ := le_max_right _ _
          intro hzero
          rw [hzero] at this
          linarith
      exact hφcont.comp continuous_fst)
    (by
      intro x hx t ht
      exact (hRd x hx t ht).sub (hφd t ht))
    (by
      intro t ht
      exact (hspace t ht).sub contDiff_const)
    (by
      intro t ht x hx
      have hev := hevol t ht x hx
      have hlap : modelLaplacian b hb (fun y ↦ R t y - φ t) x =
          modelLaplacian b hb (R t) x := by
        rw [show (fun y ↦ R t y - φ t) = fun y ↦ R t y + (-(φ t))
          from by funext y; ring]
        exact modelLaplacian_add_const b hb (R t) _ x
      rw [hlap]
      nlinarith [hev])
    (by
      intro t ht x hx hmin
      have hminR : IsMinOn (R t) K x := by
        intro z hz
        have := hmin hz
        simpa using this
      have hloc := hmin_int t ht x hx hminR
      have : IsLocalMin (fun z ↦ R t z + (-(φ t))) x :=
        hloc.add isMinFilter_const
      simpa [sub_eq_add_neg] using this)
    (by
      intro x hx
      have h00 := h0 x hx
      have hφ0 : φ 0 = m₀ := by
        rw [hφeq 0 ⟨le_refl 0, hT0⟩]
        simp
      simp only
      rw [hφ0]
      linarith)
  intro t ht x hx
  have hfin := hkey t ht x hx
  simp only at hfin
  rw [← hφeq t ht]
  linarith

namespace RicciFlow

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Hamilton's finite-time singularity** (conditional form): a bounded
quantity evolving by `∂R/∂t ≥ ΔR + aR²` with initial minimum `m₀ > 0` on
a compact domain cannot persist to time `1/(a m₀)` — the Riccati barrier
outruns any bound. The singularity theorem of Ricci flow, formal modulo
the evolution equation.
-/
theorem hamilton_finite_time_singularity
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    {R R' : ℝ → E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {T a m₀ B : ℝ}
    (ha : 0 < a) (hm₀ : 0 < m₀) (hT0 : 0 ≤ T)
    (hR_cont : Continuous ↿R)
    (hRd : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (R t))
    (hevol : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (R t) x + a * (R t x) ^ 2 ≤ R' t x)
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (R t) K x → IsLocalMin (R t) x)
    (hRB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, R t x ≤ B)
    (h0 : ∀ x ∈ K, m₀ ≤ R 0 x) :
    T < 1 / (a * m₀) := by
  by_contra hge
  push_neg at hge
  -- A time where the barrier exceeds the bound.
  set B' : ℝ := max B m₀ with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le hm₀ (le_max_right B m₀)
  set t₁ : ℝ := (1 - m₀ / (2 * B')) / (a * m₀) with ht₁
  have hm2B : m₀ / (2 * B') ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : m₀ ≤ B' := le_max_right B m₀
    linarith
  have hm2Bpos : 0 < m₀ / (2 * B') := by positivity
  have ht₁0 : 0 ≤ t₁ := by
    rw [ht₁]
    apply div_nonneg _ (by positivity)
    linarith
  have ht₁T : t₁ ≤ T := by
    rw [ht₁]
    calc (1 - m₀ / (2 * B')) / (a * m₀) ≤ 1 / (a * m₀) := by
          gcongr
          linarith
      _ ≤ T := hge
  have hsub : Icc (0 : ℝ) t₁ ⊆ Icc (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans ht₁T⟩
  -- The barrier condition on `[0, t₁]`.
  have hbar : a * m₀ * t₁ < 1 := by
    rw [ht₁]
    have hne : a * m₀ ≠ 0 := by positivity
    field_simp
    linarith
  -- Apply the comparison on `[0, t₁]`.
  have hcomp := hamilton_scalar_lower_bound b hb hbs hbpos
    (R := R) (R' := R') hK hKne (T := t₁) (a := a) (m₀ := m₀) (B := B)
    ha hm₀ ht₁0 hbar hR_cont
    (fun x hx t ht ↦ hRd x hx t (hsub ht))
    (fun t ht ↦ hspace t (hsub ht))
    (fun t ht x hx ↦ hevol t (hsub ht) x hx)
    (fun t ht x hx ↦ hmin_int t (hsub ht) x hx)
    (fun t ht x hx ↦ hRB t (hsub ht) x hx)
    h0
  -- At `t₁` the barrier equals `2B'`, exceeding the bound.
  obtain ⟨x₀, hx₀⟩ := hKne
  have hval := hcomp t₁ ⟨ht₁0, le_refl t₁⟩ x₀ hx₀
  have hφt₁ : m₀ / (1 - a * m₀ * t₁) = 2 * B' := by
    rw [ht₁]
    have hne : a * m₀ ≠ 0 := by positivity
    have hBne : (2 * B') ≠ 0 := by positivity
    field_simp
    rw [show (2 * B' - (2 * B' - m₀)) = m₀ from by ring,
      div_self (ne_of_gt hm₀)]
  rw [hφt₁] at hval
  have hRb := hRB t₁ ⟨ht₁0, ht₁T⟩ x₀ hx₀
  have hBB' : B ≤ B' := le_max_left B m₀
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Hamilton's singularity theorem from the evolution equation**: if the
scalar curvature evolves by `∂R/∂t = ΔR + 2·tr(Rc²)` with `Rc` the
`b`-self-adjoint Ricci endomorphism of trace `R`, then the trace
Cauchy–Schwarz turns the equation into the Riccati supersolution and the
flow cannot persist to `n/(2 m₀)` — the geometric form, with the
evolution data as the only hypotheses.
-/
theorem hamilton_singularity_of_evolution_eq
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    [Nontrivial E]
    {R R' : ℝ → E → ℝ} {Rc : ℝ → E → (E →ₗ[ℝ] E)} {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {T m₀ B : ℝ}
    (hm₀ : 0 < m₀) (hT0 : 0 ≤ T)
    (hR_cont : Continuous ↿R)
    (hRd : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' t x) t)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (R t))
    (hsa : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, ∀ p q : E,
      b (Rc t x p) q = b p (Rc t x q))
    (htr : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      LinearMap.trace ℝ E (Rc t x) = R t x)
    (hevol : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      R' t x = modelLaplacian b hb (R t) x
        + 2 * LinearMap.trace ℝ E (Rc t x ∘ₗ Rc t x))
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (R t) K x → IsLocalMin (R t) x)
    (hRB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, R t x ≤ B)
    (h0 : ∀ x ∈ K, m₀ ≤ R 0 x) :
    T < (Module.finrank ℝ E : ℝ) / (2 * m₀) := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    have := Module.finrank_pos (R := ℝ) (M := E)
    exact_mod_cast this
  set a : ℝ := 2 / (Module.finrank ℝ E : ℝ) with ha'
  have ha : 0 < a := by positivity
  -- The equation plus trace-CS gives the Riccati supersolution.
  have hineq : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      modelLaplacian b hb (R t) x + a * (R t x) ^ 2 ≤ R' t x := by
    intro t ht x hx
    have hcs := trace_sq_le_card_mul_trace_comp_self b hbs hbpos
      (Rc t x) (hsa t ht x hx)
    rw [htr t ht x hx] at hcs
    rw [hevol t ht x hx, ha']
    have h2 : (R t x) ^ 2 / (Module.finrank ℝ E : ℝ) ≤
        LinearMap.trace ℝ E (Rc t x ∘ₗ Rc t x) := by
      rw [div_le_iff₀ hn]
      linarith [hcs]
    have h3 : 2 / (Module.finrank ℝ E : ℝ) * (R t x) ^ 2 =
        2 * ((R t x) ^ 2 / (Module.finrank ℝ E : ℝ)) := by
      ring
    rw [h3]
    linarith
  have := hamilton_finite_time_singularity b hb hbs hbpos hK hKne
    ha hm₀ hT0 hR_cont hRd hspace hineq hmin_int hRB h0
  calc T < 1 / (a * m₀) := this
    _ = (Module.finrank ℝ E : ℝ) / (2 * m₀) := by
      rw [ha']
      field_simp

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The derivative of a trace-path**: the trace is continuous-linear in
finite dimension, so it commutes with time differentiation — the rule by
which `∂R/∂t` is computed from `∂(Ric♯)/∂t` along the flow.
-/
theorem hasDerivAt_trace {A : ℝ → E →L[ℝ] E} {A' : E →L[ℝ] E} {t₀ : ℝ}
    (hd : HasDerivAt A A' t₀) :
    HasDerivAt (fun t ↦ LinearMap.trace ℝ E (A t : E →ₗ[ℝ] E))
      (LinearMap.trace ℝ E (A' : E →ₗ[ℝ] E)) t₀ := by
  set trC : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ E) ∘ₗ
        (ContinuousLinearMap.coeLM ℝ :
          (E →L[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E))) with htrC
  have h := (trC.hasFDerivAt.comp_hasDerivAt t₀ hd)
  simpa [htrC] using h

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The derivative of `tr(A²)`**: `d/dt tr(A²) = 2 tr(A′A)` by the operator
product rule and trace cyclicity — the rule for `∂|Ric|²/∂t` in the
evolution equation.
-/
theorem hasDerivAt_trace_sq {A : ℝ → E →L[ℝ] E} {A' : E →L[ℝ] E}
    {t₀ : ℝ} (hd : HasDerivAt A A' t₀) :
    HasDerivAt (fun t ↦ LinearMap.trace ℝ E
        ((A t).comp (A t) : E →ₗ[ℝ] E))
      (2 * LinearMap.trace ℝ E ((A'.comp (A t₀)) : E →ₗ[ℝ] E)) t₀ := by
  have hcomp : HasDerivAt (fun t ↦ (A t).comp (A t))
      (A'.comp (A t₀) + (A t₀).comp A') t₀ := hd.clm_comp hd
  have h := hasDerivAt_trace hcomp
  convert h using 1
  rw [show ((A'.comp (A t₀) + (A t₀).comp A' : E →L[ℝ] E) :
    E →ₗ[ℝ] E) = (A'.comp (A t₀) : E →ₗ[ℝ] E)
      + ((A t₀).comp A' : E →ₗ[ℝ] E) from rfl, map_add]
  have hcyc : LinearMap.trace ℝ E (((A t₀).comp A' : E →ₗ[ℝ] E)) =
      LinearMap.trace ℝ E ((A'.comp (A t₀) : E →ₗ[ℝ] E)) := by
    rw [show (((A t₀).comp A' : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      ((A t₀ : E →ₗ[ℝ] E)) ∘ₗ ((A' : E →ₗ[ℝ] E)) from rfl,
      show ((A'.comp (A t₀) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      ((A' : E →ₗ[ℝ] E)) ∘ₗ ((A t₀ : E →ₗ[ℝ] E)) from rfl]
    exact LinearMap.trace_comp_comm' _ _
  rw [hcyc]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **`δΓ` vanishes in the zero direction** — the variation anchor: a
static metric has static Christoffel symbols. -/
theorem christoffelDeriv_zero_direction
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) :
    christoffelDeriv G (fun _ ↦ 0) x u v = 0 := by
  unfold christoffelDeriv
  rw [christoffelFunctional_const (0 : E →L[ℝ] E →L[ℝ] ℝ) x u v]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **`δΓ` is additive in the variation direction** — the connection's
response is linear in the metric's variation. -/
theorem christoffelDeriv_add_direction
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    {H₁ H₂ : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hH₁ : DifferentiableAt ℝ H₁ x) (hH₂ : DifferentiableAt ℝ H₂ x)
    (u v : E) :
    christoffelDeriv G (fun y ↦ H₁ y + H₂ y) x u v =
      christoffelDeriv G H₁ x u v + christoffelDeriv G H₂ x u v := by
  unfold christoffelDeriv
  have hΦ : LinearMap.toContinuousLinearMap
      (christoffelFunctional (fun y ↦ H₁ y + H₂ y) x u v) =
      LinearMap.toContinuousLinearMap
        (christoffelFunctional H₁ x u v)
      + LinearMap.toContinuousLinearMap
        (christoffelFunctional H₂ x u v) := by
    ext w
    have h := christoffelFunctional_add_apply hH₁ hH₂ u v w
    simpa using h
  rw [hΦ]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    neg_add, ContinuousLinearMap.add_apply, map_add,
    ContinuousLinearMap.neg_apply]
  abel

end RicciFlow

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**Derivative reconstruction for operator-valued paths**: an
`(E →L F)`-valued path whose every evaluation differentiates has a
derivative — basis reconstruction with `smulRight`-tensors. The general
form needed for differentiating the second-slot Christoffel maps.
-/
theorem hasDerivAt_clm_of_forall_apply'
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℝ → E →L[ℝ] F} {ψ : E →L[ℝ] F} {t₀ : ℝ}
    (h : ∀ w : E, HasDerivAt (fun t ↦ φ t w) (ψ w) t₀) :
    HasDerivAt φ ψ t₀ := by
  set bE := Module.finBasis ℝ E with hbE
  set coordC : (Fin (Module.finrank ℝ E)) → (E →L[ℝ] ℝ) :=
    fun i ↦ LinearMap.toContinuousLinearMap (bE.coord i) with hcoord
  have hrepr : ∀ ρ : E →L[ℝ] F,
      ρ = ∑ i, (coordC i).smulRight (ρ (bE i)) := by
    intro ρ
    ext w
    have hw := bE.sum_repr w
    conv_lhs => rw [← hw]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (coordC i) w = bE.coord i w from rfl,
      Module.Basis.coord_apply]
  have hsum : HasDerivAt (fun t ↦ ∑ i, (coordC i).smulRight (φ t (bE i)))
      (∑ i, (coordC i).smulRight (ψ (bE i))) t₀ := by
    apply HasDerivAt.fun_sum
    intro i _
    have hpath := h (bE i)
    have hsm := (ContinuousLinearMap.smulRightL ℝ E F
      (coordC i)).hasFDerivAt.comp_hasDerivAt t₀ hpath
    simpa using hsm
  have hfun : (fun t ↦ φ t) = fun t ↦ ∑ i,
      (coordC i).smulRight (φ t (bE i)) := by
    funext t
    exact hrepr (φ t)
  rw [show φ = fun t ↦ φ t from rfl, hfun, hrepr ψ]
  exact hsum

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional is additive in its second direction. -/
theorem christoffelFunctional_add_snd
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v₁ v₂ : E) :
    christoffelFunctional G x u (v₁ + v₂) =
      christoffelFunctional G x u v₁ + christoffelFunctional G x u v₂ := by
  apply LinearMap.ext
  intro w
  show (1 / 2 : ℝ) * ((fderiv ℝ G x u) (v₁ + v₂) w
      + (fderiv ℝ G x (v₁ + v₂)) u w - (fderiv ℝ G x w) u (v₁ + v₂)) = _
  simp only [map_add, ContinuousLinearMap.add_apply, LinearMap.add_apply]
  show _ = (1 / 2 : ℝ) * ((fderiv ℝ G x u) v₁ w
      + (fderiv ℝ G x v₁) u w - (fderiv ℝ G x w) u v₁)
    + (1 / 2 : ℝ) * ((fderiv ℝ G x u) v₂ w
      + (fderiv ℝ G x v₂) u w - (fderiv ℝ G x w) u v₂)
  ring

/-- **`δΓ` is additive in its second slot** — with first-slot symmetry,
`δΓ` is a genuine symmetric bilinear tensor-valued variation. -/
theorem christoffelDeriv_add_snd
    (G H : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v₁ v₂ : E) :
    christoffelDeriv G H x u (v₁ + v₂) =
      christoffelDeriv G H x u v₁ + christoffelDeriv G H x u v₂ := by
  unfold christoffelDeriv
  rw [christoffelFunctional_add_snd G x u v₁ v₂,
    christoffelFunctional_add_snd H x u v₁ v₂]
  simp only [map_add, ContinuousLinearMap.neg_apply]
  abel

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional is homogeneous in its second direction. -/
theorem christoffelFunctional_smul_snd
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u : E) (c : ℝ) (v : E) :
    christoffelFunctional G x u (c • v) =
      c • christoffelFunctional G x u v := by
  apply LinearMap.ext
  intro w
  show (1 / 2 : ℝ) * ((fderiv ℝ G x u) (c • v) w
      + (fderiv ℝ G x (c • v)) u w - (fderiv ℝ G x w) u (c • v)) = _
  simp only [map_smul, ContinuousLinearMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul]
  show _ = c * ((1 / 2 : ℝ) * ((fderiv ℝ G x u) v w
      + (fderiv ℝ G x v) u w - (fderiv ℝ G x w) u v))
  ring

/-- **`δΓ` is homogeneous in its second slot** — bilinearity complete. -/
theorem christoffelDeriv_smul_snd
    (G H : E → E →L[ℝ] E →L[ℝ] ℝ) (x u : E) (c : ℝ) (v : E) :
    christoffelDeriv G H x u (c • v) =
      c • christoffelDeriv G H x u v := by
  unfold christoffelDeriv
  rw [christoffelFunctional_smul_snd G x u c v,
    christoffelFunctional_smul_snd H x u c v]
  simp only [map_smul, ContinuousLinearMap.neg_apply, smul_add, smul_neg]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The `δΓ`-operator**: the variation's second slot as a continuous
endomorphism — the form entering the operator-path differentiation of the
curvature. -/
noncomputable def christoffelDerivOp (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ christoffelDeriv G H x u v
      map_add' := fun v₁ v₂ ↦ christoffelDeriv_add_snd G H x u v₁ v₂
      map_smul' := fun c v ↦ by
        simp only [RingHom.id_apply]
        exact christoffelDeriv_smul_snd G H x u c v }

@[simp]
theorem christoffelDerivOp_apply (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) :
    christoffelDerivOp G H x u v = christoffelDeriv G H x u v := rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The closed-form Christoffel operator: the second slot of
`Γ = G⁻¹Φ_G` as a continuous endomorphism. -/
noncomputable def christoffelClosedOp (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ (G x).inverse (LinearMap.toContinuousLinearMap
        (christoffelFunctional G x u v))
      map_add' := fun v₁ v₂ ↦ by
        rw [christoffelFunctional_add_snd G x u v₁ v₂]
        simp [map_add]
      map_smul' := fun c v ↦ by
        rw [christoffelFunctional_smul_snd G x u c v]
        simp [map_smul] }

@[simp]
theorem christoffelClosedOp_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) :
    christoffelClosedOp G x u v = (G x).inverse
      (LinearMap.toContinuousLinearMap
        (christoffelFunctional G x u v)) := rfl

/--
**The Christoffel operator path differentiates to the `δΓ`-operator**:
along a metric flow, `t ↦ Γₜ(u,·)` has derivative `δΓ(u,·)` as
endomorphism-valued paths — the gateway to `∂t` of the `ΓΓ`-terms of the
curvature.
-/
theorem hasDerivAt_christoffelClosedOp
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀) :
    HasDerivAt (fun t ↦ christoffelClosedOp (Gt t) x u)
      (christoffelDerivOp (Gt t₀) H x u) t₀ := by
  apply hasDerivAt_clm_of_forall_apply'
  intro v
  have h := hasDerivAt_christoffel_flow' u v hdG hev hmix
  simpa using h

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**`∂t` of the `ΓΓ`-terms**: the composition of Christoffel operator paths
differentiates by the product rule into the mixed `δΓ·Γ + Γ·δΓ` terms —
the quadratic half of the curvature variation, closed.
-/
theorem hasDerivAt_christoffelClosedOp_comp
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u w : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀) :
    HasDerivAt (fun t ↦ (christoffelClosedOp (Gt t) x u).comp
        (christoffelClosedOp (Gt t) x w))
      ((christoffelDerivOp (Gt t₀) H x u).comp
          (christoffelClosedOp (Gt t₀) x w)
        + (christoffelClosedOp (Gt t₀) x u).comp
          (christoffelDerivOp (Gt t₀) H x w)) t₀ :=
  (hasDerivAt_christoffelClosedOp u hdG hev hmix).clm_comp
    (hasDerivAt_christoffelClosedOp w hdG hev hmix)

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The `δΓ`-operator inherits the slot symmetry. -/
theorem christoffelDerivOp_symm
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x) (hHd : DifferentiableAt ℝ H x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hHsymm : ∀ (y : E) (p q : E), H y p q = H y q p) (u v : E) :
    christoffelDerivOp G H x u v = christoffelDerivOp G H x v u := by
  rw [christoffelDerivOp_apply, christoffelDerivOp_apply]
  exact christoffelDeriv_symm hGd hHd hGsymm hHsymm u v

end RicciFlow
