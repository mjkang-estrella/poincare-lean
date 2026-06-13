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

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The operator–witness bridge**: the closed-form Christoffel operator
agrees with the witness-based corrector — the identification through which
the variation theorems plug into the coordinate curvature formula. -/
theorem christoffelClosedOp_eq_christoffelAt
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbg : ∀ v w : E, b v w = G x v w) (u v : E) :
    christoffelClosedOp G x u v = christoffelAt G x b hb u v := by
  rw [christoffelClosedOp_apply]
  exact (christoffelAt_eq_inverse G b hb hbg u v).symm

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The curvature's quadratic part in operator language**: the
`Γ(v, ∇_w X)`-terms of the coordinate formula split into the operator
applied to the flat derivative plus the operator composition applied to
the field — the form whose time-derivative the `ΓΓ`-rule computes.
-/
theorem curvature_quadratic_operator_form
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbg : ∀ v w : E, b v w = G x v w)
    (X : E → E) (v w : E) :
    christoffelAt G x b hb v (fderiv ℝ X x w
        + christoffelAt G x b hb w (X x)) =
      christoffelClosedOp G x v (fderiv ℝ X x w)
        + ((christoffelClosedOp G x v).comp
            (christoffelClosedOp G x w)) (X x) := by
  rw [← christoffelClosedOp_eq_christoffelAt G b hb hbg,
    ← christoffelClosedOp_eq_christoffelAt G b hb hbg]
  rw [map_add]
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The `DΓ`-half of the curvature variation**: from directionwise
`∂t∂x`-commutation hypotheses on the Christoffel operator family
(`hmix2`), the spatial gradient of the operator family differentiates in
time to the spatial gradient of the `δΓ`-operator family — as
CLM-valued paths, by basis reconstruction.
-/
theorem hasDerivAt_christoffelOpGrad
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u : E)
    (hmix2 : ∀ v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y u) x v) t₀) :
    HasDerivAt
      (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x)
      (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y u) x) t₀ :=
  hasDerivAt_clm_of_forall_apply' hmix2

/--
The `DΓ`-half applied: the directional spatial derivative of the
Christoffel operator family, evaluated on a fixed vector, differentiates
in time to the corresponding `δΓ`-gradient value.
-/
theorem hasDerivAt_christoffelOpGrad_apply
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u : E)
    (hmix2 : ∀ v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y u) x v) t₀)
    (v z : E) :
    HasDerivAt
      (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x v z)
      (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y u) x v z) t₀ := by
  have h := hmix2 v
  exact (ContinuousLinearMap.apply ℝ E z).hasFDerivAt.comp_hasDerivAt t₀ h

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The coordinate curvature operator of a metric: the `DΓ`-difference
plus the `ΓΓ`-commutator, as an endomorphism. -/
noncomputable def coordCurvatureOp (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u w : E) : E →L[ℝ] E :=
  fderiv ℝ (fun y ↦ christoffelClosedOp G y w) x u
    - fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x w
    + (christoffelClosedOp G x u).comp (christoffelClosedOp G x w)
    - (christoffelClosedOp G x w).comp (christoffelClosedOp G x u)

/-- **The named `δRm`**: the variation of the coordinate curvature
operator at a metric `G` in the direction `H` — the `δΓ`-gradient
difference plus the mixed `δΓ·Γ + Γ·δΓ` commutator terms. -/
noncomputable def curvatureDerivOp (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u w : E) : E →L[ℝ] E :=
  fderiv ℝ (fun y ↦ christoffelDerivOp G H y w) x u
    - fderiv ℝ (fun y ↦ christoffelDerivOp G H y u) x w
    + ((christoffelDerivOp G H x u).comp (christoffelClosedOp G x w)
      + (christoffelClosedOp G x u).comp (christoffelDerivOp G H x w))
    - ((christoffelDerivOp G H x w).comp (christoffelClosedOp G x u)
      + (christoffelClosedOp G x w).comp (christoffelDerivOp G H x u))

/--
**THE CURVATURE VARIATION ASSEMBLED**: along a metric flow, the
coordinate curvature operator differentiates in time to `δRm` — the
`DΓ`-half (by basis reconstruction from the `∂t∂x`-commutation
hypotheses) plus the `ΓΓ`-half (by the operator product rule).
-/
theorem hasDerivAt_coordCurvatureOp
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u w : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀)
    (hmix2 : ∀ p v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y p) x v) t₀) :
    HasDerivAt (fun t ↦ coordCurvatureOp (Gt t) x u w)
      (curvatureDerivOp (Gt t₀) H x u w) t₀ := by
  have hDw : HasDerivAt
      (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y w) x u)
      (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y w) x u) t₀ :=
    hmix2 w u
  have hDu : HasDerivAt
      (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x w)
      (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y u) x w) t₀ :=
    hmix2 u w
  have hCuw := hasDerivAt_christoffelClosedOp_comp u w hdG hev hmix
  have hCwu := hasDerivAt_christoffelClosedOp_comp w u hdG hev hmix
  exact ((hDw.sub hDu).add hCuw).sub hCwu

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The coordinate Ricci form of a metric: the basis-trace contraction
`Ric(u,w) = Σᵢ ⟨bⁱ, Rm(bᵢ,u)w⟩` of the coordinate curvature operator. -/
noncomputable def coordRicci (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u w : E) :
    ℝ :=
  ∑ i, (Module.finBasis ℝ E).coord i
    (coordCurvatureOp G x ((Module.finBasis ℝ E) i) u w)

/-- **The named `δRic`**: the basis-trace contraction of `δRm` — the
variation of the coordinate Ricci form along a metric flow. -/
noncomputable def ricciDeriv (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u w : E) : ℝ :=
  ∑ i, (Module.finBasis ℝ E).coord i
    (curvatureDerivOp G H x ((Module.finBasis ℝ E) i) u w)

/--
**`δRic` by contraction**: along a metric flow, the coordinate Ricci
form differentiates in time to the basis-trace contraction of `δRm` —
the variation passes through the trace.
-/
theorem hasDerivAt_coordRicci
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u w : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀)
    (hmix2 : ∀ p v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y p) x v) t₀) :
    HasDerivAt (fun t ↦ coordRicci (Gt t) x u w)
      (ricciDeriv (Gt t₀) H x u w) t₀ := by
  apply HasDerivAt.fun_sum
  intro i _
  have hRm := hasDerivAt_coordCurvatureOp
    ((Module.finBasis ℝ E) i) u hdG hev hmix hmix2
  have happ := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivAt
    t₀ hRm
  exact (LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ E).coord i)).hasFDerivAt.comp_hasDerivAt t₀ happ

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional is additive in its first direction. -/
theorem christoffelFunctional_add_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u₁ u₂ v : E) :
    christoffelFunctional G x (u₁ + u₂) v =
      christoffelFunctional G x u₁ v + christoffelFunctional G x u₂ v := by
  apply LinearMap.ext
  intro w
  show (1 / 2 : ℝ) * ((fderiv ℝ G x (u₁ + u₂)) v w
      + (fderiv ℝ G x v) (u₁ + u₂) w - (fderiv ℝ G x w) (u₁ + u₂) v) = _
  simp only [map_add, ContinuousLinearMap.add_apply, LinearMap.add_apply]
  show _ = (1 / 2 : ℝ) * ((fderiv ℝ G x u₁) v w
      + (fderiv ℝ G x v) u₁ w - (fderiv ℝ G x w) u₁ v)
    + (1 / 2 : ℝ) * ((fderiv ℝ G x u₂) v w
      + (fderiv ℝ G x v) u₂ w - (fderiv ℝ G x w) u₂ v)
  ring

/-- The corrector functional is homogeneous in its first direction. -/
theorem christoffelFunctional_smul_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (c : ℝ) (u v : E) :
    christoffelFunctional G x (c • u) v =
      c • christoffelFunctional G x u v := by
  apply LinearMap.ext
  intro w
  show (1 / 2 : ℝ) * ((fderiv ℝ G x (c • u)) v w
      + (fderiv ℝ G x v) (c • u) w - (fderiv ℝ G x w) (c • u) v) = _
  simp only [map_smul, ContinuousLinearMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul]
  show _ = c * ((1 / 2 : ℝ) * ((fderiv ℝ G x u) v w
      + (fderiv ℝ G x v) u w - (fderiv ℝ G x w) u v))
  ring

/-- **The Christoffel operator is additive in its direction slot.** -/
theorem christoffelClosedOp_add_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u₁ u₂ : E) :
    christoffelClosedOp G x (u₁ + u₂) =
      christoffelClosedOp G x u₁ + christoffelClosedOp G x u₂ := by
  ext v
  simp only [christoffelClosedOp_apply, ContinuousLinearMap.add_apply]
  rw [show LinearMap.toContinuousLinearMap
      (christoffelFunctional G x (u₁ + u₂) v) =
    LinearMap.toContinuousLinearMap (christoffelFunctional G x u₁ v)
      + LinearMap.toContinuousLinearMap (christoffelFunctional G x u₂ v)
    from by rw [christoffelFunctional_add_fst]; rfl]
  exact map_add _ _ _

/-- **The Christoffel operator is homogeneous in its direction slot.** -/
theorem christoffelClosedOp_smul_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (c : ℝ) (u : E) :
    christoffelClosedOp G x (c • u) = c • christoffelClosedOp G x u := by
  ext v
  simp only [christoffelClosedOp_apply, ContinuousLinearMap.smul_apply]
  rw [show LinearMap.toContinuousLinearMap
      (christoffelFunctional G x (c • u) v) =
    c • LinearMap.toContinuousLinearMap (christoffelFunctional G x u v)
    from by rw [christoffelFunctional_smul_fst]; rfl]
  exact map_smul _ _ _

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The coordinate curvature operator is additive in its second
slot**, given differentiability of the Christoffel operator families —
the tensoriality input for contracting the second slot. -/
theorem coordCurvatureOp_add_snd
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (v w₁ w₂ : E) :
    coordCurvatureOp G x v (w₁ + w₂) =
      coordCurvatureOp G x v w₁ + coordCurvatureOp G x v w₂ := by
  unfold coordCurvatureOp
  have hfam : (fun y ↦ christoffelClosedOp G y (w₁ + w₂)) =
      fun y ↦ christoffelClosedOp G y w₁ + christoffelClosedOp G y w₂ := by
    funext y
    exact christoffelClosedOp_add_fst G y w₁ w₂
  rw [hfam, fderiv_fun_add (hdiff w₁) (hdiff w₂)]
  rw [christoffelClosedOp_add_fst G x w₁ w₂]
  simp only [ContinuousLinearMap.add_apply, map_add,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  abel

/-- **The coordinate Ricci form is additive in its first slot** — the
contraction inherits tensoriality from the curvature operator. -/
theorem coordRicci_add_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (u₁ u₂ w : E) :
    coordRicci G x (u₁ + u₂) w =
      coordRicci G x u₁ w + coordRicci G x u₂ w := by
  unfold coordRicci
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordCurvatureOp_add_snd G hdiff _ u₁ u₂]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The coordinate curvature operator is homogeneous in its second slot. -/
theorem coordCurvatureOp_smul_snd
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (v : E) (c : ℝ) (w : E) :
    coordCurvatureOp G x v (c • w) = c • coordCurvatureOp G x v w := by
  unfold coordCurvatureOp
  have hfam : (fun y ↦ christoffelClosedOp G y (c • w)) =
      fun y ↦ c • christoffelClosedOp G y w := by
    funext y
    exact christoffelClosedOp_smul_fst G y c w
  rw [hfam, fderiv_fun_const_smul (hdiff w) c]
  rw [christoffelClosedOp_smul_fst G x c w]
  simp only [ContinuousLinearMap.smul_apply, map_smul,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  module

/-- The coordinate Ricci form is homogeneous in its first slot. -/
theorem coordRicci_smul_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (c : ℝ) (u w : E) :
    coordRicci G x (c • u) w = c • coordRicci G x u w := by
  unfold coordRicci
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordCurvatureOp_smul_snd G hdiff _ c u]
  simp

/-- **The coordinate Ricci form packaged as a functional in its first
slot** — the continuous-linear shape against which the inverse metric
raises an index. -/
noncomputable def coordRicciCLM (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (w : E) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ coordRicci G x u w
      map_add' := fun u₁ u₂ ↦ coordRicci_add_fst G hdiff u₁ u₂ w
      map_smul' := fun c u ↦ by
        simp only [RingHom.id_apply]
        exact coordRicci_smul_fst G hdiff c u w }

@[simp]
theorem coordRicciCLM_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (w u : E) :
    coordRicciCLM G x hdiff w u = coordRicci G x u w := rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **`δRic` is additive in its first slot** along a flow — by uniqueness
of derivatives, from the tensoriality of the Ricci form. -/
theorem ricciDeriv_add_fst
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (u₁ u₂ w : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀)
    (hmix2 : ∀ p v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y p) x v) t₀)
    (hd2 : ∀ t : ℝ, ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x) :
    ricciDeriv (Gt t₀) H x (u₁ + u₂) w =
      ricciDeriv (Gt t₀) H x u₁ w + ricciDeriv (Gt t₀) H x u₂ w := by
  have h1 := hasDerivAt_coordRicci u₁ w hdG hev hmix hmix2
  have h2 := hasDerivAt_coordRicci u₂ w hdG hev hmix hmix2
  have h12 := h1.add h2
  have h3 := hasDerivAt_coordRicci (u₁ + u₂) w hdG hev hmix hmix2
  have hpath : (fun t ↦ coordRicci (Gt t) x (u₁ + u₂) w) =
      fun t ↦ coordRicci (Gt t) x u₁ w + coordRicci (Gt t) x u₂ w := by
    funext t
    exact coordRicci_add_fst (Gt t) (hd2 t) u₁ u₂ w
  rw [hpath] at h3
  exact h3.unique h12

/-- **`δRic` is homogeneous in its first slot** along a flow. -/
theorem ricciDeriv_smul_fst
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ} (c : ℝ) (u w : E)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀)
    (hmix2 : ∀ p v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y p) x v) t₀)
    (hd2 : ∀ t : ℝ, ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x) :
    ricciDeriv (Gt t₀) H x (c • u) w =
      c • ricciDeriv (Gt t₀) H x u w := by
  have h1 := hasDerivAt_coordRicci u w hdG hev hmix hmix2
  have h2 := h1.const_smul c
  have h3 := hasDerivAt_coordRicci (c • u) w hdG hev hmix hmix2
  have hpath : (fun t ↦ coordRicci (Gt t) x (c • u) w) =
      fun t ↦ c • coordRicci (Gt t) x u w := by
    funext t
    exact coordRicci_smul_fst (Gt t) (hd2 t) c u w
  rw [hpath] at h3
  exact h3.unique h2

/-- **The coordinate scalar curvature**: the inverse-metric contraction
`R = Σⱼ Ric(♯bʲ, bⱼ)` of the coordinate Ricci form. -/
noncomputable def coordScalar (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∑ j, coordRicci G x
    ((G x).inverse (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord j)))
    ((Module.finBasis ℝ E) j)

/--
**THE TIME-DERIVATIVE OF THE SCALAR CURVATURE ALONG A FLOW**: the
coordinate scalar curvature differentiates to the contracted `δRic`
plus the inverse-metric variation term — `∂R/∂t = Σⱼ [δRic(♯bʲ,bⱼ) −
Ric((G⁻¹HG⁻¹)bʲ, bⱼ)]`. The structural evolution equation of `R`.
-/
theorem hasDerivAt_coordScalar
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ}
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀)
    (hmix2 : ∀ p v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y p) x v) t₀)
    (hd2 : ∀ t : ℝ, ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x) :
    HasDerivAt (fun t ↦ coordScalar (Gt t) x)
      (∑ j, (ricciDeriv (Gt t₀) H x
          ((Gt t₀ x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord j)))
          ((Module.finBasis ℝ E) j)
        + coordRicci (Gt t₀) x
          ((-((Gt t₀ x).inverse.comp ((H x).comp (Gt t₀ x).inverse)))
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord j)))
          ((Module.finBasis ℝ E) j))) t₀ := by
  apply HasDerivAt.fun_sum
  intro j _
  set bE := Module.finBasis ℝ E
  set ρ : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (bE.coord j) with hρ
  -- The Ricci form as a CLM-valued path in time.
  set A : ℝ → E →L[ℝ] ℝ :=
    fun t ↦ coordRicciCLM (Gt t) x (hd2 t) (bE j) with hA
  set ψ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ ricciDeriv (Gt t₀) H x u (bE j)
      map_add' := fun u₁ u₂ ↦
        ricciDeriv_add_fst u₁ u₂ (bE j) hdG hev hmix hmix2 hd2
      map_smul' := fun c u ↦ by
        simp only [RingHom.id_apply]
        exact ricciDeriv_smul_fst c u (bE j) hdG hev hmix hmix2 hd2 }
    with hψ
  have hAderiv : HasDerivAt A ψ t₀ := by
    apply hasDerivAt_clm_of_forall_apply
    intro u
    exact hasDerivAt_coordRicci u (bE j) hdG hev hmix hmix2
  -- The raised-index path in time.
  have hInv : HasDerivAt (fun t ↦ (Gt t x).inverse)
      (-((Gt t₀ x).inverse.comp ((H x).comp (Gt t₀ x).inverse))) t₀ :=
    hasDerivAt_clm_inverse hdG hev
  have hv : HasDerivAt (fun t ↦ (Gt t x).inverse ρ)
      ((-((Gt t₀ x).inverse.comp ((H x).comp (Gt t₀ x).inverse))) ρ)
      t₀ := by
    simpa using hInv.clm_apply (hasDerivAt_const t₀ ρ)
  have h := hAderiv.clm_apply hv
  exact h

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corrector functional of a constant metric vanishes. -/
theorem christoffelFunctional_const_eq_zero
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) :
    christoffelFunctional (fun _ : E ↦ G₀) x u v = 0 := by
  apply LinearMap.ext
  intro w
  show (1 / 2 : ℝ) * ((fderiv ℝ (fun _ : E ↦ G₀) x u) v w
      + (fderiv ℝ (fun _ : E ↦ G₀) x v) u w
      - (fderiv ℝ (fun _ : E ↦ G₀) x w) u v) = 0
  rw [fderiv_fun_const]
  simp

/-- The Christoffel operator of a constant metric vanishes. -/
theorem christoffelClosedOp_const_eq_zero
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (x u : E) :
    christoffelClosedOp (fun _ : E ↦ G₀) x u = 0 := by
  ext v
  rw [christoffelClosedOp_apply,
    christoffelFunctional_const_eq_zero G₀ x u v]
  simp [map_zero]

/-- The coordinate curvature operator of a constant metric vanishes. -/
theorem coordCurvatureOp_const_eq_zero
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (x u w : E) :
    coordCurvatureOp (fun _ : E ↦ G₀) x u w = 0 := by
  unfold coordCurvatureOp
  have hfam : ∀ p : E, (fun y : E ↦
      christoffelClosedOp (fun _ : E ↦ G₀) y p) = fun _ : E ↦ 0 := by
    intro p
    funext y
    exact christoffelClosedOp_const_eq_zero G₀ y p
  rw [hfam u, hfam w, fderiv_fun_const,
    christoffelClosedOp_const_eq_zero G₀ x u,
    christoffelClosedOp_const_eq_zero G₀ x w]
  simp

/-- The coordinate Ricci form of a constant metric vanishes. -/
theorem coordRicci_const_eq_zero
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (x u w : E) :
    coordRicci (fun _ : E ↦ G₀) x u w = 0 := by
  unfold coordRicci
  apply Finset.sum_eq_zero
  intro i _
  rw [coordCurvatureOp_const_eq_zero]
  simp

/-- **The flat anchor**: the coordinate scalar curvature of a constant
metric vanishes — the contraction chain computes correctly on the model. -/
theorem coordScalar_const_eq_zero
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    coordScalar (fun _ : E ↦ G₀) x = 0 := by
  unfold coordScalar
  apply Finset.sum_eq_zero
  intro j _
  exact coordRicci_const_eq_zero G₀ x _ _

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The coordinate Ricci form is additive in its second slot. -/
theorem coordRicci_add_snd (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u w₁ w₂ : E) :
    coordRicci G x u (w₁ + w₂) =
      coordRicci G x u w₁ + coordRicci G x u w₂ := by
  unfold coordRicci
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add, map_add]

/-- The coordinate Ricci form is homogeneous in its second slot. -/
theorem coordRicci_smul_snd (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (c : ℝ) (u w : E) :
    coordRicci G x u (c • w) = c • coordRicci G x u w := by
  unfold coordRicci
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]

/-- **The coordinate Ricci form as a bilinear CLM** — the tensor shape
of `Ric`, the direction field of the Ricci flow. -/
noncomputable def coordRicciForm (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ coordRicciCLM G x hdiff u
      map_add' := fun u₁ u₂ ↦ by
        ext w
        show coordRicci G x w (u₁ + u₂) = _
        rw [coordRicci_add_snd]
        rfl
      map_smul' := fun c u ↦ by
        ext w
        show coordRicci G x w (c • u) = _
        rw [coordRicci_smul_snd]
        rfl }

@[simp]
theorem coordRicciForm_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (u w : E) :
    coordRicciForm G x hdiff u w = coordRicci G x w u := rfl

/-- **The coordinate `|Ric|²`**: the double-raised contraction
`Σⱼ Ric(♯Ric(♯bʲ,·), bⱼ) = Ricᵢⱼ Ric^{ij}`. -/
noncomputable def coordRicciNormSq (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x) : ℝ :=
  ∑ j, coordRicci G x
    ((G x).inverse (coordRicciForm G x hdiff
      ((G x).inverse (LinearMap.toContinuousLinearMap
        ((Module.finBasis ℝ E).coord j)))))
    ((Module.finBasis ℝ E) j)

/--
**THE `2|Ric|²`-HALF OF HAMILTON'S IDENTITY**: in the Ricci-flow
direction `H = −2·Ric`, the inverse-metric variation term of
`∂R/∂t` evaluates to `+2|Ric|²` in coordinates.
-/
theorem inverseVariation_ricci_direction
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x) :
    ∑ j, coordRicci G x
        ((-((G x).inverse.comp
            ((((-2 : ℝ) • coordRicciForm G x hdiff)).comp
              (G x).inverse)))
          (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j)
      = 2 * coordRicciNormSq G x hdiff := by
  unfold coordRicciNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  set ρ := LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ E).coord j)
  have harg : (-((G x).inverse.comp
      ((((-2 : ℝ) • coordRicciForm G x hdiff)).comp (G x).inverse))) ρ
      = (2 : ℝ) • (G x).inverse (coordRicciForm G x hdiff
        ((G x).inverse ρ)) := by
    simp only [ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      map_smul]
    module
  rw [harg, coordRicci_smul_fst G hdiff 2]
  simp [smul_eq_mul]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**HAMILTON'S SCALAR EVOLUTION EQUATION, modulo contracted Bianchi**:
along a Ricci flow (`H = −2·Ric` at the point), given the contracted
second Bianchi identity for the flow (`hBianchi`: the trace of `δRic`
is the Laplacian of `R`), the scalar curvature satisfies
`∂R/∂t = ΔR + 2|Ric|²`. The structural derivative, the
inverse-variation evaluation, and the Bianchi input compose into the
equation that drives the finite-time singularity theorem.
-/
theorem hamilton_scalar_evolution_of_bianchi
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ}
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀)
    (hmix2 : ∀ p v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y p) x v) t₀)
    (hd2 : ∀ t : ℝ, ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x)
    (hH : H x = (-2 : ℝ) • coordRicciForm (Gt t₀) x (hd2 t₀))
    (hBianchi : ∑ j, ricciDeriv (Gt t₀) H x
        ((Gt t₀ x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j)
      = modelLaplacian b hb (fun y ↦ coordScalar (Gt t₀) y) x) :
    HasDerivAt (fun t ↦ coordScalar (Gt t) x)
      (modelLaplacian b hb (fun y ↦ coordScalar (Gt t₀) y) x
        + 2 * coordRicciNormSq (Gt t₀) x (hd2 t₀)) t₀ := by
  have h := hasDerivAt_coordScalar hdG hev hmix hmix2 hd2
  rw [Finset.sum_add_distrib, hBianchi] at h
  have hvar : ∑ j, coordRicci (Gt t₀) x
      ((-((Gt t₀ x).inverse.comp ((H x).comp (Gt t₀ x).inverse)))
        (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
      ((Module.finBasis ℝ E) j)
      = 2 * coordRicciNormSq (Gt t₀) x (hd2 t₀) := by
    rw [hH]
    exact inverseVariation_ricci_direction (Gt t₀) x (hd2 t₀)
  rw [hvar] at h
  exact h

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The Ricci endomorphism**: the index-raised Ricci form `♯∘Ric♭` —
the operator shape demanded by the singularity theorem's hypotheses. -/
noncomputable def coordRicciEndo (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x) :
    E →ₗ[ℝ] E where
  toFun u := (G x).inverse (coordRicciForm G x hdiff u)
  map_add' u v := by rw [map_add, map_add]
  map_smul' c u := by rw [map_smul, map_smul]; rfl

@[simp]
theorem coordRicciEndo_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (u : E) :
    coordRicciEndo G x hdiff u =
      (G x).inverse (coordRicciForm G x hdiff u) := rfl

/-- **The metric pairs the Ricci endomorphism back to the Ricci form**:
`G(Rc u, ·) = Ric(·, u)` under invertibility. -/
theorem g_coordRicciEndo (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (hinv : (G x).IsInvertible) (u : E) :
    G x (coordRicciEndo G x hdiff u) = coordRicciForm G x hdiff u := by
  rw [coordRicciEndo_apply]
  exact (hinv.inverse_apply_eq.mp rfl).symm

/--
**THE SCALAR IS THE TRACE OF THE RICCI ENDOMORPHISM**: for a symmetric
invertible metric, `tr(Rc) = R` in coordinates — exactly the trace
hypothesis demanded by the finite-time singularity theorem.
-/
theorem trace_coordRicciEndo (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (hinv : (G x).IsInvertible)
    (hGsymm : ∀ v w : E, G x v w = G x w v) :
    LinearMap.trace ℝ E (coordRicciEndo G x hdiff) = coordScalar G x := by
  set bE := Module.finBasis ℝ E with hbE
  rw [LinearMap.trace_eq_matrix_trace ℝ bE, Matrix.trace]
  unfold coordScalar
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  set ρ := LinearMap.toContinuousLinearMap (bE.coord j) with hρ
  -- `coordⱼ(Rc bⱼ) = G(Rc bⱼ)(♯ρʲ)` by symmetry and the inverse identity.
  have hpair : ∀ v : E, bE.coord j v = G x v ((G x).inverse ρ) := by
    intro v
    have h1 : G x v ((G x).inverse ρ) = G x ((G x).inverse ρ) v :=
      hGsymm v _
    have h2 : G x ((G x).inverse ρ) = ρ :=
      (hinv.inverse_apply_eq.mp rfl).symm
    rw [h1, h2]
    rfl
  rw [show bE.repr (coordRicciEndo G x hdiff (bE j)) j =
    bE.coord j (coordRicciEndo G x hdiff (bE j)) from rfl]
  rw [hpair, ← ContinuousLinearMap.comp_apply]
  rw [show (G x) (coordRicciEndo G x hdiff (bE j)) =
    coordRicciForm G x hdiff (bE j) from
    g_coordRicciEndo G x hdiff hinv (bE j)]
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The raised-index contraction is the trace**: for an invertible metric,
`Σⱼ G(f(♯bʲ))(bⱼ) = tr f` — the trace of the conjugation `♭∘f∘♯`
computed in the dual basis, collapsed by trace-commutation.
-/
theorem sum_g_raised_eq_trace
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (hinv : (G x).IsInvertible)
    (f : E →ₗ[ℝ] E) :
    ∑ j, G x (f ((G x).inverse (LinearMap.toContinuousLinearMap
        ((Module.finBasis ℝ E).coord j))))
      ((Module.finBasis ℝ E) j)
      = LinearMap.trace ℝ E f := by
  set bE := Module.finBasis ℝ E with hbE
  -- The lowering and raising maps, as plain linear maps.
  set flat : E →ₗ[ℝ] (E →L[ℝ] ℝ) := (G x).toLinearMap with hflat
  set sharp : (E →L[ℝ] ℝ) →ₗ[ℝ] E := ((G x).inverse).toLinearMap
    with hsharp
  have hid : sharp ∘ₗ flat = LinearMap.id := by
    apply LinearMap.ext
    intro u
    exact hinv.inverse_apply_eq.mpr rfl
  -- The conjugated endomorphism on the dual.
  set D : (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) := flat ∘ₗ f ∘ₗ sharp with hD
  -- Its trace equals the trace of `f` by commutation and `♯∘♭ = id`.
  have htrD : LinearMap.trace ℝ (E →L[ℝ] ℝ) D = LinearMap.trace ℝ E f := by
    rw [hD, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hid,
      LinearMap.comp_id]
  -- Compute the trace of `D` in the dual basis.
  set bD : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (E →L[ℝ] ℝ) :=
    bE.dualBasis.map LinearMap.toContinuousLinearMap with hbD
  rw [← htrD, LinearMap.trace_eq_matrix_trace ℝ bD, Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have hbDj : bD j = LinearMap.toContinuousLinearMap (bE.coord j) := by
    rw [hbD, Module.Basis.map_apply]
    congr 1
    exact congrFun bE.coe_dualBasis j
  have hrepr : ∀ lam : E →L[ℝ] ℝ, bD.repr lam j = lam (bE j) := by
    intro lam
    rw [hbD, Module.Basis.map_repr]
    show bE.dualBasis.repr (LinearMap.toContinuousLinearMap.symm lam) j = _
    rw [Module.Basis.dualBasis_repr]
    rfl
  rw [hrepr, hbDj]
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**`|Ric|²` IS THE TRACE OF `Rc²`**: for an invertible metric with
symmetric Ricci form, the coordinate `|Ric|²` equals
`tr(Rc ∘ Rc)` — exactly the quadratic term demanded by the evolution
hypothesis of the finite-time singularity theorem.
-/
theorem coordRicciNormSq_eq_trace
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (hinv : (G x).IsInvertible)
    (hRicSymm : ∀ u w : E, coordRicci G x u w = coordRicci G x w u) :
    coordRicciNormSq G x hdiff =
      LinearMap.trace ℝ E
        (coordRicciEndo G x hdiff ∘ₗ coordRicciEndo G x hdiff) := by
  rw [← sum_g_raised_eq_trace G x hinv]
  unfold coordRicciNormSq
  apply Finset.sum_congr rfl
  intro j _
  set ρ := LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ E).coord j) with hρ
  set v := (G x).inverse ρ with hv
  -- The summand is `Ric(Rc v, bⱼ)`; flip by symmetry and pair back.
  have h1 : (G x).inverse (coordRicciForm G x hdiff v) =
      coordRicciEndo G x hdiff v := rfl
  rw [h1]
  rw [hRicSymm (coordRicciEndo G x hdiff v) ((Module.finBasis ℝ E) j)]
  have h2 : coordRicci G x ((Module.finBasis ℝ E) j)
      (coordRicciEndo G x hdiff v) =
      coordRicciForm G x hdiff (coordRicciEndo G x hdiff v)
        ((Module.finBasis ℝ E) j) := rfl
  rw [h2, ← g_coordRicciEndo G x hdiff hinv]
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The Ricci endomorphism is self-adjoint** with respect to a symmetric
invertible metric with symmetric Ricci form — the self-adjointness
hypothesis of the finite-time singularity theorem, discharged in
coordinates.
-/
theorem coordRicciEndo_selfAdjoint
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (hinv : (G x).IsInvertible)
    (hGsymm : ∀ v w : E, G x v w = G x w v)
    (hRicSymm : ∀ u w : E, coordRicci G x u w = coordRicci G x w u)
    (p q : E) :
    G x (coordRicciEndo G x hdiff p) q
      = G x p (coordRicciEndo G x hdiff q) := by
  have h1 : G x (coordRicciEndo G x hdiff p) q =
      coordRicci G x q p := by
    rw [g_coordRicciEndo G x hdiff hinv]
    rfl
  have h2 : G x p (coordRicciEndo G x hdiff q) =
      coordRicci G x p q := by
    rw [hGsymm, g_coordRicciEndo G x hdiff hinv]
    rfl
  rw [h1, h2, hRicSymm]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Set in
/--
**THE CONDITIONAL RICCI-FLOW SINGULARITY THEOREM**: a Ricci flow of
coordinate metrics (`∂G/∂t = −2 Ric` with the standard regularity and
symmetry data, the contracted Bianchi identity, and the model
compatibility hypotheses) whose initial scalar curvature is bounded
below by `m₀ > 0` on a compact set attaining interior minima cannot
extend past `n/(2m₀)`: every hypothesis of the finite-time singularity
theorem is discharged by the variation machinery — the derivative of
`R` by the assembled `δΓ→δRm→δRic→∂R/∂t` chain with the Bianchi input,
the trace identity by `trace_coordRicciEndo`, and the quadratic term by
`coordRicciNormSq_eq_trace`.
-/
theorem hamilton_ricci_flow_singularity
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    [Nontrivial E]
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {H : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {T m₀ B : ℝ} (hm₀ : 0 < m₀) (hT0 : 0 ≤ T)
    (hd2 : ∀ (t : ℝ) (x : E) (u : E),
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x)
    (hinv : ∀ (t : ℝ) (x : E), (Gt t x).IsInvertible)
    (hGsymm : ∀ (t : ℝ) (x : E) (v w : E), Gt t x v w = Gt t x w v)
    (hRicSymm : ∀ (t : ℝ) (x : E) (u w : E),
      coordRicci (Gt t) x u w = coordRicci (Gt t) x w u)
    (hdG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      HasDerivAt (fun s ↦ Gt s x) (H t x) t)
    (hmix : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, ∀ p q r : E,
      HasDerivAt (fun s ↦ (fderiv ℝ (Gt s) x p) q r)
        ((fderiv ℝ (H t) x p) q r) t)
    (hmix2 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, ∀ p v : E,
      HasDerivAt
        (fun s ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt s) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t) (H t) y p) x v) t)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      H t x = (-2 : ℝ) • coordRicciForm (Gt t) x (hd2 t x))
    (hBianchi : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ∑ j, ricciDeriv (Gt t) (H t) x
          ((Gt t x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord j)))
          ((Module.finBasis ℝ E) j)
        = modelLaplacian b hb (fun y ↦ coordScalar (Gt t) y) x)
    (hR_cont : Continuous ↿(fun t x ↦ coordScalar (Gt t) x))
    (hspace : ∀ t ∈ Icc (0 : ℝ) T,
      ContDiff ℝ 2 (fun x ↦ coordScalar (Gt t) x))
    (hsa : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, ∀ p q : E,
      b (coordRicciEndo (Gt t) x (hd2 t x) p) q
        = b p (coordRicciEndo (Gt t) x (hd2 t x) q))
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (fun y ↦ coordScalar (Gt t) y) K x →
        IsLocalMin (fun y ↦ coordScalar (Gt t) y) x)
    (hRB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, coordScalar (Gt t) x ≤ B)
    (h0 : ∀ x ∈ K, m₀ ≤ coordScalar (Gt 0) x) :
    T < (Module.finrank ℝ E : ℝ) / (2 * m₀) := by
  apply hamilton_singularity_of_evolution_eq b hb hbs hbpos hK hKne
    hm₀ hT0
    (R := fun t x ↦ coordScalar (Gt t) x)
    (R' := fun t x ↦
      modelLaplacian b hb (fun y ↦ coordScalar (Gt t) y) x
        + 2 * LinearMap.trace ℝ E
          (coordRicciEndo (Gt t) x (hd2 t x)
            ∘ₗ coordRicciEndo (Gt t) x (hd2 t x)))
    (Rc := fun t x ↦ coordRicciEndo (Gt t) x (hd2 t x))
    hR_cont ?_ hspace hsa ?_ ?_ hmin_int hRB h0
  · -- the time derivative, from the assembled variation machinery
    intro x hx t ht
    have h := hamilton_scalar_evolution_of_bianchi
      (Gt := Gt) (H := H t) (x := x) (t₀ := t) b hb
      (hdG t ht x hx)
      (Filter.Eventually.of_forall fun s ↦ hinv s x)
      (hmix t ht x hx) (hmix2 t ht x hx)
      (fun s u ↦ hd2 s x u)
      (hH t ht x hx) (hBianchi t ht x hx)
    rwa [coordRicciNormSq_eq_trace (Gt t) x (hd2 t x) (hinv t x)
      (hRicSymm t x)] at h
  · -- the trace identity
    intro t ht x hx
    exact trace_coordRicciEndo (Gt t) x (hd2 t x) (hinv t x)
      (hGsymm t x)
  · -- the evolution equation, by definition of `R'`
    intro t ht x hx
    rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Torsion symmetry of the Christoffel operator**: for a
differentiable symmetric metric, `Γ(u,v) = Γ(v,u)`. -/
theorem christoffelClosedOp_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p) (u v : E) :
    christoffelClosedOp G x u v = christoffelClosedOp G x v u := by
  rw [christoffelClosedOp_apply, christoffelClosedOp_apply,
    christoffelFunctional_symm hGd hGsymm u v]

/-- The coordinate curvature operator is antisymmetric in its plane. -/
theorem coordCurvatureOp_antisymm
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x u w : E) :
    coordCurvatureOp G x u w = -coordCurvatureOp G x w u := by
  unfold coordCurvatureOp
  abel

/-- Applying the spatial derivative of the operator family commutes
with evaluation: `[D_b Γ(a,·)] c = D_b [Γ(a,c)]`. -/
theorem fderiv_christoffelClosedOp_apply
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (a b c : E) :
    (fderiv ℝ (fun y ↦ christoffelClosedOp G y a) x b) c
      = fderiv ℝ (fun y ↦ christoffelClosedOp G y a c) x b := by
  have h := (ContinuousLinearMap.apply ℝ E c).hasFDerivAt.comp x
    (hdiff a).hasFDerivAt
  have hfd : fderiv ℝ (fun y ↦ christoffelClosedOp G y a c) x
      = (ContinuousLinearMap.apply ℝ E c).comp
        (fderiv ℝ (fun y ↦ christoffelClosedOp G y a) x) :=
    h.fderiv
  rw [hfd]
  rfl

/--
**THE FIRST BIANCHI IDENTITY IN COORDINATES**: for a torsion-symmetric
Christoffel family, the cyclic sum of the coordinate curvature
operator vanishes — `R(u,w)v + R(w,v)u + R(v,u)w = 0`.
-/
theorem coord_first_bianchi
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (u w v : E) :
    coordCurvatureOp G x u w v + coordCurvatureOp G x w v u
      + coordCurvatureOp G x v u w = 0 := by
  have happ := fderiv_christoffelClosedOp_apply hdiff
  have hfam : ∀ a c : E, (fun y ↦ christoffelClosedOp G y a c)
      = fun y ↦ christoffelClosedOp G y c a := by
    intro a c
    funext y
    exact hΓsymm y a c
  unfold coordCurvatureOp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  rw [happ u w v, happ w u v, happ w v u, happ v w u, happ v u w,
    happ u v w]
  rw [hfam w v, hfam u v, hfam u w]
  rw [hΓsymm x w v, hΓsymm x u v, hΓsymm x u w]
  abel

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**The contracted first Bianchi identity**: the antisymmetric part of
the coordinate Ricci form is the trace of the curvature operator on the
plane — `Ric(u,w) − Ric(w,u) = −tr R(u,w)`. Ricci symmetry reduces to
the vanishing of the curvature trace.
-/
theorem coordRicci_antisymm_part
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (u w : E) :
    coordRicci G x u w - coordRicci G x w u
      = -LinearMap.trace ℝ E
          ((coordCurvatureOp G x u w : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  set bE := Module.finBasis ℝ E with hbE
  have htr : LinearMap.trace ℝ E
      ((coordCurvatureOp G x u w : E →L[ℝ] E) : E →ₗ[ℝ] E)
      = ∑ j, bE.coord j (coordCurvatureOp G x u w (bE j)) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bE, Matrix.trace]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  unfold coordRicci
  rw [htr, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := coord_first_bianchi hdiff hΓsymm (bE j) u w
  have hanti : coordCurvatureOp G x w (bE j)
      = -coordCurvatureOp G x (bE j) w :=
    coordCurvatureOp_antisymm G x w (bE j)
  have h4 : bE.coord j (coordCurvatureOp G x (bE j) u w)
      + bE.coord j (coordCurvatureOp G x u w (bE j))
      + bE.coord j (coordCurvatureOp G x w (bE j) u) = 0 := by
    have := congrArg (fun z ↦ bE.coord j z) h
    simpa [map_add] using this
  have h5 : bE.coord j (coordCurvatureOp G x w (bE j) u)
      = - bE.coord j (coordCurvatureOp G x (bE j) w u) := by
    rw [hanti]
    simp
  rw [h5] at h4
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The metric pairs the Christoffel operator back to the corrector
functional**: `G(Γ(u,v), ·) = Φ_G(u,v)` under invertibility. -/
theorem g_christoffelClosedOp
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E} (hinv : (G x).IsInvertible)
    (u v : E) :
    G x (christoffelClosedOp G x u v)
      = LinearMap.toContinuousLinearMap
        (christoffelFunctional G x u v) := by
  rw [christoffelClosedOp_apply]
  exact (hinv.inverse_apply_eq.mp rfl).symm

/--
**METRIC COMPATIBILITY OF THE COORDINATE LEVI-CIVITA CONNECTION**:
the derivative of the metric is recovered from the Christoffel
operator — `D_u G(a,b) = G(Γ(u,a),b) + G(a,Γ(u,b))`. The defining
property of the Levi-Civita corrector, verified for the closed form.
-/
theorem coord_metric_compatible
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : (G x).IsInvertible) (u a b : E) :
    (fderiv ℝ G x u) a b
      = G x (christoffelClosedOp G x u a) b
        + G x a (christoffelClosedOp G x u b) := by
  have h1 : G x (christoffelClosedOp G x u a) b
      = (1 / 2 : ℝ) * ((fderiv ℝ G x u) a b + (fderiv ℝ G x a) u b
        - (fderiv ℝ G x b) u a) := by
    rw [g_christoffelClosedOp G hinv u a]
    rfl
  have h2 : G x a (christoffelClosedOp G x u b)
      = (1 / 2 : ℝ) * ((fderiv ℝ G x u) b a + (fderiv ℝ G x b) u a
        - (fderiv ℝ G x a) u b) := by
    rw [hGsymm x a (christoffelClosedOp G x u b),
      g_christoffelClosedOp G hinv u b]
    rfl
  rw [h1, h2, fderiv_metric_symm G hGd hGsymm u b a]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Product rule for the pairing `y ↦ G_y(Γ_y(u,a), b)`: the derivative
splits into the metric-derivative and Christoffel-derivative terms. -/
theorem hasFDerivAt_g_christoffel_left
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hdiffΓ : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (u a b : E) :
    HasFDerivAt (fun y ↦ G y (christoffelClosedOp G y u a) b)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp
        ((G x).comp ((ContinuousLinearMap.apply ℝ E a).comp
            (fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x))
          + (fderiv ℝ G x).flip (christoffelClosedOp G x u a))) x := by
  have hVa : HasFDerivAt (fun y ↦ christoffelClosedOp G y u a)
      ((ContinuousLinearMap.apply ℝ E a).comp
        (fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x)) x :=
    (ContinuousLinearMap.apply ℝ E a).hasFDerivAt.comp x
      (hdiffΓ u).hasFDerivAt
  have hA : HasFDerivAt (fun y ↦ (G y) (christoffelClosedOp G y u a))
      ((G x).comp ((ContinuousLinearMap.apply ℝ E a).comp
          (fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x))
        + (fderiv ℝ G x).flip (christoffelClosedOp G x u a)) x :=
    hGd.hasFDerivAt.clm_apply hVa
  exact (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hA

/-- Product rule for the pairing `y ↦ G_y(a, Γ_y(u,b))`. -/
theorem hasFDerivAt_g_christoffel_right
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hdiffΓ : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (u a b : E) :
    HasFDerivAt (fun y ↦ G y a (christoffelClosedOp G y u b))
      ((G x a).comp ((ContinuousLinearMap.apply ℝ E b).comp
          (fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x))
        + ((fderiv ℝ G x).flip a).flip
          (christoffelClosedOp G x u b)) x := by
  have hVb : HasFDerivAt (fun y ↦ christoffelClosedOp G y u b)
      ((ContinuousLinearMap.apply ℝ E b).comp
        (fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x)) x :=
    (ContinuousLinearMap.apply ℝ E b).hasFDerivAt.comp x
      (hdiffΓ u).hasFDerivAt
  have hGa : HasFDerivAt (fun y ↦ (G y) a)
      ((fderiv ℝ G x).flip a) x := by
    simpa using hGd.hasFDerivAt.clm_apply (hasFDerivAt_const a x)
  exact hGa.clm_apply hVb

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**G-SKEW-SYMMETRY OF THE COORDINATE CURVATURE OPERATOR**: for a `C²`
symmetric invertible metric, `G(R(u,w)a, b) + G(a, R(u,w)b) = 0` — the
curvature acts skew-adjointly. Differentiating metric compatibility a
second time, Schwarz symmetry kills the second-derivative terms and the
mixed Christoffel terms cancel in pairs.
-/
theorem coordCurvatureOp_skew
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (u w a b : E) :
    G x (coordCurvatureOp G x u w a) b
      + G x a (coordCurvatureOp G x u w b) = 0 := by
  have hGd : ∀ y : E, DifferentiableAt ℝ G y := fun y ↦
    (hGC2.differentiable (by norm_num)).differentiableAt
  have hd2G : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hGC2.contDiffAt).fderiv_right (m := 1)
      (by norm_num)).differentiableAt one_ne_zero
  -- The compatibility identity as a function identity.
  have F1 : ∀ p : E, (fun y ↦ (fderiv ℝ G y) p a b)
      = fun y ↦ G y (christoffelClosedOp G y p a) b
        + G y a (christoffelClosedOp G y p b) := by
    intro p
    funext y
    exact coord_metric_compatible (hGd y) hGsymm (hinv y) p a b
  -- Equate the two derivatives.
  have hEq : ∀ p q : E, (fderiv ℝ (fderiv ℝ G) x q) p a b
      = (G x ((fderiv ℝ (fun y ↦ christoffelClosedOp G y p) x q) a) b
          + (fderiv ℝ G x q) (christoffelClosedOp G x p a) b)
        + (G x a ((fderiv ℝ (fun y ↦ christoffelClosedOp G y p) x q) b)
          + (fderiv ℝ G x q) a (christoffelClosedOp G x p b)) := by
    intro p q
    have hL := hasFDerivAt_g_christoffel_left (hGd x) hdiffΓ p a b
    have hR := hasFDerivAt_g_christoffel_right (hGd x) hdiffΓ p a b
    have hsum := hL.add hR
    have h1 := HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E →L[ℝ] E →L[ℝ] ℝ) hd2G.hasFDerivAt (hasFDerivAt_const p x)
    have h2 := HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E →L[ℝ] ℝ) h1 (hasFDerivAt_const a x)
    have h3 := HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := ℝ) h2 (hasFDerivAt_const b x)
    rw [F1 p] at h3
    have huniq := h3.unique hsum
    have happ := congrArg (fun (Φ : E →L[ℝ] ℝ) ↦ Φ q) huniq
    simpa using happ
  -- Schwarz symmetry.
  have hsymm2 : IsSymmSndFDerivAt ℝ G x :=
    (hGC2.contDiffAt).isSymmSndFDerivAt (by norm_num)
  have hsch : (fderiv ℝ (fderiv ℝ G) x w) u a b
      = (fderiv ℝ (fderiv ℝ G) x u) w a b := by
    rw [hsymm2 w u]
  -- Expand the metric-derivative terms by compatibility at `x`.
  have hDG : ∀ (q p r : E), (fderiv ℝ G x q) p r
      = G x (christoffelClosedOp G x q p) r
        + G x p (christoffelClosedOp G x q r) :=
    fun q p r ↦ coord_metric_compatible (hGd x) hGsymm (hinv x) q p r
  -- Assemble.
  have h1 := hEq u w
  have h2 := hEq w u
  rw [hsch] at h1
  unfold coordCurvatureOp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  rw [hDG w (christoffelClosedOp G x u a) b,
    hDG w a (christoffelClosedOp G x u b)] at h1
  rw [hDG u (christoffelClosedOp G x w a) b,
    hDG u a (christoffelClosedOp G x w b)] at h2
  linarith [h1, h2]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**SYMMETRY OF THE COORDINATE RICCI FORM**: for a `C²` symmetric
invertible metric, `Ric(u,w) = Ric(w,u)` — the curvature trace vanishes
by skew-adjointness, so the contracted first Bianchi identity closes
the antisymmetric part. The Ricci-symmetry hypothesis of the
singularity machinery, discharged.
-/
theorem coordRicci_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (u w : E) :
    coordRicci G x u w = coordRicci G x w u := by
  have hGd : ∀ y : E, DifferentiableAt ℝ G y := fun y ↦
    (hGC2.differentiable (by norm_num)).differentiableAt
  have hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a :=
    fun y a b ↦ christoffelClosedOp_symm (hGd y) hGsymm a b
  -- The metric as a bilinear form, nondegenerate by invertibility.
  set bx : LinearMap.BilinForm ℝ E :=
    LinearMap.mk₂ ℝ (fun v w ↦ G x v w)
      (fun a b c ↦ by simp) (fun c a b ↦ by simp)
      (fun a b c ↦ by simp) (fun c a b ↦ by simp) with hbx
  have hzero : ∀ v : E, (∀ z : E, G x v z = 0) → v = 0 := by
    intro v hv
    have hGv : G x v = 0 := by
      ext z
      exact hv z
    have hvid := (hinv x).inverse_apply_eq.mpr (rfl :
      G x v = (G x) v)
    rw [hGv] at hvid
    rw [← hvid]
    simp
  have hbnd : bx.Nondegenerate := by
    constructor
    · refine fun v hv ↦ hzero v fun z ↦ hv z
    · refine fun v hv ↦ hzero v fun z ↦ ?_
      rw [hGsymm x v z]
      exact hv z
  -- The curvature trace vanishes by skew-adjointness.
  have htr0 : LinearMap.trace ℝ E
      ((coordCurvatureOp G x u w : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0 := by
    apply trace_eq_zero_of_skew bx hbnd
    intro v z
    have hsk := coordCurvatureOp_skew hGC2 hGsymm hinv hdiffΓ u w v z
    show G x (coordCurvatureOp G x u w v) z
      = - (G x v (coordCurvatureOp G x u w z))
    linarith
  have hanti := coordRicci_antisymm_part hdiffΓ hΓsymm u w
  rw [htr0] at hanti
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Set in
/--
**The conditional Ricci-flow singularity theorem, with Ricci symmetry
derived**: for a family of `C²` symmetric invertible metrics, the
Ricci-symmetry input is supplied by `coordRicci_symm` — the named
geometric hypotheses shrink to the contracted second Bianchi identity
and the model regularity data.
-/
theorem hamilton_ricci_flow_singularity'
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbs : LinearMap.IsSymm b)
    (hbpos : ∀ v : E, v ≠ 0 → 0 < b v v)
    [Nontrivial E]
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {H : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {T m₀ B : ℝ} (hm₀ : 0 < m₀) (hT0 : 0 ≤ T)
    (hGC2 : ∀ t : ℝ, ContDiff ℝ 2 (Gt t))
    (hd2 : ∀ (t : ℝ) (x : E) (u : E),
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x)
    (hinv : ∀ (t : ℝ) (x : E), (Gt t x).IsInvertible)
    (hGsymm : ∀ (t : ℝ) (x : E) (v w : E), Gt t x v w = Gt t x w v)
    (hdG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      HasDerivAt (fun s ↦ Gt s x) (H t x) t)
    (hmix : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, ∀ p q r : E,
      HasDerivAt (fun s ↦ (fderiv ℝ (Gt s) x p) q r)
        ((fderiv ℝ (H t) x p) q r) t)
    (hmix2 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, ∀ p v : E,
      HasDerivAt
        (fun s ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt s) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t) (H t) y p) x v) t)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      H t x = (-2 : ℝ) • coordRicciForm (Gt t) x (hd2 t x))
    (hBianchi : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ∑ j, ricciDeriv (Gt t) (H t) x
          ((Gt t x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord j)))
          ((Module.finBasis ℝ E) j)
        = modelLaplacian b hb (fun y ↦ coordScalar (Gt t) y) x)
    (hR_cont : Continuous ↿(fun t x ↦ coordScalar (Gt t) x))
    (hspace : ∀ t ∈ Icc (0 : ℝ) T,
      ContDiff ℝ 2 (fun x ↦ coordScalar (Gt t) x))
    (hsa : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, ∀ p q : E,
      b (coordRicciEndo (Gt t) x (hd2 t x) p) q
        = b p (coordRicciEndo (Gt t) x (hd2 t x) q))
    (hmin_int : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      IsMinOn (fun y ↦ coordScalar (Gt t) y) K x →
        IsLocalMin (fun y ↦ coordScalar (Gt t) y) x)
    (hRB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K, coordScalar (Gt t) x ≤ B)
    (h0 : ∀ x ∈ K, m₀ ≤ coordScalar (Gt 0) x) :
    T < (Module.finrank ℝ E : ℝ) / (2 * m₀) :=
  hamilton_ricci_flow_singularity b hb hbs hbpos hK hKne hm₀ hT0
    hd2 hinv hGsymm
    (fun t x u w ↦ coordRicci_symm (hGC2 t) (hGsymm t) (hinv t)
      (fun p ↦ hd2 t x p) u w)
    hdG hmix hmix2 hH hBianchi hR_cont hspace hsa hmin_int hRB h0

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Generic evaluation-commutation**: for any differentiable
CLM-valued family, applying the spatial derivative commutes with
evaluation at a fixed vector. -/
theorem fderiv_clm_family_apply
    {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : E → F →L[ℝ] V} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) (v : E) (c : F) :
    (fderiv ℝ Φ x v) c = fderiv ℝ (fun y ↦ Φ y c) x v := by
  have h := (ContinuousLinearMap.apply ℝ V c).hasFDerivAt.comp x
    hΦ.hasFDerivAt
  have hfd : fderiv ℝ (fun y ↦ Φ y c) x
      = (ContinuousLinearMap.apply ℝ V c).comp (fderiv ℝ Φ x) :=
    h.fderiv
  rw [hfd]
  rfl

/-- **Differentiability of the curvature family**: with differentiable
Christoffel families and differentiable family gradients, the
coordinate curvature operator is a differentiable operator family. -/
theorem differentiableAt_coordCurvatureOp_family
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (u w : E) :
    DifferentiableAt ℝ (fun y ↦ coordCurvatureOp G y u w) x := by
  unfold coordCurvatureOp
  have h1 : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z w) y u) x := by
    have := DifferentiableAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E →L[ℝ] E) (hdd w) (differentiableAt_const u)
    exact this
  have h2 : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z u) y w) x := by
    have := DifferentiableAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E →L[ℝ] E) (hdd u) (differentiableAt_const w)
    exact this
  have h3 : DifferentiableAt ℝ (fun y ↦
      (christoffelClosedOp G y u).comp (christoffelClosedOp G y w)) x :=
    (hdiffΓ x u).clm_comp (hdiffΓ x w)
  have h4 : DifferentiableAt ℝ (fun y ↦
      (christoffelClosedOp G y w).comp (christoffelClosedOp G y u)) x :=
    (hdiffΓ x w).clm_comp (hdiffΓ x u)
  exact ((h1.sub h2).add h3).sub h4

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The covariant derivative of the curvature in coordinates**:
`∇_v R(u,w)` — the flat derivative of the operator family corrected by
the Christoffel action on the endomorphism part and on both plane
slots. The object whose cyclic sum is the second Bianchi identity. -/
noncomputable def covCurvDeriv (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v u w : E) : E →L[ℝ] E :=
  fderiv ℝ (fun y ↦ coordCurvatureOp G y u w) x v
    + (christoffelClosedOp G x v).comp (coordCurvatureOp G x u w)
    - (coordCurvatureOp G x u w).comp (christoffelClosedOp G x v)
    - coordCurvatureOp G x (christoffelClosedOp G x v u) w
    - coordCurvatureOp G x u (christoffelClosedOp G x v w)

/-- The covariant curvature derivative is antisymmetric in the plane. -/
theorem covCurvDeriv_antisymm (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v u w : E) :
    covCurvDeriv G x v u w = -covCurvDeriv G x v w u := by
  unfold covCurvDeriv
  have hfam : (fun y ↦ coordCurvatureOp G y u w)
      = fun y ↦ -coordCurvatureOp G y w u := by
    funext y
    exact coordCurvatureOp_antisymm G y u w
  rw [hfam, fderiv_fun_neg]
  rw [coordCurvatureOp_antisymm G x u w,
    coordCurvatureOp_antisymm G x (christoffelClosedOp G x v u) w,
    coordCurvatureOp_antisymm G x u (christoffelClosedOp G x v w)]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_comp]
  abel

/-- The covariant curvature derivative vanishes for constant metrics. -/
theorem covCurvDeriv_const_eq_zero (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (x v u w : E) :
    covCurvDeriv (fun _ : E ↦ G₀) x v u w = 0 := by
  unfold covCurvDeriv
  have hfam : (fun y : E ↦ coordCurvatureOp (fun _ : E ↦ G₀) y u w)
      = fun _ : E ↦ 0 := by
    funext y
    exact coordCurvatureOp_const_eq_zero G₀ y u w
  rw [hfam, fderiv_fun_const]
  rw [coordCurvatureOp_const_eq_zero, coordCurvatureOp_const_eq_zero,
    coordCurvatureOp_const_eq_zero,
    christoffelClosedOp_const_eq_zero]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Product rule for the Christoffel composition family. -/
theorem fderiv_christoffelClosedOp_comp_apply
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (u w v : E) :
    fderiv ℝ (fun y ↦ (christoffelClosedOp G y u).comp
        (christoffelClosedOp G y w)) x v
      = (christoffelClosedOp G x u).comp
          ((fderiv ℝ (fun y ↦ christoffelClosedOp G y w) x) v)
        + ((fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x) v).comp
          (christoffelClosedOp G x w) := by
  have h := fderiv_clm_comp (hdiffΓ u) (hdiffΓ w)
  rw [show fderiv ℝ (fun y ↦ (christoffelClosedOp G y u).comp
      (christoffelClosedOp G y w)) x v
    = (fderiv ℝ (fun y ↦ (christoffelClosedOp G y u).comp
        (christoffelClosedOp G y w)) x) v from rfl, h]
  simp

/--
**The derivative of the curvature family**: the spatial derivative of
`y ↦ R_y(u,w)` splits into the second derivatives of the Christoffel
families and the Christoffel-gradient cross terms — the expansion that
feeds the second Bianchi cancellation.
-/
theorem fderiv_coordCurvatureOp_family
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (u w v : E) :
    fderiv ℝ (fun y ↦ coordCurvatureOp G y u w) x v
      = (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z w)) x v) u
        - (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z u)) x v) w
        + ((christoffelClosedOp G x u).comp
            ((fderiv ℝ (fun y ↦ christoffelClosedOp G y w) x) v)
          + ((fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x) v).comp
            (christoffelClosedOp G x w))
        - ((christoffelClosedOp G x w).comp
            ((fderiv ℝ (fun y ↦ christoffelClosedOp G y u) x) v)
          + ((fderiv ℝ (fun y ↦ christoffelClosedOp G y w) x) v).comp
            (christoffelClosedOp G x u)) := by
  have h1 : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z w) y u) x :=
    DifferentiableAt.clm_apply (𝕜 := ℝ) (G := E) (H := E →L[ℝ] E)
      (hdd w) (differentiableAt_const u)
  have h2 : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z u) y w) x :=
    DifferentiableAt.clm_apply (𝕜 := ℝ) (G := E) (H := E →L[ℝ] E)
      (hdd u) (differentiableAt_const w)
  have h3 : DifferentiableAt ℝ (fun y ↦
      (christoffelClosedOp G y u).comp (christoffelClosedOp G y w)) x :=
    (hdiffΓ u).clm_comp (hdiffΓ w)
  have h4 : DifferentiableAt ℝ (fun y ↦
      (christoffelClosedOp G y w).comp (christoffelClosedOp G y u)) x :=
    (hdiffΓ w).clm_comp (hdiffΓ u)
  have hF : HasFDerivAt (fun y ↦ coordCurvatureOp G y u w)
      ((((fderiv ℝ (fun y ↦ fderiv ℝ
            (fun z ↦ christoffelClosedOp G z w) y u) x)
          - fderiv ℝ (fun y ↦ fderiv ℝ
            (fun z ↦ christoffelClosedOp G z u) y w) x)
        + fderiv ℝ (fun y ↦ (christoffelClosedOp G y u).comp
            (christoffelClosedOp G y w)) x)
        - fderiv ℝ (fun y ↦ (christoffelClosedOp G y w).comp
            (christoffelClosedOp G y u)) x) x :=
    ((h1.hasFDerivAt.sub h2.hasFDerivAt).add h3.hasFDerivAt).sub
      h4.hasFDerivAt
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [fderiv_christoffelClosedOp_comp_apply hdiffΓ u w v,
    fderiv_christoffelClosedOp_comp_apply hdiffΓ w u v]
  have e1 : fderiv ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z w) y u) x v
      = (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z w)) x v)
        u := (fderiv_clm_family_apply (hdd w) v u).symm
  have e2 : fderiv ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z u) y w) x v
      = (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z u)) x v)
        w := (fderiv_clm_family_apply (hdd u) v w).symm
  rw [e1, e2]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Slot symmetry of the Christoffel gradient**: differentiating the
torsion symmetry, the family index and the applied vector of the
Christoffel gradient commute. -/
theorem fderiv_christoffelClosedOp_slot_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (p q v : E) :
    (fderiv ℝ (fun y ↦ christoffelClosedOp G y p) x v) q
      = (fderiv ℝ (fun y ↦ christoffelClosedOp G y q) x v) p := by
  rw [fderiv_clm_family_apply (hdiffΓ p) v q,
    fderiv_clm_family_apply (hdiffΓ q) v p]
  have hfe : (fun y ↦ christoffelClosedOp G y p q)
      = fun y ↦ christoffelClosedOp G y q p :=
    funext fun y ↦ hΓsymm y p q
  rw [hfe]

/-- **Slot symmetry of the second Christoffel gradient**: the family
index and the applied vector commute through two derivatives. -/
theorem sndFDeriv_christoffelClosedOp_slot_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (p q a v : E) :
    (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z p)) x a v) q
      = (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z q)) x a v)
        p := by
  have hΦp : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y v) x :=
    DifferentiableAt.clm_apply (𝕜 := ℝ) (G := E) (H := E →L[ℝ] E)
      (hdd p) (differentiableAt_const v)
  have hΦq : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z q) y v) x :=
    DifferentiableAt.clm_apply (𝕜 := ℝ) (G := E) (H := E →L[ℝ] E)
      (hdd q) (differentiableAt_const v)
  have e1 : (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z p))
      x a v) q
      = fderiv ℝ (fun y ↦ (fderiv ℝ
          (fun z ↦ christoffelClosedOp G z p) y v) q) x a := by
    rw [fderiv_clm_family_apply (hdd p) a v]
    rw [fderiv_clm_family_apply hΦp a q]
  have e2 : (fderiv ℝ (fderiv ℝ (fun z ↦ christoffelClosedOp G z q))
      x a v) p
      = fderiv ℝ (fun y ↦ (fderiv ℝ
          (fun z ↦ christoffelClosedOp G z q) y v) p) x a := by
    rw [fderiv_clm_family_apply (hdd q) a v]
    rw [fderiv_clm_family_apply hΦq a p]
  rw [e1, e2]
  have hfe : (fun y ↦ (fderiv ℝ
        (fun z ↦ christoffelClosedOp G z p) y v) q)
      = fun y ↦ (fderiv ℝ
        (fun z ↦ christoffelClosedOp G z q) y v) p :=
    funext fun y ↦ fderiv_christoffelClosedOp_slot_symm
      (fun r ↦ hdiffΓ y r) hΓsymm p q v
  rw [hfe]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**THE SECOND BIANCHI IDENTITY IN COORDINATES**: the cyclic sum of the
covariant curvature derivative vanishes —
`∇_v R(u,w) + ∇_u R(w,v) + ∇_w R(v,u) = 0`. The second derivatives of
the Christoffel families cancel by Schwarz symmetry, the cubic
Christoffel terms cancel cyclically, and every mixed term cancels in
pairs under torsion symmetry.
-/
theorem coord_second_bianchi
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hsymΓ : ∀ p : E, IsSymmSndFDerivAt ℝ
      (fun z ↦ christoffelClosedOp G z p) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (u v w : E) :
    covCurvDeriv G x v u w + covCurvDeriv G x u w v
      + covCurvDeriv G x w v u = 0 := by
  unfold covCurvDeriv
  rw [fderiv_coordCurvatureOp_family hdiffΓ hdd u w v,
    fderiv_coordCurvatureOp_family hdiffΓ hdd w v u,
    fderiv_coordCurvatureOp_family hdiffΓ hdd v u w]
  unfold coordCurvatureOp
  rw [hΓsymm x v u, hΓsymm x w v, hΓsymm x w u]
  rw [(hsymΓ w) v u, (hsymΓ u) v w, (hsymΓ v) u w]
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_assoc]
  abel

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The covariant Ricci derivative in coordinates**: the basis-trace
contraction of the covariant curvature derivative — `∇_v Ric(u,w)`. -/
noncomputable def covRicciDeriv (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v u w : E) : ℝ :=
  ∑ j, (Module.finBasis ℝ E).coord j
    ((covCurvDeriv G x v ((Module.finBasis ℝ E) j) u) w)

/-- **The curvature divergence in coordinates**: the contraction of the
covariant curvature derivative over the differentiation slot. -/
noncomputable def curvDivergence (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u w z : E) : ℝ :=
  ∑ j, (Module.finBasis ℝ E).coord j
    ((covCurvDeriv G x ((Module.finBasis ℝ E) j) u w) z)

/--
**THE FIRST CONTRACTED BIANCHI IDENTITY**: contracting the second
Bianchi identity once — `∇_v Ric(w,z) − ∇_w Ric(v,z) + div R(w,v)z = 0`.
-/
theorem coord_first_contracted_bianchi
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hsymΓ : ∀ p : E, IsSymmSndFDerivAt ℝ
      (fun z ↦ christoffelClosedOp G z p) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (v w z : E) :
    covRicciDeriv G x v w z + curvDivergence G x w v z
      - covRicciDeriv G x w v z = 0 := by
  unfold covRicciDeriv curvDivergence
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro j _
  set bj := (Module.finBasis ℝ E) j
  have hB := coord_second_bianchi hdiffΓ hdd hsymΓ hΓsymm bj v w
  have hanti : covCurvDeriv G x w v bj = -covCurvDeriv G x w bj v :=
    covCurvDeriv_antisymm G x w v bj
  rw [hanti] at hB
  -- hB : cCD x v bj w + cCD x bj w v + (−cCD x w bj v) = 0
  have happ := congrArg (fun (A : E →L[ℝ] E) ↦
    (Module.finBasis ℝ E).coord j (A z)) hB
  simpa [map_add, map_sub, map_neg] using happ

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**PAIR SYMMETRY OF THE LOWERED CURVATURE**: `⟨R(u,w)a, b⟩ = ⟨R(a,b)u, w⟩`
— the classical diamond argument from plane antisymmetry, pairing
skew-symmetry, and the first Bianchi identity.
-/
theorem coordCurvature_pair_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (u w a b : E) :
    G x (coordCurvatureOp G x u w a) b
      = G x (coordCurvatureOp G x a b u) w := by
  have hGd : ∀ y : E, DifferentiableAt ℝ G y := fun y ↦
    (hGC2.differentiable (by norm_num)).differentiableAt
  have hΓsymm : ∀ (y : E) (p q : E),
      christoffelClosedOp G y p q = christoffelClosedOp G y q p :=
    fun y p q ↦ christoffelClosedOp_symm (hGd y) hGsymm p q
  have hA1 : ∀ p q r s : E, G x (coordCurvatureOp G x p q r) s
      = -G x (coordCurvatureOp G x q p r) s := by
    intro p q r s
    rw [coordCurvatureOp_antisymm G x p q]
    simp
  have hA2 : ∀ p q r s : E, G x (coordCurvatureOp G x p q r) s
      = -G x (coordCurvatureOp G x p q s) r := by
    intro p q r s
    have h := coordCurvatureOp_skew hGC2 hGsymm hinv hdiffΓ p q r s
    have hsw := hGsymm x r (coordCurvatureOp G x p q s)
    linarith
  have hcyc : ∀ p q r s : E, G x (coordCurvatureOp G x p q r) s
      + G x (coordCurvatureOp G x q r p) s
      + G x (coordCurvatureOp G x r p q) s = 0 := by
    intro p q r s
    have h := coord_first_bianchi hdiffΓ hΓsymm p q r
    have happ := congrArg (fun e ↦ G x e s) h
    simpa [map_add] using happ
  have B1 := hcyc u w a b
  have B2 := hcyc w a b u
  have B3 := hcyc a b u w
  have B4 := hcyc b u w a
  have f1 := hA1 a u w b
  have f2 := hA2 w a b u
  have f3 := hA2 a b w u
  have f4 := hA2 b w a u
  have f5 := hA2 b u a w
  have f6 := hA2 u a b w
  have f7 := hA2 u w b a
  have f8 := hA1 w b u a
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The Ricci divergence in coordinates**: `div Ric(u) =
Σₖ ∇_{♯bᵏ} Ric(u, bₖ)` — the raised contraction of the covariant Ricci
derivative over its differentiation slot. -/
noncomputable def ricciDivergence (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u : E) : ℝ :=
  ∑ k, covRicciDeriv G x
    ((G x).inverse (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord k)))
    u ((Module.finBasis ℝ E) k)

/-- **The contracted scalar derivative**: `Σₖ ∇_w Ric(♯bᵏ, bₖ)` — the
covariant derivative of the scalar contraction in direction `w`. -/
noncomputable def scalarContractionDeriv (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x w : E) : ℝ :=
  ∑ k, covRicciDeriv G x w
    ((G x).inverse (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord k)))
    ((Module.finBasis ℝ E) k)

/--
**THE TWICE-CONTRACTED BIANCHI IDENTITY, raw form**: contracting the
first contracted Bianchi identity against the inverse metric —
`div Ric(w) + Σₖ div R(w, ♯bᵏ)bₖ = ∇_w(tr Ric)`.
-/
theorem coord_twice_contracted_bianchi_raw
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hsymΓ : ∀ p : E, IsSymmSndFDerivAt ℝ
      (fun z ↦ christoffelClosedOp G z p) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (w : E) :
    ricciDivergence G x w
      + ∑ k, curvDivergence G x w
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k)))
          ((Module.finBasis ℝ E) k)
      = scalarContractionDeriv G x w := by
  unfold ricciDivergence scalarContractionDeriv
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro k _
  have h := coord_first_contracted_bianchi hdiffΓ hdd hsymΓ hΓsymm
    ((G x).inverse (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord k)))
    w ((Module.finBasis ℝ E) k)
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Product rule for the pairing of a metric family against a
differentiable operator family: `y ↦ G_y(V_y(a), b)`. -/
theorem hasFDerivAt_g_op_family
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {V : E → E →L[ℝ] E} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hV : DifferentiableAt ℝ V x) (a b : E) :
    HasFDerivAt (fun y ↦ G y (V y a) b)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp
        ((G x).comp ((ContinuousLinearMap.apply ℝ E a).comp
            (fderiv ℝ V x))
          + (fderiv ℝ G x).flip (V x a))) x := by
  have hVa : HasFDerivAt (fun y ↦ V y a)
      ((ContinuousLinearMap.apply ℝ E a).comp (fderiv ℝ V x)) x :=
    (ContinuousLinearMap.apply ℝ E a).hasFDerivAt.comp x hV.hasFDerivAt
  have hA : HasFDerivAt (fun y ↦ (G y) (V y a))
      ((G x).comp ((ContinuousLinearMap.apply ℝ E a).comp
          (fderiv ℝ V x))
        + (fderiv ℝ G x).flip (V x a)) x :=
    hGd.hasFDerivAt.clm_apply hVa
  exact (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hA

/--
**PAIR SYMMETRY OF THE COVARIANT CURVATURE DERIVATIVE**:
`⟨(∇_vR)(u,w)a, b⟩ = ⟨(∇_vR)(a,b)u, w⟩` — differentiating the pointwise
pair symmetry, the metric-compatibility corrections match in pairs
through the pointwise pair symmetry itself.
-/
theorem covCurvDeriv_pair_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (v u w a b : E) :
    G x (covCurvDeriv G x v u w a) b
      = G x (covCurvDeriv G x v a b u) w := by
  have hGd : ∀ y : E, DifferentiableAt ℝ G y := fun y ↦
    (hGC2.differentiable (by norm_num)).differentiableAt
  -- Pointwise pair symmetry, at every point.
  have hps : ∀ (y : E) (p q r s : E),
      G y (coordCurvatureOp G y p q r) s
        = G y (coordCurvatureOp G y r s p) q := by
    intro y p q r s
    exact coordCurvature_pair_symm hGC2 hGsymm hinv
      (fun m ↦ hdiffΓ y m) p q r s
  -- Differentiability of the curvature families at x (and everywhere
  -- needed).
  have hRfam : ∀ p q : E, DifferentiableAt ℝ
      (fun y ↦ coordCurvatureOp G y p q) x :=
    fun p q ↦ differentiableAt_coordCurvatureOp_family hdiffΓ hdd p q
  -- Derivatives of the two pairing fields.
  have hL := hasFDerivAt_g_op_family (hGd x) (hRfam u w) a b
  have hR := hasFDerivAt_g_op_family (hGd x) (hRfam a b) u w
  have hP : (fun y ↦ G y (coordCurvatureOp G y u w a) b)
      = fun y ↦ G y (coordCurvatureOp G y a b u) w := by
    funext y
    exact hps y u w a b
  rw [hP] at hL
  have huniq := hL.unique hR
  have hEq := congrArg (fun (Φ : E →L[ℝ] ℝ) ↦ Φ v) huniq
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.flip_apply] at hEq
  -- Metric compatibility for the metric-derivative terms.
  have hDG : ∀ (p r : E), (fderiv ℝ G x v) p r
      = G x (christoffelClosedOp G x v p) r
        + G x p (christoffelClosedOp G x v r) :=
    fun p r ↦ coord_metric_compatible (hGd x) hGsymm (hinv x) v p r
  rw [hDG (coordCurvatureOp G x u w a) b,
    hDG (coordCurvatureOp G x a b u) w] at hEq
  -- Expand the goal through the covariant-derivative definition.
  unfold covCurvDeriv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  -- Pair-symmetry instances matching the correction terms.
  have ps1 := hps x u w (christoffelClosedOp G x v a) b
  have ps2 := hps x (christoffelClosedOp G x v u) w a b
  have ps3 := hps x u (christoffelClosedOp G x v w) a b
  have ps4 := hps x u w a (christoffelClosedOp G x v b)
  -- Symmetry conversions for second-slot Christoffel pairings.
  have sy1 := hGsymm x (coordCurvatureOp G x u w a)
    (christoffelClosedOp G x v b)
  have sy2 := hGsymm x (coordCurvatureOp G x a b u)
    (christoffelClosedOp G x v w)
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The covariant curvature derivative is additive in its second plane
slot. -/
theorem covCurvDeriv_add_snd
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (v u w₁ w₂ : E) :
    covCurvDeriv G x v u (w₁ + w₂)
      = covCurvDeriv G x v u w₁ + covCurvDeriv G x v u w₂ := by
  unfold covCurvDeriv
  have hfam : (fun y ↦ coordCurvatureOp G y u (w₁ + w₂))
      = fun y ↦ coordCurvatureOp G y u w₁
        + coordCurvatureOp G y u w₂ := by
    funext y
    exact coordCurvatureOp_add_snd G (fun p ↦ hdiffΓ y p) u w₁ w₂
  rw [hfam, fderiv_fun_add
    (differentiableAt_coordCurvatureOp_family hdiffΓ hdd u w₁)
    (differentiableAt_coordCurvatureOp_family hdiffΓ hdd u w₂)]
  rw [coordCurvatureOp_add_snd G (fun p ↦ hdiffΓ x p) u w₁ w₂,
    map_add, coordCurvatureOp_add_snd G (fun p ↦ hdiffΓ x p) u
      (christoffelClosedOp G x v w₁) (christoffelClosedOp G x v w₂)]
  have hslot : coordCurvatureOp G x (christoffelClosedOp G x v u)
      (w₁ + w₂)
      = coordCurvatureOp G x (christoffelClosedOp G x v u) w₁
        + coordCurvatureOp G x (christoffelClosedOp G x v u) w₂ :=
    coordCurvatureOp_add_snd G (fun p ↦ hdiffΓ x p) _ w₁ w₂
  rw [hslot]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp]
  abel

/-- The covariant curvature derivative is homogeneous in its second
plane slot. -/
theorem covCurvDeriv_smul_snd
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (v u : E) (c : ℝ) (w : E) :
    covCurvDeriv G x v u (c • w) = c • covCurvDeriv G x v u w := by
  unfold covCurvDeriv
  have hfam : (fun y ↦ coordCurvatureOp G y u (c • w))
      = fun y ↦ c • coordCurvatureOp G y u w := by
    funext y
    exact coordCurvatureOp_smul_snd G (fun p ↦ hdiffΓ y p) u c w
  rw [hfam, fderiv_fun_const_smul
    (differentiableAt_coordCurvatureOp_family hdiffΓ hdd u w) c]
  rw [coordCurvatureOp_smul_snd G (fun p ↦ hdiffΓ x p) u c w,
    map_smul, coordCurvatureOp_smul_snd G (fun p ↦ hdiffΓ x p) u c
      (christoffelClosedOp G x v w)]
  have hslot : coordCurvatureOp G x (christoffelClosedOp G x v u)
      (c • w)
      = c • coordCurvatureOp G x (christoffelClosedOp G x v u) w :=
    coordCurvatureOp_smul_snd G (fun p ↦ hdiffΓ x p) _ c w
  rw [hslot]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp]
  module

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Coordinates against a symmetric invertible metric are raised
pairings: `bʲ(m) = G(m, ♯bʲ)`. -/
theorem coord_eq_g_raised
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hinv : (G x).IsInvertible)
    (hGsymm : ∀ p q : E, G x p q = G x q p)
    (j : Fin (Module.finrank ℝ E)) (m : E) :
    (Module.finBasis ℝ E).coord j m
      = G x m ((G x).inverse (LinearMap.toContinuousLinearMap
        ((Module.finBasis ℝ E).coord j))) := by
  set ρ := LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ E).coord j) with hρ
  have h2 : G x ((G x).inverse ρ) = ρ :=
    (hinv.inverse_apply_eq.mp rfl).symm
  rw [hGsymm m ((G x).inverse ρ), h2]
  rfl

/-- The raised-basis coefficient matrix is symmetric. -/
theorem coord_raised_symm
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hinv : (G x).IsInvertible)
    (hGsymm : ∀ p q : E, G x p q = G x q p)
    (i k : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).coord i
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord k)))
      = (Module.finBasis ℝ E).coord k
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord i))) := by
  rw [coord_eq_g_raised G hinv hGsymm i,
    coord_eq_g_raised G hinv hGsymm k]
  exact hGsymm _ _

/--
**The raised-contraction swap**: for any slotwise-linear scalar form,
contracting the raised index in the first slot equals contracting it in
the second — `Σₖ F(♯bᵏ, bₖ) = Σₖ F(bₖ, ♯bᵏ)`.
-/
theorem sum_raised_contraction_swap
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hinv : (G x).IsInvertible)
    (hGsymm : ∀ p q : E, G x p q = G x q p)
    (F : E → E → ℝ)
    (hadd1 : ∀ p₁ p₂ q, F (p₁ + p₂) q = F p₁ q + F p₂ q)
    (hsmul1 : ∀ (c : ℝ) p q, F (c • p) q = c • F p q)
    (hadd2 : ∀ p q₁ q₂, F p (q₁ + q₂) = F p q₁ + F p q₂)
    (hsmul2 : ∀ (c : ℝ) p q, F p (c • q) = c • F p q) :
    ∑ k, F ((G x).inverse (LinearMap.toContinuousLinearMap
        ((Module.finBasis ℝ E).coord k))) ((Module.finBasis ℝ E) k)
      = ∑ k, F ((Module.finBasis ℝ E) k)
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k))) := by
  set bE := Module.finBasis ℝ E with hbE
  set s : Fin (Module.finrank ℝ E) → E := fun k ↦
    (G x).inverse (LinearMap.toContinuousLinearMap (bE.coord k))
    with hs
  -- Expand the raised vectors in the basis.
  have hrepr : ∀ k, s k = ∑ i, bE.coord i (s k) • bE i := by
    intro k
    exact (bE.sum_repr (s k)).symm
  have hexp1 : ∀ k, F (s k) (bE k)
      = ∑ i, bE.coord i (s k) • F (bE i) (bE k) := by
    intro k
    conv_lhs => rw [hrepr k]
    set L : E →ₗ[ℝ] ℝ :=
      IsLinearMap.mk' (fun p ↦ F p (bE k))
        ⟨fun p₁ p₂ ↦ hadd1 p₁ p₂ (bE k),
         fun c p ↦ hsmul1 c p (bE k)⟩ with hL
    have := map_sum L (fun i ↦ bE.coord i (s k) • bE i) Finset.univ
    simp only [map_smul] at this
    exact this
  have hexp2 : ∀ k, F (bE k) (s k)
      = ∑ i, bE.coord i (s k) • F (bE k) (bE i) := by
    intro k
    conv_lhs => rw [hrepr k]
    set L : E →ₗ[ℝ] ℝ :=
      IsLinearMap.mk' (fun q ↦ F (bE k) q)
        ⟨fun q₁ q₂ ↦ hadd2 (bE k) q₁ q₂,
         fun c q ↦ hsmul2 c (bE k) q⟩ with hL
    have := map_sum L (fun i ↦ bE.coord i (s k) • bE i) Finset.univ
    simp only [map_smul] at this
    exact this
  rw [Finset.sum_congr rfl (fun k _ ↦ hexp1 k),
    Finset.sum_congr rfl (fun k _ ↦ hexp2 k), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [coord_raised_symm G hinv hGsymm i k]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The covariant curvature derivative is additive in its
differentiation slot. -/
theorem covCurvDeriv_add_fst
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (v₁ v₂ u w : E) :
    covCurvDeriv G x (v₁ + v₂) u w
      = covCurvDeriv G x v₁ u w + covCurvDeriv G x v₂ u w := by
  unfold covCurvDeriv
  rw [map_add, christoffelClosedOp_add_fst G x v₁ v₂]
  simp only [ContinuousLinearMap.add_apply]
  rw [coordCurvatureOp_add_snd G hdiffΓ u
    (christoffelClosedOp G x v₁ w) (christoffelClosedOp G x v₂ w)]
  have h3 : coordCurvatureOp G x (christoffelClosedOp G x v₁ u
        + christoffelClosedOp G x v₂ u) w
      = coordCurvatureOp G x (christoffelClosedOp G x v₁ u) w
        + coordCurvatureOp G x (christoffelClosedOp G x v₂ u) w := by
    rw [coordCurvatureOp_antisymm G x _ w,
      coordCurvatureOp_add_snd G hdiffΓ w _ _,
      coordCurvatureOp_antisymm G x w (christoffelClosedOp G x v₁ u),
      coordCurvatureOp_antisymm G x w (christoffelClosedOp G x v₂ u)]
    abel
  rw [h3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add]
  abel

/-- The covariant curvature derivative is homogeneous in its
differentiation slot. -/
theorem covCurvDeriv_smul_fst
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x)
    (c : ℝ) (v u w : E) :
    covCurvDeriv G x (c • v) u w = c • covCurvDeriv G x v u w := by
  unfold covCurvDeriv
  rw [map_smul, christoffelClosedOp_smul_fst G x c v]
  simp only [ContinuousLinearMap.smul_apply]
  rw [coordCurvatureOp_smul_snd G hdiffΓ u c
    (christoffelClosedOp G x v w)]
  have h3 : coordCurvatureOp G x (c • christoffelClosedOp G x v u) w
      = c • coordCurvatureOp G x (christoffelClosedOp G x v u) w := by
    rw [coordCurvatureOp_antisymm G x _ w,
      coordCurvatureOp_smul_snd G hdiffΓ w c _,
      coordCurvatureOp_antisymm G x w (christoffelClosedOp G x v u)]
    module
  rw [h3]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul]
  module

/-- **Applied skew-symmetry of the covariant curvature derivative**:
`⟨(∇_vR)(u,w)a, b⟩ = −⟨(∇_vR)(u,w)b, a⟩`, from pair symmetry and plane
antisymmetry. -/
theorem covCurvDeriv_applied_skew
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (v u w a b : E) :
    G x (covCurvDeriv G x v u w a) b
      = -G x (covCurvDeriv G x v u w b) a := by
  rw [covCurvDeriv_pair_symm hGC2 hGsymm hinv hdiffΓ hdd v u w a b,
    covCurvDeriv_pair_symm hGC2 hGsymm hinv hdiffΓ hdd v u w b a]
  rw [covCurvDeriv_antisymm G x v a b]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**THE FIRST BIANCHI IDENTITY FOR THE COVARIANT CURVATURE DERIVATIVE**:
`(∇_vR)(u,w)a + (∇_vR)(w,a)u + (∇_vR)(a,u)w = 0` — differentiating the
pointwise cyclic identity, the Christoffel corrections cancel through
three instances of the pointwise identity itself.
-/
theorem covCurvDeriv_first_bianchi
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a)
    (v u w a : E) :
    covCurvDeriv G x v u w a + covCurvDeriv G x v w a u
      + covCurvDeriv G x v a u w = 0 := by
  have hRfam : ∀ p q : E, DifferentiableAt ℝ
      (fun y ↦ coordCurvatureOp G y p q) x :=
    fun p q ↦ differentiableAt_coordCurvatureOp_family hdiffΓ hdd p q
  -- Vector-valued curvature families and their derivatives.
  have hV : ∀ p q r : E, HasFDerivAt
      (fun y ↦ coordCurvatureOp G y p q r)
      ((ContinuousLinearMap.apply ℝ E r).comp
        (fderiv ℝ (fun y ↦ coordCurvatureOp G y p q) x)) x :=
    fun p q r ↦ (ContinuousLinearMap.apply ℝ E r).hasFDerivAt.comp x
      (hRfam p q).hasFDerivAt
  have hs := ((hV u w a).add (hV w a u)).add (hV a u w)
  have hfun : (((fun y ↦ coordCurvatureOp G y u w a)
        + fun y ↦ coordCurvatureOp G y w a u)
        + fun y ↦ coordCurvatureOp G y a u w)
      = fun _ : E ↦ (0 : E) := by
    funext y
    simp only [Pi.add_apply]
    exact coord_first_bianchi (fun p ↦ hdiffΓ y p) hΓsymm u w a
  rw [hfun] at hs
  have huniq := hs.unique (hasFDerivAt_const (0 : E) x)
  have hD := congrArg (fun (Φ : E →L[ℝ] E) ↦ Φ v) huniq
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.zero_apply] at hD
  -- The three pointwise Bianchi instances absorbing the corrections.
  have hB1 := coord_first_bianchi (fun p ↦ hdiffΓ x p) hΓsymm u w
    (christoffelClosedOp G x v a)
  have hB2 := coord_first_bianchi (fun p ↦ hdiffΓ x p) hΓsymm w a
    (christoffelClosedOp G x v u)
  have hB3 := coord_first_bianchi (fun p ↦ hdiffΓ x p) hΓsymm a u
    (christoffelClosedOp G x v w)
  -- The Christoffel action on the pointwise identity.
  have hΓ0 : christoffelClosedOp G x v (coordCurvatureOp G x u w a)
      + christoffelClosedOp G x v (coordCurvatureOp G x w a u)
      + christoffelClosedOp G x v (coordCurvatureOp G x a u w) = 0 := by
    have hc := coord_first_bianchi (fun p ↦ hdiffΓ x p) hΓsymm u w a
    have h0 : christoffelFunctional G x v 0 = (0 : E →ₗ[ℝ] ℝ) := by
      have := christoffelFunctional_smul_snd G x v 0 0
      simpa using this
    have := congrArg (fun m ↦ christoffelClosedOp G x v m) hc
    simpa [map_add, h0] using this
  unfold covCurvDeriv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  have hgoal : (fderiv ℝ (fun y ↦ coordCurvatureOp G y u w) x v) a
      + christoffelClosedOp G x v (coordCurvatureOp G x u w a)
      - coordCurvatureOp G x u w (christoffelClosedOp G x v a)
      - coordCurvatureOp G x (christoffelClosedOp G x v u) w a
      - coordCurvatureOp G x u (christoffelClosedOp G x v w) a
      + ((fderiv ℝ (fun y ↦ coordCurvatureOp G y w a) x v) u
      + christoffelClosedOp G x v (coordCurvatureOp G x w a u)
      - coordCurvatureOp G x w a (christoffelClosedOp G x v u)
      - coordCurvatureOp G x (christoffelClosedOp G x v w) a u
      - coordCurvatureOp G x w (christoffelClosedOp G x v a) u)
      + ((fderiv ℝ (fun y ↦ coordCurvatureOp G y a u) x v) w
      + christoffelClosedOp G x v (coordCurvatureOp G x a u w)
      - coordCurvatureOp G x a u (christoffelClosedOp G x v w)
      - coordCurvatureOp G x (christoffelClosedOp G x v a) u w
      - coordCurvatureOp G x a (christoffelClosedOp G x v u) w)
      = (((fderiv ℝ (fun y ↦ coordCurvatureOp G y u w) x v) a
          + (fderiv ℝ (fun y ↦ coordCurvatureOp G y w a) x v) u)
          + (fderiv ℝ (fun y ↦ coordCurvatureOp G y a u) x v) w)
        + (christoffelClosedOp G x v (coordCurvatureOp G x u w a)
          + christoffelClosedOp G x v (coordCurvatureOp G x w a u)
          + christoffelClosedOp G x v (coordCurvatureOp G x a u w))
        - (coordCurvatureOp G x u w (christoffelClosedOp G x v a)
          + coordCurvatureOp G x w (christoffelClosedOp G x v a) u
          + coordCurvatureOp G x (christoffelClosedOp G x v a) u w)
        - (coordCurvatureOp G x w a (christoffelClosedOp G x v u)
          + coordCurvatureOp G x a (christoffelClosedOp G x v u) w
          + coordCurvatureOp G x (christoffelClosedOp G x v u) w a)
        - (coordCurvatureOp G x a u (christoffelClosedOp G x v w)
          + coordCurvatureOp G x u (christoffelClosedOp G x v w) a
          + coordCurvatureOp G x (christoffelClosedOp G x v w) a u) := by
    abel
  rw [hgoal, hD, hΓ0, hB1, hB2, hB3]
  simp

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**THE MIDDLE TERM OF THE TWICE-CONTRACTED BIANCHI IS THE RICCI
DIVERGENCE**: `Σₖ div R(w, ♯bᵏ)bₖ = div Ric(w)` — by pair symmetry, the
raised-contraction swaps, the first Bianchi identity for `∇R`, plane
antisymmetry, and the vanishing of the skew trace.
-/
theorem curvDivergence_contraction_eq_ricciDivergence
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (w : E) :
    ∑ k, curvDivergence G x w
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord k)))
        ((Module.finBasis ℝ E) k)
      = ricciDivergence G x w := by
  have hGd : ∀ y : E, DifferentiableAt ℝ G y := fun y ↦
    (hGC2.differentiable (by norm_num)).differentiableAt
  have hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a :=
    fun y a b ↦ christoffelClosedOp_symm (hGd y) hGsymm a b
  set bE := Module.finBasis ℝ E with hbE
  set S : Fin (Module.finrank ℝ E) → E := fun k ↦
    (G x).inverse (LinearMap.toContinuousLinearMap (bE.coord k))
    with hS
  have hcoord : ∀ (j : Fin (Module.finrank ℝ E)) (m : E),
      bE.coord j m = G x m (S j) :=
    fun j m ↦ coord_eq_g_raised G (hinv x) (hGsymm x) j m
  -- Generic: the skew trace vanishes.
  have hskewtrace : ∀ M : E →L[ℝ] E,
      (∀ p q : E, G x (M p) q = -G x (M q) p) →
      ∑ j, G x (M (bE j)) (S j) = 0 := by
    intro M hMskew
    have hsw := sum_raised_contraction_swap G (hinv x) (hGsymm x)
      (fun p q ↦ G x (M p) q)
      (fun p₁ p₂ q ↦ by dsimp only; rw [map_add]; simp)
      (fun c p q ↦ by dsimp only; rw [map_smul]; simp)
      (fun p q₁ q₂ ↦ by dsimp only; simp)
      (fun c p q ↦ by dsimp only; simp)
    have hneg : ∑ j, G x (M (S j)) (bE j)
        = -∑ j, G x (M (bE j)) (S j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [hMskew (S j) (bE j)]
    rw [hneg] at hsw
    linarith
  -- Unfold both sides to pairing form.
  unfold curvDivergence ricciDivergence covRicciDeriv
  -- Step A1–A2: pair symmetry then the (1,3)-slot swap, per k.
  have hstep : ∀ k, ∑ j, bE.coord j
      ((covCurvDeriv G x (bE j) w (S k)) (bE k))
      = ∑ j, G x ((covCurvDeriv G x (S j) (bE k) (bE j)) w) (S k) := by
    intro k
    have h1 : ∀ j, bE.coord j
        ((covCurvDeriv G x (bE j) w (S k)) (bE k))
        = G x ((covCurvDeriv G x (bE j) (bE k) (S j)) w) (S k) := by
      intro j
      rw [hcoord j]
      exact covCurvDeriv_pair_symm hGC2 hGsymm hinv hdiffΓ hdd
        (bE j) w (S k) (bE k) (S j)
    rw [Finset.sum_congr rfl fun j _ ↦ h1 j]
    exact sum_raised_contraction_swap G (hinv x) (hGsymm x)
      (fun p q ↦ G x ((covCurvDeriv G x q (bE k) p) w) (S k))
      (fun p₁ p₂ q ↦ by
        dsimp only
        rw [covCurvDeriv_add_snd hdiffΓ hdd q (bE k) p₁ p₂]
        simp [map_add])
      (fun c p q ↦ by
        dsimp only
        rw [covCurvDeriv_smul_snd hdiffΓ hdd q (bE k) c p]
        simp)
      (fun p q₁ q₂ ↦ by
        dsimp only
        rw [covCurvDeriv_add_fst (fun m ↦ hdiffΓ x m) q₁ q₂ (bE k) p]
        simp [map_add])
      (fun c p q ↦ by
        dsimp only
        rw [covCurvDeriv_smul_fst (fun m ↦ hdiffΓ x m) c q (bE k) p]
        simp)
  rw [Finset.sum_congr rfl fun k _ ↦ hstep k]
  -- Step A3: rename the indices.
  rw [Finset.sum_comm]
  -- Steps A4–A6: first Bianchi, plane antisymmetry, skew trace.
  apply Finset.sum_congr rfl
  intro k _
  have hFB : ∀ j, (covCurvDeriv G x (S k) (bE j) (bE k)) w
      = -(covCurvDeriv G x (S k) (bE k) w) (bE j)
        - (covCurvDeriv G x (S k) w (bE j)) (bE k) := by
    intro j
    have h := covCurvDeriv_first_bianchi hdiffΓ hdd hΓsymm
      (S k) (bE j) (bE k) w
    have h' : covCurvDeriv G x (S k) (bE j) (bE k) w
        + covCurvDeriv G x (S k) (bE k) w (bE j)
        + covCurvDeriv G x (S k) w (bE j) (bE k) = 0 := h
    linear_combination (norm := module) h'
  have hPA : ∀ j, (covCurvDeriv G x (S k) w (bE j)) (bE k)
      = -(covCurvDeriv G x (S k) (bE j) w) (bE k) := by
    intro j
    rw [covCurvDeriv_antisymm G x (S k) w (bE j)]
    simp
  have hterm : ∀ j, G x ((covCurvDeriv G x (S k) (bE j) (bE k)) w)
      (S j)
      = -G x ((covCurvDeriv G x (S k) (bE k) w) (bE j)) (S j)
        + G x ((covCurvDeriv G x (S k) (bE j) w) (bE k)) (S j) := by
    intro j
    rw [hFB j, hPA j]
    simp [map_add, map_sub]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_add_distrib]
  -- The skew-trace sum vanishes.
  have hzero : ∑ j, -G x ((covCurvDeriv G x (S k) (bE k) w) (bE j))
      (S j) = 0 := by
    have := hskewtrace (covCurvDeriv G x (S k) (bE k) w)
      (fun p q ↦ covCurvDeriv_applied_skew hGC2 hGsymm hinv hdiffΓ hdd
        (S k) (bE k) w p q)
    rw [Finset.sum_neg_distrib, this, neg_zero]
  rw [hzero, zero_add]
  -- The remaining sum is the Ricci-divergence summand.
  exact Finset.sum_congr rfl fun j _ ↦ (hcoord j _).symm

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**THE TWICE-CONTRACTED BIANCHI IDENTITY**: `2 · div Ric(w) = ∇_w(tr Ric)`
— the classical identity behind Hamilton's evolution equation, from the
raw double contraction and the middle-term identification.
-/
theorem coord_twice_contracted_bianchi
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hsymΓ : ∀ p : E, IsSymmSndFDerivAt ℝ
      (fun z ↦ christoffelClosedOp G z p) x)
    (w : E) :
    2 * ricciDivergence G x w = scalarContractionDeriv G x w := by
  have hGd : ∀ y : E, DifferentiableAt ℝ G y := fun y ↦
    (hGC2.differentiable (by norm_num)).differentiableAt
  have hΓsymm : ∀ (y : E) (a b : E),
      christoffelClosedOp G y a b = christoffelClosedOp G y b a :=
    fun y a b ↦ christoffelClosedOp_symm (hGd y) hGsymm a b
  have hraw := coord_twice_contracted_bianchi_raw
    (fun p ↦ hdiffΓ x p) hdd hsymΓ hΓsymm (x := x) w
  have hmid := curvDivergence_contraction_eq_ricciDivergence
    hGC2 hGsymm hinv hdiffΓ hdd w
  rw [hmid] at hraw
  linarith

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The covariant derivative of a 2-tensor family in coordinates**:
`(∇_v H)(p,q) = D_v H(p,q) − H(Γ(v,p), q) − H(p, Γ(v,q))`. -/
noncomputable def covTensor2Deriv (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v p q : E) : ℝ :=
  (fderiv ℝ H x v) p q
    - H x (christoffelClosedOp G x v p) q
    - H x p (christoffelClosedOp G x v q)

/--
**`δΓ` IN COVARIANT FORM**: the variation of the Christoffel symbols is
the classical half-sum of covariant derivatives of the variation tensor
— `G(δΓ(u,v), w) = ½[(∇_uH)(v,w) + (∇_vH)(u,w) − (∇_wH)(u,v)]`. The
Christoffel corrections regroup through torsion symmetry and the
symmetry of `H`.
-/
theorem g_christoffelDeriv
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : (G x).IsInvertible)
    (hHsymm : ∀ p q : E, H x p q = H x q p)
    (u v w : E) :
    G x (christoffelDeriv G H x u v) w
      = (1 / 2 : ℝ) * (covTensor2Deriv G H x u v w
        + covTensor2Deriv G H x v u w
        - covTensor2Deriv G H x w u v) := by
  have hGiG : ∀ f : E →L[ℝ] ℝ, G x ((G x).inverse f) = f :=
    fun f ↦ (hinv.inverse_apply_eq.mp rfl).symm
  -- Pair the variation with the metric.
  have hpair : G x (christoffelDeriv G H x u v) w
      = LinearMap.toContinuousLinearMap
          (christoffelFunctional H x u v) w
        - H x (christoffelClosedOp G x u v) w := by
    unfold christoffelDeriv
    rw [map_add]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      map_neg, hGiG]
    have hop : (G x).inverse (LinearMap.toContinuousLinearMap
        (christoffelFunctional G x u v)) = christoffelClosedOp G x u v :=
      (christoffelClosedOp_apply G x u v).symm
    rw [hop]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
    ring
  rw [hpair]
  -- Expand the corrector functional and the covariant derivatives.
  show (1 / 2 : ℝ) * ((fderiv ℝ H x u) v w + (fderiv ℝ H x v) u w
      - (fderiv ℝ H x w) u v) - H x (christoffelClosedOp G x u v) w = _
  unfold covTensor2Deriv
  have hΓuv := christoffelClosedOp_symm hGd hGsymm u v
  have hΓuw := christoffelClosedOp_symm hGd hGsymm u w
  have hΓvw := christoffelClosedOp_symm hGd hGsymm v w
  have hs1 := hHsymm v (christoffelClosedOp G x u w)
  have hs2 := hHsymm u (christoffelClosedOp G x v w)
  rw [hΓuv] at *
  linarith [hHsymm (christoffelClosedOp G x w u) v,
    hHsymm (christoffelClosedOp G x w v) u,
    congrArg (fun m ↦ H x m w) hΓuv,
    congrArg (fun m ↦ H x v m) hΓuw.symm,
    congrArg (fun m ↦ H x u m) hΓvw.symm]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The covariant derivative of the Christoffel variation**:
`(∇_v δΓ)(p, z)` — the flat derivative of the `δΓ`-operator family
corrected by the Christoffel action on the value and both slots. -/
noncomputable def covDeltaGammaDeriv (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v p z : E) : E :=
  (fderiv ℝ (fun y ↦ christoffelDerivOp G H y p) x v) z
    + christoffelClosedOp G x v (christoffelDerivOp G H x p z)
    - christoffelDerivOp G H x (christoffelClosedOp G x v p) z
    - christoffelDerivOp G H x p (christoffelClosedOp G x v z)

/--
**`δRm` IS THE ANTISYMMETRIZED COVARIANT DERIVATIVE OF `δΓ`** (the
Lichnerowicz form): `δRm(u,w)z = (∇_u δΓ)(w,z) − (∇_w δΓ)(u,z)` — the
slot corrections cancel through torsion symmetry, and the commutator
terms are exactly the Christoffel actions.
-/
theorem curvatureDerivOp_eq_covDeltaGamma
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hΓsymm : ∀ a b : E,
      christoffelClosedOp G x a b = christoffelClosedOp G x b a)
    (u w z : E) :
    curvatureDerivOp G H x u w z
      = covDeltaGammaDeriv G H x u w z
        - covDeltaGammaDeriv G H x w u z := by
  unfold covDeltaGammaDeriv curvatureDerivOp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  rw [hΓsymm u w]
  abel

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The divergence of the Christoffel variation**: `div δΓ(u,w) =
Σᵢ ⟨bⁱ, (∇_{bᵢ}δΓ)(u,w)⟩` — the basis-trace contraction of `∇δΓ`
pairing the differentiation slot with the value coordinate. -/
noncomputable def deltaGammaDivergence (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u w : E) : ℝ :=
  ∑ i, (Module.finBasis ℝ E).coord i
    (covDeltaGammaDeriv G H x ((Module.finBasis ℝ E) i) u w)

/-- **The trace-derivative of the Christoffel variation**:
`Σᵢ ⟨bⁱ, (∇_u δΓ)(bᵢ,w)⟩` — the covariant `u`-derivative of the
first-slot trace contraction of `δΓ`. -/
noncomputable def deltaGammaContractionDeriv
    (G H : E → E →L[ℝ] E →L[ℝ] ℝ) (x u w : E) : ℝ :=
  ∑ i, (Module.finBasis ℝ E).coord i
    (covDeltaGammaDeriv G H x u ((Module.finBasis ℝ E) i) w)

/--
**THE CONTRACTED LICHNEROWICZ FORMULA**: the variation of the Ricci
form is the divergence of the Christoffel variation minus the
covariant derivative of its trace —
`δRic(u,w) = div δΓ(u,w) − ∇_u(tr δΓ)(w)`.
-/
theorem ricciDeriv_eq_deltaGamma_contractions
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hΓsymm : ∀ a b : E,
      christoffelClosedOp G x a b = christoffelClosedOp G x b a)
    (u w : E) :
    ricciDeriv G H x u w
      = deltaGammaDivergence G H x u w
        - deltaGammaContractionDeriv G H x u w := by
  unfold ricciDeriv deltaGammaDivergence deltaGammaContractionDeriv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [curvatureDerivOp_eq_covDeltaGamma hΓsymm
    ((Module.finBasis ℝ E) i) u w, map_sub]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The raised divergence of `δΓ`**: `Σⱼ div δΓ(♯bʲ, bⱼ)` — the
metric trace of the `δΓ`-divergence, the leading term of the raised
Ricci variation that drives the scalar evolution. -/
noncomputable def deltaGammaDivergenceTrace (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) : ℝ :=
  ∑ j, deltaGammaDivergence G H x
    ((G x).inverse (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord j)))
    ((Module.finBasis ℝ E) j)

/-- **The raised trace-derivative of `δΓ`**: `Σⱼ ∇_{♯bʲ}(tr δΓ)(bⱼ)` —
the metric trace of the covariant `δΓ`-trace derivative. -/
noncomputable def deltaGammaContractionDerivTrace
    (G H : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∑ j, deltaGammaContractionDeriv G H x
    ((G x).inverse (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord j)))
    ((Module.finBasis ℝ E) j)

/--
**THE RAISED CONTRACTED LICHNEROWICZ IDENTITY**: the `hBianchi`
left-hand side — the raised metric trace of the Ricci variation —
splits as the raised `δΓ`-divergence minus the raised `δΓ`-trace
derivative. This is the exact term whose identification with the
scalar Laplacian closes the Hamilton evolution equation.
-/
theorem ricciDeriv_raised_trace_eq
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hΓsymm : ∀ a b : E,
      christoffelClosedOp G x a b = christoffelClosedOp G x b a) :
    ∑ j, ricciDeriv G H x
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j)
      = deltaGammaDivergenceTrace G H x
        - deltaGammaContractionDerivTrace G H x := by
  unfold deltaGammaDivergenceTrace deltaGammaContractionDerivTrace
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact ricciDeriv_eq_deltaGamma_contractions hΓsymm _ _

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**METRIC COMPATIBILITY FOR THE `δΓ` COVARIANT DERIVATIVE**: pairing the
covariant derivative of the Christoffel variation against the metric is
the covariant derivative of the pairing — the directional derivative of
`y ↦ G_y(δΓ_y(p,z), w)` minus the three lower-slot Christoffel
corrections. Because `∇G = 0`, the metric passes through the covariant
derivative, turning `G(∇δΓ, ·)` into the genuine `(0,4)`-tensor
derivative of `G(δΓ, ·)`.
-/
theorem g_covDeltaGammaDeriv
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} {p : E}
    (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : (G x).IsInvertible)
    (hVd : DifferentiableAt ℝ (fun y ↦ christoffelDerivOp G H y p) x)
    (v z w : E) :
    G x (covDeltaGammaDeriv G H x v p z) w
      = (fderiv ℝ (fun y ↦ G y (christoffelDerivOp G H y p z) w) x) v
        - G x (christoffelDerivOp G H x
            (christoffelClosedOp G x v p) z) w
        - G x (christoffelDerivOp G H x p
            (christoffelClosedOp G x v z)) w
        - G x (christoffelDerivOp G H x p z)
            (christoffelClosedOp G x v w) := by
  -- The product rule for the metric pairing of the `δΓ`-vector field.
  have hfd : HasFDerivAt
      (fun y ↦ G y (christoffelDerivOp G H y p z) w) _ x :=
    hasFDerivAt_g_op_family hGd hVd z w
  have hDv := congrArg (fun (Φ : E →L[ℝ] ℝ) ↦ Φ v) hfd.fderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.flip_apply] at hDv
  -- Metric compatibility: the metric-derivative term is the two
  -- Christoffel actions on the value and the test vector.
  have hmc := coord_metric_compatible hGd hGsymm hinv v
    (christoffelDerivOp G H x p z) w
  -- Distribute `G x (·) w` through the covariant-derivative sum.
  unfold covDeltaGammaDeriv
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  rw [hDv, hmc]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**THE `δΓ` PAIRING AS A FUNCTION OF THE BASE POINT**: at every point the
metric pairing `G_y(δΓ_y(p,z), w)` equals the Lichnerowicz half-sum of
covariant derivatives of the variation tensor `H`. This is
`g_christoffelDeriv` promoted to a functional identity over the base
point, the form ready to be differentiated along a flow direction to
produce second covariant derivatives of `H`.
-/
theorem g_christoffelDerivOp_pairing_eq
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hGd : ∀ y : E, DifferentiableAt ℝ G y)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hHsymm : ∀ (y : E) (p q : E), H y p q = H y q p)
    (p z w : E) :
    (fun y ↦ G y (christoffelDerivOp G H y p z) w)
      = fun y ↦ (1 / 2 : ℝ) * (covTensor2Deriv G H y p z w
        + covTensor2Deriv G H y z p w
        - covTensor2Deriv G H y w p z) := by
  funext y
  rw [christoffelDerivOp_apply]
  exact g_christoffelDeriv (hGd y) hGsymm (hinv y) (hHsymm y) p z w

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The covariant 2-tensor derivative is additive in its differentiation
direction. -/
theorem covTensor2Deriv_add_dir
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (v₁ v₂ p q : E) :
    covTensor2Deriv G H x (v₁ + v₂) p q
      = covTensor2Deriv G H x v₁ p q + covTensor2Deriv G H x v₂ p q := by
  unfold covTensor2Deriv
  simp only [christoffelClosedOp_add_fst, map_add,
    ContinuousLinearMap.add_apply]
  ring

/-- The covariant 2-tensor derivative is homogeneous in its
differentiation direction. -/
theorem covTensor2Deriv_smul_dir
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (c : ℝ) (v p q : E) :
    covTensor2Deriv G H x (c • v) p q
      = c * covTensor2Deriv G H x v p q := by
  unfold covTensor2Deriv
  simp only [christoffelClosedOp_smul_fst, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The covariant 2-tensor derivative is additive in its first tensor
slot. -/
theorem covTensor2Deriv_add_left
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (v p₁ p₂ q : E) :
    covTensor2Deriv G H x v (p₁ + p₂) q
      = covTensor2Deriv G H x v p₁ q + covTensor2Deriv G H x v p₂ q := by
  unfold covTensor2Deriv
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

/-- The covariant 2-tensor derivative is additive in its second tensor
slot. -/
theorem covTensor2Deriv_add_right
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (v p q₁ q₂ : E) :
    covTensor2Deriv G H x v p (q₁ + q₂)
      = covTensor2Deriv G H x v p q₁ + covTensor2Deriv G H x v p q₂ := by
  unfold covTensor2Deriv
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

/-- The covariant 2-tensor derivative is homogeneous in its first tensor
slot. -/
theorem covTensor2Deriv_smul_left
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (c : ℝ) (v p q : E) :
    covTensor2Deriv G H x v (c • p) q
      = c * covTensor2Deriv G H x v p q := by
  unfold covTensor2Deriv
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The covariant 2-tensor derivative is homogeneous in its second tensor
slot. -/
theorem covTensor2Deriv_smul_right
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (c : ℝ) (v p q : E) :
    covTensor2Deriv G H x v p (c • q)
      = c * covTensor2Deriv G H x v p q := by
  unfold covTensor2Deriv
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The metric as a bilinear form**: the underlying `BilinForm` of a
continuous metric tensor `m : E →L E →L ℝ`, the form the curved Laplacian
raises indices against. This adapter lets the metric family `Gt t` serve
as the index-raising data `b` of `curvedLaplacian`, so the genuine
Laplace–Beltrami operator of the flow can be named. -/
noncomputable def metricBilin (m : E →L[ℝ] E →L[ℝ] ℝ) :
    LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w ↦ m v w)
    (fun a b c ↦ by simp) (fun c a b ↦ by simp)
    (fun a b c ↦ by simp) (fun c a b ↦ by simp)

@[simp] theorem metricBilin_apply (m : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    metricBilin m v w = m v w := rfl

/-- **The metric bilinear form is nondegenerate** whenever the metric is
invertible — the index-raising data the curved Laplacian requires. -/
theorem metricBilin_nondeg {m : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ v w : E, m v w = m w v) (hinv : m.IsInvertible) :
    (metricBilin m).Nondegenerate := by
  have hzero : ∀ v : E, (∀ z : E, m v z = 0) → v = 0 := by
    intro v hv
    have hmv : m v = 0 := by ext z; exact hv z
    have hvid := hinv.inverse_apply_eq.mpr (rfl : m v = m v)
    rw [hmv] at hvid
    rw [← hvid]; simp
  constructor
  · exact fun v hv ↦ hzero v fun z ↦ by
      simpa using hv z
  · refine fun v hv ↦ hzero v fun z ↦ ?_
    rw [hsymm v z]
    simpa using hv z

/--
**THE CURVED LAPLACIAN IS THE METRIC-RAISED TRACE OF THE COVARIANT
HESSIAN**: against the metric family `y ↦ metricBilin (G y)`, the
Laplace–Beltrami operator is the basis-raised contraction
`Δ_g f = Σⱼ Hess f(♯bʲ, bⱼ)`. This converts the abstract trace defining
`curvedLaplacian` into the concrete basis contraction produced by the
Bianchi machinery — the shape needed to identify it with the Ricci
variation.
-/
theorem curvedLaplacian_eq_raised_sum
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (f : E → ℝ) :
    curvedLaplacian G (fun y ↦ metricBilin (G y))
        (fun y ↦ metricBilin_nondeg (hGsymm y) (hinv y)) f x
      = ∑ j, covariantHessian G (fun y ↦ metricBilin (G y))
          (fun y ↦ metricBilin_nondeg (hGsymm y) (hinv y)) f x
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord j)))
          ((Module.finBasis ℝ E) j) := by
  set bb : E → LinearMap.BilinForm ℝ E := fun y ↦ metricBilin (G y) with hbb
  set hbnd : ∀ y, (bb y).Nondegenerate :=
    fun y ↦ metricBilin_nondeg (hGsymm y) (hinv y) with hhb
  set Bsharp : E →ₗ[ℝ] E :=
    (LinearMap.BilinForm.toDual (bb x) (hbnd x)).symm.toLinearMap ∘ₗ
      covariantHessianLin G bb hbnd f x with hBsharp
  -- The pairing identity: raising the covariant Hessian and pairing back
  -- with the metric recovers the covariant Hessian.
  have hpair : ∀ v w : E,
      G x (Bsharp v) w = covariantHessian G bb hbnd f x v w := by
    intro v w
    have heq : (LinearMap.BilinForm.toDual (bb x) (hbnd x)) (Bsharp v)
        = covariantHessianLin G bb hbnd f x v := by
      rw [hBsharp]
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe]
      exact LinearEquiv.apply_symm_apply _ _
    have h2 := congrArg (fun ψ ↦ ψ w) heq
    simp only [LinearMap.BilinForm.toDual_def] at h2
    have h3 : covariantHessianLin G bb hbnd f x v w
        = covariantHessian G bb hbnd f x v w := by
      simp only [covariantHessianLin, LinearMap.mk₂_apply]
    rw [h3] at h2
    exact h2
  have key : (∑ j, covariantHessian G bb hbnd f x
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j))
      = LinearMap.trace ℝ E Bsharp := by
    rw [← sum_g_raised_eq_trace G x (hinv x) Bsharp]
    exact Finset.sum_congr rfl fun j _ ↦ (hpair _ _).symm
  rw [key]
  unfold curvedLaplacian
  rfl

/--
**THE CURVED LAPLACIAN IN EXPLICIT COORDINATE FORM**: against the metric
the Laplace–Beltrami operator is the basis-raised sum of the flat
second derivative minus the Christoffel correction —
`Δ_g f = Σⱼ [D²f(♯bʲ, bⱼ) − Df(Γ(♯bʲ, bⱼ))]`. This is the precise shape
the variation-of-Ricci side must match.
-/
theorem curvedLaplacian_eq_raised_hessian_sum
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (f : E → ℝ) :
    curvedLaplacian G (fun y ↦ metricBilin (G y))
        (fun y ↦ metricBilin_nondeg (hGsymm y) (hinv y)) f x
      = ∑ j, ((fderiv ℝ (fderiv ℝ f) x
            ((G x).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord j)))
            ((Module.finBasis ℝ E) j))
          - (fderiv ℝ f x) (christoffelClosedOp G x
              ((G x).inverse (LinearMap.toContinuousLinearMap
                ((Module.finBasis ℝ E).coord j)))
              ((Module.finBasis ℝ E) j))) := by
  rw [curvedLaplacian_eq_raised_sum G hGsymm hinv f]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show christoffelClosedOp G x
      ((G x).inverse (LinearMap.toContinuousLinearMap
        ((Module.finBasis ℝ E).coord j)))
      ((Module.finBasis ℝ E) j)
      = christoffelAt G x (metricBilin (G x))
          (metricBilin_nondeg (hGsymm x) (hinv x))
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord j)))
          ((Module.finBasis ℝ E) j)
    from christoffelClosedOp_eq_christoffelAt G (metricBilin (G x))
      (metricBilin_nondeg (hGsymm x) (hinv x))
      (fun v w ↦ metricBilin_apply (G x) v w) _ _]
  rfl

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**THE SPATIAL DERIVATIVE OF THE RAISED INDEX**: differentiating the
inverse-metric raising `y ↦ (G y)⁻¹ φ` of a fixed covector along a
direction `v` gives `−(G x)⁻¹((D_v G)((G x)⁻¹ φ))` — the spatial analog
of the flow-time inverse-derivative formula, obtained by differentiating
the pairing identity `G_y((G y)⁻¹ φ) = φ`. This is the term whose
metric-compatibility cancellation against the Christoffel correction
yields `∇R = dR`.
-/
theorem hasFDerivAt_inverse_raise
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hG : DifferentiableAt ℝ G x)
    (hev : ∀ᶠ y in nhds x, (G y).IsInvertible)
    (φ : E →L[ℝ] ℝ) :
    HasFDerivAt (fun y ↦ (G y).inverse φ)
      (-(((G x).inverse).comp
          ((fderiv ℝ G x).flip ((G x).inverse φ)))) x := by
  have hinv : (G x).IsInvertible := hev.self_of_nhds
  -- Differentiability of the operator-inverse path, then the raised path.
  have hInvDiff : DifferentiableAt ℝ (fun y ↦ (G y).inverse) x :=
    ((hinv.contDiffAt_map_inverse (n := 1)).differentiableAt
      one_ne_zero).comp x hG
  have hψ : DifferentiableAt ℝ (fun y ↦ (G y).inverse φ) x :=
    hInvDiff.clm_apply (differentiableAt_const φ)
  set B' : E →L[ℝ] E := fderiv ℝ (fun y ↦ (G y).inverse φ) x with hB'
  have hB : HasFDerivAt (fun y ↦ (G y).inverse φ) B' x := hψ.hasFDerivAt
  -- The pairing `G_y ((G y)⁻¹ φ)` is eventually `φ`.
  have hid : (fun y ↦ (G y) ((G y).inverse φ)) =ᶠ[nhds x] fun _ ↦ φ := by
    filter_upwards [hev] with y hy
    obtain ⟨e, he⟩ := hy
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact e.apply_symm_apply φ
  -- Differentiate the pairing by the product rule.
  have hpair : HasFDerivAt (fun y ↦ (G y) ((G y).inverse φ))
      ((G x).comp B' + (fderiv ℝ G x).flip ((G x).inverse φ)) x :=
    hG.hasFDerivAt.clm_apply hB
  -- Being eventually constant forces the derivative to vanish.
  have hzero : (G x).comp B' + (fderiv ℝ G x).flip ((G x).inverse φ) = 0 :=
    hpair.unique ((hasFDerivAt_const φ x).congr_of_eventuallyEq hid)
  -- Solve for `B'`.
  have hBA : (G x).comp B' = -((fderiv ℝ G x).flip ((G x).inverse φ)) := by
    linear_combination (norm := abel) hzero
  have h1 := congrArg (fun L ↦ ((G x).inverse).comp L) hBA
  simp only at h1
  rw [← ContinuousLinearMap.comp_assoc] at h1
  have hinvG : ((G x).inverse).comp (G x) = ContinuousLinearMap.id ℝ E := by
    obtain ⟨e, he⟩ := hinv
    rw [← he, ContinuousLinearMap.inverse_equiv]
    ext m; simp
  rw [hinvG, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_neg] at h1
  rw [← h1]
  exact hB

/-- **The metric pairing of the raised-index derivative collapses**:
pairing `G_x` against the spatial derivative of `(G·)⁻¹ φ` recovers
minus the metric-derivative covector, the lowering identity
`G_x((G x)⁻¹ ·) = ·` undoing the raise. -/
theorem g_inverse_raise_fderiv
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hinv : (G x).IsInvertible) (φ : E →L[ℝ] ℝ) (v z : E) :
    G x ((-(((G x).inverse).comp
          ((fderiv ℝ G x).flip ((G x).inverse φ)))) v) z
      = -((fderiv ℝ G x v) ((G x).inverse φ) z) := by
  have hGiG : ∀ ξ : E →L[ℝ] ℝ, G x ((G x).inverse ξ) = ξ :=
    fun ξ ↦ (hinv.inverse_apply_eq.mp rfl).symm
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_neg]
  rw [hGiG]

/-- **METRIC COMPATIBILITY FOR THE RAISED-INDEX DERIVATIVE**: the spatial
derivative of `(G·)⁻¹ φ`, paired with the metric, is minus the two
Christoffel actions — `∇G = 0` realised on the raised index. This is the
correction term that cancels against the Christoffel piece of the Ricci
covariant derivative to yield `∇R = dR`. -/
theorem g_inverse_raise_metric_compat
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : (G x).IsInvertible) (φ : E →L[ℝ] ℝ) (v z : E) :
    G x ((-(((G x).inverse).comp
          ((fderiv ℝ G x).flip ((G x).inverse φ)))) v) z
      = -(G x (christoffelClosedOp G x v ((G x).inverse φ)) z)
        - G x ((G x).inverse φ) (christoffelClosedOp G x v z) := by
  rw [g_inverse_raise_fderiv hinv φ v z,
    coord_metric_compatible hGd hGsymm hinv v ((G x).inverse φ) z]
  ring

/-- **The coordinate Ricci form is spatially differentiable**: with both
plane arguments fixed, `y ↦ Ric_y(u,w)` differentiates at `x` — the
basis-trace contraction of the differentiable curvature family. This is
the prerequisite for differentiating the scalar curvature in space. -/
theorem differentiableAt_coordRicci_family
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (u w : E) :
    DifferentiableAt ℝ (fun y ↦ coordRicci G y u w) x := by
  unfold coordRicci
  apply DifferentiableAt.fun_sum
  intro i _
  have hfam := differentiableAt_coordCurvatureOp_family hdiffΓ hdd
    ((Module.finBasis ℝ E) i) u
  have happ : DifferentiableAt ℝ
      (fun y ↦ (coordCurvatureOp G y ((Module.finBasis ℝ E) i) u) w) x :=
    hfam.clm_apply (differentiableAt_const w)
  exact (LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ E).coord i)).differentiableAt.comp x happ

/-- **The basis-trace formula**: contracting an endomorphism against the
basis and its dual gives the trace — `Σⱼ ⟨bʲ, Φ bⱼ⟩ = tr Φ`. The
coordinate realisation of the trace through the chosen basis. -/
theorem sum_coord_eq_trace (Φ : E →ₗ[ℝ] E) :
    ∑ j, (Module.finBasis ℝ E).coord j (Φ ((Module.finBasis ℝ E) j))
      = LinearMap.trace ℝ E Φ := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ E) Φ, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]

/-- The coordinate curvature operator is additive in its first plane
slot — by antisymmetry and second-slot additivity. -/
theorem coordCurvatureOp_add_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (v₁ v₂ w : E) :
    coordCurvatureOp G x (v₁ + v₂) w
      = coordCurvatureOp G x v₁ w + coordCurvatureOp G x v₂ w := by
  rw [coordCurvatureOp_antisymm G x (v₁ + v₂) w,
    coordCurvatureOp_add_snd G hdiff w v₁ v₂,
    coordCurvatureOp_antisymm G x w v₁, coordCurvatureOp_antisymm G x w v₂]
  abel

/-- The coordinate curvature operator is homogeneous in its first plane
slot. -/
theorem coordCurvatureOp_smul_fst
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (c : ℝ) (v w : E) :
    coordCurvatureOp G x (c • v) w = c • coordCurvatureOp G x v w := by
  rw [coordCurvatureOp_antisymm G x (c • v) w,
    coordCurvatureOp_smul_snd G hdiff w c v,
    coordCurvatureOp_antisymm G x w v, smul_neg, neg_neg]

/--
**THE TRACE-SLOT CHRISTOFFEL CORRECTIONS CANCEL**: in the covariant
derivative of the Ricci contraction, the correction from the Christoffel
action on the curvature output and the correction from its action on the
traced input are `tr(Γ_v ∘ Ψ)` and `tr(Ψ ∘ Γ_v)` for the curvature-trace
endomorphism `Ψ(p) = R(p,u)w` — equal by trace cyclicity. This is the
metric-naturality of the trace that makes `∇` commute with contraction.
-/
theorem coordRicci_trace_slot_cancel
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (v u w : E) :
    (∑ j, (Module.finBasis ℝ E).coord j
        (christoffelClosedOp G x v
          ((coordCurvatureOp G x ((Module.finBasis ℝ E) j) u) w)))
      = ∑ j, (Module.finBasis ℝ E).coord j
        ((coordCurvatureOp G x (christoffelClosedOp G x v
          ((Module.finBasis ℝ E) j)) u) w) := by
  set Ψ : E →ₗ[ℝ] E :=
    { toFun := fun p ↦ (coordCurvatureOp G x p u) w
      map_add' := fun p₁ p₂ ↦ by
        rw [coordCurvatureOp_add_fst G hdiff p₁ p₂ u,
          ContinuousLinearMap.add_apply]
      map_smul' := fun c p ↦ by
        simp only [RingHom.id_apply]
        rw [coordCurvatureOp_smul_fst G hdiff c p u,
          ContinuousLinearMap.smul_apply] } with hΨ
  have hL : (∑ j, (Module.finBasis ℝ E).coord j
        (christoffelClosedOp G x v
          ((coordCurvatureOp G x ((Module.finBasis ℝ E) j) u) w)))
      = LinearMap.trace ℝ E
        ((christoffelClosedOp G x v).toLinearMap ∘ₗ Ψ) := by
    rw [← sum_coord_eq_trace ((christoffelClosedOp G x v).toLinearMap ∘ₗ Ψ)]
    rfl
  have hR : (∑ j, (Module.finBasis ℝ E).coord j
        ((coordCurvatureOp G x (christoffelClosedOp G x v
          ((Module.finBasis ℝ E) j)) u) w))
      = LinearMap.trace ℝ E
        (Ψ ∘ₗ (christoffelClosedOp G x v).toLinearMap) := by
    rw [← sum_coord_eq_trace (Ψ ∘ₗ (christoffelClosedOp G x v).toLinearMap)]
    rfl
  rw [hL, hR]
  exact LinearMap.trace_comp_comm' _ _

/-- **`fderiv` COMMUTES WITH THE RICCI TRACE CONTRACTION**: the spatial
derivative of `y ↦ Ric_y(u,w)` is the basis-trace contraction of the
spatial derivative of the curvature family — the fixed contraction maps
pass through the Fréchet derivative. -/
theorem fderiv_coordRicci_eq
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (v u w : E) :
    (fderiv ℝ (fun y ↦ coordRicci G y u w) x) v
      = ∑ j, (Module.finBasis ℝ E).coord j
          ((fderiv ℝ (fun y ↦ coordCurvatureOp G y
            ((Module.finBasis ℝ E) j) u) x v) w) := by
  have hfd : ∀ j : Fin (Module.finrank ℝ E), HasFDerivAt
      (fun y ↦ (Module.finBasis ℝ E).coord j
        ((coordCurvatureOp G y ((Module.finBasis ℝ E) j) u) w))
      ((LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)).comp
        ((ContinuousLinearMap.apply ℝ E w).comp
          (fderiv ℝ (fun y ↦ coordCurvatureOp G y
            ((Module.finBasis ℝ E) j) u) x))) x := by
    intro j
    have hR := (differentiableAt_coordCurvatureOp_family hdiffΓ hdd
      ((Module.finBasis ℝ E) j) u).hasFDerivAt
    have hRw := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp x hR
    exact (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord j)).hasFDerivAt.comp x hRw
  have key : HasFDerivAt (fun y ↦ coordRicci G y u w)
      (∑ j, (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)).comp
        ((ContinuousLinearMap.apply ℝ E w).comp
          (fderiv ℝ (fun y ↦ coordCurvatureOp G y
            ((Module.finBasis ℝ E) j) u) x))) x :=
    HasFDerivAt.fun_sum fun j _ ↦ hfd j
  rw [key.fderiv, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rfl

/--
**THE COVARIANT RICCI DERIVATIVE IS THE `(0,2)`-TENSOR DERIVATIVE**: the
curvature-defined `covRicciDeriv` equals the genuine covariant derivative
of the Ricci form — `∇_v Ric(u,w) = D_v Ric(u,w) − Ric(Γ_v u, w) −
Ric(u, Γ_v w)`. The trace-slot Christoffel corrections of the curvature
derivative cancel by trace cyclicity, leaving exactly the tensor
covariant derivative. This is the structural identity that yields
`∇R = dR` for the scalar curvature.
-/
theorem covRicciDeriv_eq_tensor_deriv
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (v u w : E) :
    covRicciDeriv G x v u w
      = (fderiv ℝ (fun y ↦ coordRicci G y u w) x) v
        - coordRicci G x (christoffelClosedOp G x v u) w
        - coordRicci G x u (christoffelClosedOp G x v w) := by
  have hdiff : ∀ p : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y p) x :=
    fun p ↦ hdiffΓ x p
  have hcr : ∀ a b : E, coordRicci G x a b
      = ∑ j, (Module.finBasis ℝ E).coord j
          ((coordCurvatureOp G x ((Module.finBasis ℝ E) j) a) b) :=
    fun a b ↦ rfl
  -- Decompose each basis summand of `covRicciDeriv`.
  have hterm : ∀ j : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).coord j
          ((covCurvDeriv G x v ((Module.finBasis ℝ E) j) u) w)
        = (Module.finBasis ℝ E).coord j
            ((fderiv ℝ (fun y ↦ coordCurvatureOp G y
              ((Module.finBasis ℝ E) j) u) x v) w)
          + (Module.finBasis ℝ E).coord j
              (christoffelClosedOp G x v
                ((coordCurvatureOp G x ((Module.finBasis ℝ E) j) u) w))
          - (Module.finBasis ℝ E).coord j
              ((coordCurvatureOp G x ((Module.finBasis ℝ E) j) u)
                (christoffelClosedOp G x v w))
          - (Module.finBasis ℝ E).coord j
              ((coordCurvatureOp G x (christoffelClosedOp G x v
                ((Module.finBasis ℝ E) j)) u) w)
          - (Module.finBasis ℝ E).coord j
              ((coordCurvatureOp G x ((Module.finBasis ℝ E) j)
                (christoffelClosedOp G x v u)) w) := by
    intro j
    unfold covCurvDeriv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, map_add, map_sub]
  unfold covRicciDeriv
  rw [Finset.sum_congr rfl (fun j _ ↦ hterm j)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← fderiv_coordRicci_eq hdiffΓ hdd v u w,
    coordRicci_trace_slot_cancel G hdiff v u w,
    hcr (christoffelClosedOp G x v u) w,
    hcr u (christoffelClosedOp G x v w)]
  abel

/--
**SYMMETRY OF THE RICCI CHRISTOFFEL-CORRECTION TRACES**: the two
correction traces of the covariant Ricci divergence coincide —
`Σₖ Ric(Γ_w ♯bᵏ, bₖ) = Σₖ Ric(♯bᵏ, Γ_w bₖ)`. Raised-contraction swap
moves the raised index across the contraction, and Ricci symmetry
restores the slot order. Half of the metric-trace cancellation that
turns `∇R` into `dR`.
-/
theorem coordRicci_christoffel_correction_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (w : E) :
    (∑ k, coordRicci G x
        (christoffelClosedOp G x w
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k))))
        ((Module.finBasis ℝ E) k))
      = ∑ k, coordRicci G x
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k)))
          (christoffelClosedOp G x w ((Module.finBasis ℝ E) k)) := by
  have hswap := sum_raised_contraction_swap G (hinv x) (hGsymm x)
    (fun a b ↦ coordRicci G x a (christoffelClosedOp G x w b))
    (fun a₁ a₂ b ↦ coordRicci_add_fst G hdiffΓ a₁ a₂ _)
    (fun c a b ↦ coordRicci_smul_fst G hdiffΓ c a _)
    (fun a b₁ b₂ ↦ by dsimp only; rw [map_add, coordRicci_add_snd])
    (fun c a b ↦ by dsimp only; rw [map_smul, coordRicci_smul_snd])
  have hsymm_sum : (∑ k, coordRicci G x
        (christoffelClosedOp G x w
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k))))
        ((Module.finBasis ℝ E) k))
      = ∑ k, coordRicci G x ((Module.finBasis ℝ E) k)
          (christoffelClosedOp G x w
            ((G x).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k)))) :=
    Finset.sum_congr rfl fun k _ ↦
      coordRicci_symm hGC2 hGsymm hinv hdiffΓ _ _
  rw [hsymm_sum]
  exact hswap.symm

/-- **Basis expansion of the Ricci form's first slot**: `Ric(v,w) =
Σᵢ ⟨bⁱ, v⟩ Ric(bᵢ, w)`. The first slot is linear, so the Ricci form is
recovered from its components against the basis. -/
theorem coordRicci_eq_sum_first_slot
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (v w : E) :
    coordRicci G x v w
      = ∑ i, (Module.finBasis ℝ E).coord i v
          * coordRicci G x ((Module.finBasis ℝ E) i) w := by
  rw [(coordRicciCLM_apply G x hdiff w v).symm]
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, coordRicciCLM_apply, smul_eq_mul, Module.Basis.coord_apply]

/-- **Frozen-base-point derivative of the Ricci form over the basis**:
with the first slot a fixed vector `c`, the spatial derivative of
`y ↦ Ric_y(c, bk)` expands over the basis as
`Σᵢ ⟨bⁱ, c⟩ · D Ric_y(bᵢ, bk)`. The fixed first-slot vector pulls out
through the (linear) first slot, leaving the basis-component derivatives. -/
theorem fderiv_coordRicci_first_slot_const
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (c bk w : E) :
    (fderiv ℝ (fun y ↦ coordRicci G y c bk) x) w
      = ∑ i, (Module.finBasis ℝ E).coord i c
          * (fderiv ℝ (fun y ↦ coordRicci G y
              ((Module.finBasis ℝ E) i) bk) x) w := by
  have hfun : (fun y ↦ coordRicci G y c bk)
      = fun y ↦ ∑ i, (Module.finBasis ℝ E).coord i c
          * coordRicci G y ((Module.finBasis ℝ E) i) bk := by
    funext y
    exact coordRicci_eq_sum_first_slot (fun u ↦ hdiffΓ y u) c bk
  rw [hfun, fderiv_fun_sum fun i _ ↦
    (differentiableAt_coordRicci_family hdiffΓ hdd ((Module.finBasis ℝ E) i)
      bk).const_mul ((Module.finBasis ℝ E).coord i c),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_const_mul
    (differentiableAt_coordRicci_family hdiffΓ hdd ((Module.finBasis ℝ E) i) bk),
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/--
**THE PRODUCT RULE FOR THE RAISED RICCI FORM**: differentiating
`y ↦ Ric_y((G y)⁻¹ρ, bk)` splits into the frozen-index derivative plus
the Ricci form evaluated on the derivative of the raised index —
`D[Ric((G·)⁻¹ρ, bk)] = D[Ric((G x)⁻¹ρ, bk)]_frozen + Ric(D((G·)⁻¹ρ), bk)`.
This is the chain rule that exposes the inverse-metric variation term,
which metric compatibility then cancels against the Christoffel
corrections.
-/
theorem fderiv_coordRicci_raised_eq
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hGd : DifferentiableAt ℝ G x)
    (ρ : E →L[ℝ] ℝ) (bk w : E) :
    (fderiv ℝ (fun y ↦ coordRicci G y ((G y).inverse ρ) bk) x) w
      = (fderiv ℝ (fun y ↦ coordRicci G y ((G x).inverse ρ) bk) x) w
        + coordRicci G x
            ((-(((G x).inverse).comp
              ((fderiv ℝ G x).flip ((G x).inverse ρ)))) w) bk := by
  set bE := Module.finBasis ℝ E with hbE
  set V' : E →L[ℝ] E :=
    -(((G x).inverse).comp ((fderiv ℝ G x).flip ((G x).inverse ρ))) with hV'
  have hVfd : HasFDerivAt (fun y ↦ (G y).inverse ρ) V' x :=
    hasFDerivAt_inverse_raise hGd (Filter.Eventually.of_forall hinv) ρ
  have hmul : ∀ i : Fin (Module.finrank ℝ E),
      HasFDerivAt
        (fun y ↦ bE.coord i ((G y).inverse ρ) * coordRicci G y (bE i) bk)
        (bE.coord i ((G x).inverse ρ)
            • (fderiv ℝ (fun y ↦ coordRicci G y (bE i) bk) x)
          + coordRicci G x (bE i) bk
            • (LinearMap.toContinuousLinearMap (bE.coord i)).comp V') x := by
    intro i
    have hg : HasFDerivAt (fun y ↦ bE.coord i ((G y).inverse ρ))
        ((LinearMap.toContinuousLinearMap (bE.coord i)).comp V') x :=
      (LinearMap.toContinuousLinearMap (bE.coord i)).hasFDerivAt.comp x hVfd
    have hh : HasFDerivAt (fun y ↦ coordRicci G y (bE i) bk)
        (fderiv ℝ (fun y ↦ coordRicci G y (bE i) bk) x) x :=
      (differentiableAt_coordRicci_family hdiffΓ hdd (bE i) bk).hasFDerivAt
    exact hg.mul hh
  have hsum : HasFDerivAt (fun y ↦ coordRicci G y ((G y).inverse ρ) bk)
      (∑ i, (bE.coord i ((G x).inverse ρ)
            • (fderiv ℝ (fun y ↦ coordRicci G y (bE i) bk) x)
          + coordRicci G x (bE i) bk
            • (LinearMap.toContinuousLinearMap (bE.coord i)).comp V')) x := by
    have hfun : (fun y ↦ coordRicci G y ((G y).inverse ρ) bk)
        = fun y ↦ ∑ i, bE.coord i ((G y).inverse ρ)
            * coordRicci G y (bE i) bk := by
      funext y
      exact coordRicci_eq_sum_first_slot (fun u ↦ hdiffΓ y u) _ bk
    rw [hfun]
    exact HasFDerivAt.fun_sum fun i _ ↦ hmul i
  rw [hsum.fderiv, ContinuousLinearMap.sum_apply,
    fderiv_coordRicci_first_slot_const hdiffΓ hdd ((G x).inverse ρ) bk w,
    coordRicci_eq_sum_first_slot (fun u ↦ hdiffΓ x u) (V' w) bk,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [show ((LinearMap.toContinuousLinearMap (bE.coord i)).comp V') w
      = bE.coord i (V' w) from rfl]
  ring

/--
**THE INVERSE-METRIC-DERIVATIVE TRACE IS TWICE THE CHRISTOFFEL-CORRECTION
TRACE**: `Σₖ Ric(D_w ♯bᵏ, bₖ) = −2 Σₖ Ric(Γ_w ♯bᵏ, bₖ)`. Metric
compatibility splits the raised-index derivative into two Christoffel
pieces; one is the correction trace directly, the other becomes it after
swapping the contraction order and applying metric and Ricci symmetry.
The third ingredient of the `∇R = dR` cancellation.
-/
theorem coordRicci_inverse_raise_trace
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (w : E) :
    (∑ k, coordRicci G x
        ((-(((G x).inverse).comp
          ((fderiv ℝ G x).flip ((G x).inverse
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k)))))) w)
        ((Module.finBasis ℝ E) k))
      = -2 * ∑ k, coordRicci G x
          (christoffelClosedOp G x w
            ((G x).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k))))
          ((Module.finBasis ℝ E) k) := by
  have hGd : DifferentiableAt ℝ G x :=
    (hGC2.differentiable (by norm_num)).differentiableAt
  -- Coordinate of the raised-index derivative, by metric compatibility.
  have hDcoord : ∀ i k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).coord i
        ((-(((G x).inverse).comp
          ((fderiv ℝ G x).flip ((G x).inverse
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k)))))) w)
      = -((Module.finBasis ℝ E).coord i
            (christoffelClosedOp G x w
              ((G x).inverse (LinearMap.toContinuousLinearMap
                ((Module.finBasis ℝ E).coord k)))))
        - G x ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k)))
            (christoffelClosedOp G x w
              ((G x).inverse (LinearMap.toContinuousLinearMap
                ((Module.finBasis ℝ E).coord i)))) := by
    intro i k
    rw [coord_eq_g_raised G (hinv x) (hGsymm x) i,
      g_inverse_raise_metric_compat hGd hGsymm (hinv x)
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k)) w
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord i))),
      coord_eq_g_raised G (hinv x) (hGsymm x) i
        (christoffelClosedOp G x w
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k))))]
  -- Expand the trace into a double sum and substitute the coordinate.
  have hexp : ∀ k : Fin (Module.finrank ℝ E),
      coordRicci G x
        ((-(((G x).inverse).comp
          ((fderiv ℝ G x).flip ((G x).inverse
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k)))))) w)
        ((Module.finBasis ℝ E) k)
      = -coordRicci G x
          (christoffelClosedOp G x w
            ((G x).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k))))
          ((Module.finBasis ℝ E) k)
        - ∑ i, G x ((G x).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k)))
              (christoffelClosedOp G x w
                ((G x).inverse (LinearMap.toContinuousLinearMap
                  ((Module.finBasis ℝ E).coord i))))
            * coordRicci G x ((Module.finBasis ℝ E) i)
                ((Module.finBasis ℝ E) k) := by
    intro k
    rw [coordRicci_eq_sum_first_slot hdiffΓ _ ((Module.finBasis ℝ E) k),
      coordRicci_eq_sum_first_slot hdiffΓ
        (christoffelClosedOp G x w
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord k)))) ((Module.finBasis ℝ E) k),
      ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hDcoord i k]
    ring
  rw [Finset.sum_congr rfl fun k _ ↦ hexp k, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  -- The double sum equals the correction trace `T1`.
  have hS2 : (∑ k, ∑ i,
        G x ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord k)))
          (christoffelClosedOp G x w
            ((G x).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord i))))
        * coordRicci G x ((Module.finBasis ℝ E) i)
            ((Module.finBasis ℝ E) k))
      = ∑ k, coordRicci G x
          (christoffelClosedOp G x w
            ((G x).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k))))
          ((Module.finBasis ℝ E) k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coordRicci_eq_sum_first_slot hdiffΓ
      (christoffelClosedOp G x w
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord i)))) ((Module.finBasis ℝ E) i)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hGsymm x, coord_eq_g_raised G (hinv x) (hGsymm x) k
        (christoffelClosedOp G x w
          ((G x).inverse (LinearMap.toContinuousLinearMap
            ((Module.finBasis ℝ E).coord i)))),
      coordRicci_symm hGC2 hGsymm hinv hdiffΓ ((Module.finBasis ℝ E) i)
        ((Module.finBasis ℝ E) k)]
  rw [hS2]
  ring

/-- **The raised Ricci form is spatially differentiable**: with the
inverse metric raising one slot, `y ↦ Ric_y((G y)⁻¹ρ, bk)` differentiates
at `x` — basis expansion plus the differentiability of the components and
the raised index. -/
theorem differentiableAt_coordRicci_raised
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hGd : DifferentiableAt ℝ G x)
    (ρ : E →L[ℝ] ℝ) (bk : E) :
    DifferentiableAt ℝ (fun y ↦ coordRicci G y ((G y).inverse ρ) bk) x := by
  have hfun : (fun y ↦ coordRicci G y ((G y).inverse ρ) bk)
      = fun y ↦ ∑ i, (Module.finBasis ℝ E).coord i ((G y).inverse ρ)
          * coordRicci G y ((Module.finBasis ℝ E) i) bk := by
    funext y
    exact coordRicci_eq_sum_first_slot (fun u ↦ hdiffΓ y u) _ bk
  rw [hfun]
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.mul
  · exact (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord i)).differentiableAt.comp x
      (hasFDerivAt_inverse_raise hGd
        (Filter.Eventually.of_forall hinv) ρ).differentiableAt
  · exact differentiableAt_coordRicci_family hdiffΓ hdd
      ((Module.finBasis ℝ E) i) bk

/--
**`∇R = dR`: THE COVARIANT SCALAR-CURVATURE DERIVATIVE IS THE DIFFERENTIAL**:
the metric-trace of the covariant Ricci derivative equals the ordinary
derivative of the scalar curvature — `scalarContractionDeriv = d(coordScalar)`.
The covariant derivative commutes with the metric trace: the
inverse-metric-variation term from differentiating the raised index
cancels the Christoffel corrections of the Ricci covariant derivative.
This is the boss brick of the Bianchi bridge.
-/
theorem scalarContractionDeriv_eq_fderiv_coordScalar
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (w : E) :
    scalarContractionDeriv G x w
      = (fderiv ℝ (fun y ↦ coordScalar G y) x) w := by
  have hGd : DifferentiableAt ℝ G x :=
    (hGC2.differentiable (by norm_num)).differentiableAt
  have hdiffΓx : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x :=
    fun u ↦ hdiffΓ x u
  -- Express the contracted Ricci divergence through the tensor derivative.
  have hSC : scalarContractionDeriv G x w
      = ∑ k, ((fderiv ℝ (fun y ↦ coordRicci G y
              ((G x).inverse (LinearMap.toContinuousLinearMap
                ((Module.finBasis ℝ E).coord k)))
              ((Module.finBasis ℝ E) k)) x) w
          - coordRicci G x (christoffelClosedOp G x w
              ((G x).inverse (LinearMap.toContinuousLinearMap
                ((Module.finBasis ℝ E).coord k))))
              ((Module.finBasis ℝ E) k)
          - coordRicci G x
              ((G x).inverse (LinearMap.toContinuousLinearMap
                ((Module.finBasis ℝ E).coord k)))
              (christoffelClosedOp G x w ((Module.finBasis ℝ E) k))) := by
    unfold scalarContractionDeriv
    exact Finset.sum_congr rfl fun k _ ↦
      covRicciDeriv_eq_tensor_deriv hdiffΓ hdd w _ _
  -- Differentiate the scalar curvature through the raised contraction.
  have hFC : (fderiv ℝ (fun y ↦ coordScalar G y) x) w
      = ∑ k, ((fderiv ℝ (fun y ↦ coordRicci G y
              ((G x).inverse (LinearMap.toContinuousLinearMap
                ((Module.finBasis ℝ E).coord k)))
              ((Module.finBasis ℝ E) k)) x) w
          + coordRicci G x
              ((-(((G x).inverse).comp
                ((fderiv ℝ G x).flip ((G x).inverse
                  (LinearMap.toContinuousLinearMap
                    ((Module.finBasis ℝ E).coord k)))))) w)
              ((Module.finBasis ℝ E) k)) := by
    rw [show (fun y ↦ coordScalar G y)
        = fun y ↦ ∑ k, coordRicci G y
            ((G y).inverse (LinearMap.toContinuousLinearMap
              ((Module.finBasis ℝ E).coord k)))
            ((Module.finBasis ℝ E) k) from rfl,
      fderiv_fun_sum fun k _ ↦ differentiableAt_coordRicci_raised hdiffΓ hdd
        hinv hGd (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord k)) ((Module.finBasis ℝ E) k),
      ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ ↦
      fderiv_coordRicci_raised_eq hdiffΓ hdd hinv hGd _ _ w
  rw [hSC, hFC, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have h1 := coordRicci_christoffel_correction_symm hGC2 hGsymm hinv hdiffΓx w
  have h2 := coordRicci_inverse_raise_trace hGC2 hGsymm hinv hdiffΓx w
  linarith [h1, h2]

/--
**THE TWICE-CONTRACTED BIANCHI IDENTITY IN ANALYTIC FORM**: the Ricci
divergence is half the differential of the scalar curvature —
`div Ric(w) = ½ d R(w)`. Combining the covariant twice-contracted Bianchi
identity `2 div Ric = ∇(tr Ric)` with `∇R = dR`, this is the classical
`div Ric = ½ ∇R` ready to feed the scalar-curvature evolution equation.
-/
theorem ricciDivergence_eq_half_fderiv_scalar
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hsymΓ : ∀ p : E, IsSymmSndFDerivAt ℝ
      (fun z ↦ christoffelClosedOp G z p) x)
    (w : E) :
    ricciDivergence G x w
      = (1 / 2 : ℝ) * (fderiv ℝ (fun y ↦ coordScalar G y) x) w := by
  have h1 := coord_twice_contracted_bianchi hGC2 hGsymm hinv hdiffΓ hdd hsymΓ w
  have h2 := scalarContractionDeriv_eq_fderiv_coordScalar hGC2 hGsymm hinv
    hdiffΓ hdd w
  rw [h2] at h1
  linarith

/-- The Ricci divergence is additive in its argument. -/
theorem ricciDivergence_add
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (u₁ u₂ : E) :
    ricciDivergence G x (u₁ + u₂)
      = ricciDivergence G x u₁ + ricciDivergence G x u₂ := by
  unfold ricciDivergence
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold covRicciDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [covCurvDeriv_add_snd hdiffΓ hdd _ _ u₁ u₂,
    ContinuousLinearMap.add_apply, map_add]

/-- The Ricci divergence is homogeneous in its argument. -/
theorem ricciDivergence_smul
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (c : ℝ) (u : E) :
    ricciDivergence G x (c • u) = c • ricciDivergence G x u := by
  unfold ricciDivergence
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold covRicciDeriv
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [covCurvDeriv_smul_snd hdiffΓ hdd _ _ c u,
    ContinuousLinearMap.smul_apply, map_smul]

/-- **The Ricci divergence as a covector**: the `1`-form `u ↦ div Ric(u)`,
packaged as a continuous linear functional. -/
noncomputable def ricciDivergenceForm (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x) :
    E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ ricciDivergence G x u
      map_add' := fun u₁ u₂ ↦ ricciDivergence_add hdiffΓ hdd u₁ u₂
      map_smul' := fun c u ↦ by
        simp only [RingHom.id_apply]
        exact ricciDivergence_smul hdiffΓ hdd c u }

@[simp] theorem ricciDivergenceForm_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x) (u : E) :
    ricciDivergenceForm G x hdiffΓ hdd u = ricciDivergence G x u := rfl

/--
**THE CONTRACTED BIANCHI IDENTITY IN GRADIENT FORM**: the differential of
the scalar curvature is twice the Ricci-divergence covector —
`d R = 2 · div Ric`. This is the form of the twice-contracted Bianchi
identity that drives the gradient flow of scalar curvature.
-/
theorem fderiv_coordScalar_eq_two_ricciDivergenceForm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiffΓ : ∀ (y : E) (p : E),
      DifferentiableAt ℝ (fun z ↦ christoffelClosedOp G z p) y)
    (hdd : ∀ p : E, DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ christoffelClosedOp G z p) y) x)
    (hsymΓ : ∀ p : E, IsSymmSndFDerivAt ℝ
      (fun z ↦ christoffelClosedOp G z p) x) :
    fderiv ℝ (fun y ↦ coordScalar G y) x
      = (2 : ℝ) • ricciDivergenceForm G x hdiffΓ hdd := by
  ext w
  rw [ContinuousLinearMap.smul_apply, ricciDivergenceForm_apply, smul_eq_mul,
    ricciDivergence_eq_half_fderiv_scalar hGC2 hGsymm hinv hdiffΓ hdd hsymΓ w]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**HAMILTON'S SCALAR EVOLUTION EQUATION, CORRECTLY TARGETED**: along a
coordinate Ricci flow `∂g/∂t = H = −2 Ric`, the scalar curvature evolves
by `∂R/∂t = Δ_g R + 2|Ric|²` — with the GENUINE Laplace–Beltrami operator
`curvedLaplacian` (not the bare `modelLaplacian`), conditional on the
correctly-stated Bianchi identity `Σⱼ δRic(♯bʲ, bⱼ) = Δ_g R`. This is the
geometrically-faithful evolution equation: the design analysis showed the
`modelLaplacian` form is false off `Γ = 0`, while this `curvedLaplacian`
form is unconditional once `hBianchi` is discharged.
-/
theorem hamilton_scalar_evolution_of_bianchi_curved
    {Gt : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} {t₀ : ℝ}
    (hdG : HasDerivAt (fun t ↦ Gt t x) (H x) t₀)
    (hev : ∀ᶠ t in nhds t₀, (Gt t x).IsInvertible)
    (hmix : ∀ p q r : E,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) x p) q r)
        ((fderiv ℝ H x p) q r) t₀)
    (hmix2 : ∀ p v : E,
      HasDerivAt
        (fun t ↦ fderiv ℝ (fun y ↦ christoffelClosedOp (Gt t) y p) x v)
        (fderiv ℝ (fun y ↦ christoffelDerivOp (Gt t₀) H y p) x v) t₀)
    (hd2 : ∀ t : ℝ, ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp (Gt t) y u) x)
    (hH : H x = (-2 : ℝ) • coordRicciForm (Gt t₀) x (hd2 t₀))
    (hbnd : ∀ y : E, (metricBilin (Gt t₀ y)).Nondegenerate)
    (hBianchi : ∑ j, ricciDeriv (Gt t₀) H x
        ((Gt t₀ x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j)
      = curvedLaplacian (Gt t₀) (fun y ↦ metricBilin (Gt t₀ y)) hbnd
          (fun y ↦ coordScalar (Gt t₀) y) x) :
    HasDerivAt (fun t ↦ coordScalar (Gt t) x)
      (curvedLaplacian (Gt t₀) (fun y ↦ metricBilin (Gt t₀ y)) hbnd
          (fun y ↦ coordScalar (Gt t₀) y) x
        + 2 * coordRicciNormSq (Gt t₀) x (hd2 t₀)) t₀ := by
  have h := hasDerivAt_coordScalar hdG hev hmix hmix2 hd2
  rw [Finset.sum_add_distrib, hBianchi] at h
  have hvar : ∑ j, coordRicci (Gt t₀) x
      ((-((Gt t₀ x).inverse.comp ((H x).comp (Gt t₀ x).inverse)))
        (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
      ((Module.finBasis ℝ E) j)
      = 2 * coordRicciNormSq (Gt t₀) x (hd2 t₀) := by
    rw [hH]
    exact inverseVariation_ricci_direction (Gt t₀) x (hd2 t₀)
  rw [hvar] at h
  exact h

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
**THE METRIC-PAIRED LICHNEROWICZ FORM OF `∇δΓ`**: pairing the covariant
derivative of the Christoffel variation against the metric gives the
directional derivative of the Lichnerowicz half-sum of covariant
derivatives of `H`, minus the three lower-slot Christoffel corrections.
This combines metric compatibility for `∇δΓ` with the `δΓ = ½∇H` formula,
turning `G(∇δΓ, ·)` into the derivative of second covariant derivatives of
`H` — the entry point to contracting `δRic` into the scalar Laplacian.
-/
theorem g_covDeltaGammaDeriv_lichnerowicz
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} {p : E}
    (hGd : ∀ y : E, DifferentiableAt ℝ G y)
    (hGsymm : ∀ (y : E) (a b : E), G y a b = G y b a)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hHsymm : ∀ (y : E) (a b : E), H y a b = H y b a)
    (hVd : DifferentiableAt ℝ (fun y ↦ christoffelDerivOp G H y p) x)
    (v z w : E) :
    G x (covDeltaGammaDeriv G H x v p z) w
      = (fderiv ℝ (fun y ↦ (1 / 2 : ℝ) * (covTensor2Deriv G H y p z w
          + covTensor2Deriv G H y z p w
          - covTensor2Deriv G H y w p z)) x) v
        - G x (christoffelDerivOp G H x
            (christoffelClosedOp G x v p) z) w
        - G x (christoffelDerivOp G H x p
            (christoffelClosedOp G x v z)) w
        - G x (christoffelDerivOp G H x p z)
            (christoffelClosedOp G x v w) := by
  rw [g_covDeltaGammaDeriv (hGd x) hGsymm (hinv x) hVd v z w,
    g_christoffelDerivOp_pairing_eq hGd hGsymm hinv hHsymm p z w]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The covariant 2-tensor derivative is spatially differentiable**:
`y ↦ (∇_v H)(p,q)` differentiates at `x` given that `H` is twice
differentiable and the Christoffel families differentiate. The
prerequisite for forming the second covariant derivative `∇²H`. -/
theorem differentiableAt_covTensor2Deriv_family
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hHd : DifferentiableAt ℝ H x)
    (hH2 : DifferentiableAt ℝ (fun y ↦ fderiv ℝ H y) x)
    (hΓd : ∀ a : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y a) x)
    (v p q : E) :
    DifferentiableAt ℝ (fun y ↦ covTensor2Deriv G H y v p q) x := by
  unfold covTensor2Deriv
  -- The flat second-derivative term.
  have ht1 : DifferentiableAt ℝ (fun y ↦ (fderiv ℝ H y v) p q) x :=
    (((hH2.clm_apply (differentiableAt_const v)).clm_apply
      (differentiableAt_const p)).clm_apply (differentiableAt_const q))
  -- The two Christoffel-correction terms.
  have hVp : DifferentiableAt ℝ
      (fun y ↦ christoffelClosedOp G y v p) x :=
    (hΓd v).clm_apply (differentiableAt_const p)
  have hVq : DifferentiableAt ℝ
      (fun y ↦ christoffelClosedOp G y v q) x :=
    (hΓd v).clm_apply (differentiableAt_const q)
  have ht2 : DifferentiableAt ℝ
      (fun y ↦ H y (christoffelClosedOp G y v p) q) x :=
    (hHd.clm_apply hVp).clm_apply (differentiableAt_const q)
  have ht3 : DifferentiableAt ℝ
      (fun y ↦ H y p (christoffelClosedOp G y v q)) x :=
    (hHd.clm_apply (differentiableAt_const p)).clm_apply hVq
  exact (ht1.sub ht2).sub ht3

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The covariant 2-tensor derivative vanishes on constant data. -/
theorem covTensor2Deriv_const_eq_zero (G₀ H₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (x v p q : E) :
    covTensor2Deriv (fun _ : E ↦ G₀) (fun _ : E ↦ H₀) x v p q = 0 := by
  unfold covTensor2Deriv
  simp [christoffelClosedOp_const_eq_zero, fderiv_fun_const]

/-- **The second covariant derivative of a 2-tensor**: `(∇²H)(v';v,p,q)` —
the covariant derivative of the `(0,3)`-tensor `∇H` in direction `v'`,
correcting the differentiation direction and both tensor slots. The object
whose basis traces are `div div H` and `Δ tr H`. -/
noncomputable def covTensor2SndDeriv (G H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v' v p q : E) : ℝ :=
  (fderiv ℝ (fun y ↦ covTensor2Deriv G H y v p q) x) v'
    - covTensor2Deriv G H x (christoffelClosedOp G x v' v) p q
    - covTensor2Deriv G H x v (christoffelClosedOp G x v' p) q
    - covTensor2Deriv G H x v p (christoffelClosedOp G x v' q)

/-- The second covariant derivative vanishes on constant data. -/
theorem covTensor2SndDeriv_const_eq_zero (G₀ H₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (x v' v p q : E) :
    covTensor2SndDeriv (fun _ : E ↦ G₀) (fun _ : E ↦ H₀) x v' v p q = 0 := by
  unfold covTensor2SndDeriv
  have hf : (fun y ↦ covTensor2Deriv (fun _ : E ↦ G₀) (fun _ : E ↦ H₀)
      y v p q) = fun _ ↦ (0 : ℝ) := by
    funext y
    exact covTensor2Deriv_const_eq_zero G₀ H₀ y v p q
  rw [hf, fderiv_fun_const]
  simp [covTensor2Deriv_const_eq_zero]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The flat derivative of `∇H` is `∇²H` plus Christoffel corrections**:
`D_{v'}(∇H)(v,p,q) = (∇²H)(v';v,p,q) + (∇H)(Γ_{v'}v,p,q) + (∇H)(v,Γ_{v'}p,q)
+ (∇H)(v,p,Γ_{v'}q)`. Rearranges the second-covariant-derivative
definition, the form used to substitute into the Lichnerowicz pairing. -/
theorem fderiv_covTensor2Deriv_eq
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (v' v p q : E) :
    (fderiv ℝ (fun y ↦ covTensor2Deriv G H y v p q) x) v'
      = covTensor2SndDeriv G H x v' v p q
        + covTensor2Deriv G H x (christoffelClosedOp G x v' v) p q
        + covTensor2Deriv G H x v (christoffelClosedOp G x v' p) q
        + covTensor2Deriv G H x v p (christoffelClosedOp G x v' q) := by
  unfold covTensor2SndDeriv
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Distributing the derivative of the Lichnerowicz `½∇H`-sum**: the
directional derivative of the half-sum of covariant `H`-derivatives is the
half-sum of their directional derivatives — `fderiv`-linearity, the step
that lets each term become a second covariant derivative `∇²H`. -/
theorem fderiv_lichnerowicz_sum
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hHd : DifferentiableAt ℝ H x)
    (hH2 : DifferentiableAt ℝ (fun y ↦ fderiv ℝ H y) x)
    (hΓd : ∀ a : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y a) x)
    (v p z w : E) :
    (fderiv ℝ (fun y ↦ (1 / 2 : ℝ) * (covTensor2Deriv G H y p z w
        + covTensor2Deriv G H y z p w
        - covTensor2Deriv G H y w p z)) x) v
      = (1 / 2 : ℝ) * ((fderiv ℝ (fun y ↦ covTensor2Deriv G H y p z w) x) v
          + (fderiv ℝ (fun y ↦ covTensor2Deriv G H y z p w) x) v
          - (fderiv ℝ (fun y ↦ covTensor2Deriv G H y w p z) x) v) := by
  have d1 := (differentiableAt_covTensor2Deriv_family hHd hH2 hΓd p z w).hasFDerivAt
  have d2 := (differentiableAt_covTensor2Deriv_family hHd hH2 hΓd z p w).hasFDerivAt
  have d3 := (differentiableAt_covTensor2Deriv_family hHd hH2 hΓd w p z).hasFDerivAt
  have hfd : HasFDerivAt (fun y ↦ (1 / 2 : ℝ) * (covTensor2Deriv G H y p z w
        + covTensor2Deriv G H y z p w - covTensor2Deriv G H y w p z))
      ((1 / 2 : ℝ) • ((fderiv ℝ (fun y ↦ covTensor2Deriv G H y p z w) x
          + fderiv ℝ (fun y ↦ covTensor2Deriv G H y z p w) x)
        - fderiv ℝ (fun y ↦ covTensor2Deriv G H y w p z) x)) x :=
    ((d1.add d2).sub d3).const_mul (1 / 2 : ℝ)
  rw [hfd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **`G(∇δΓ,w)` as half-sum of `∇H`-derivatives**: combining the
metric-paired Lichnerowicz form with the derivative-distribution, the
metric pairing of the covariant Christoffel-variation derivative is the
half-sum of the three directional derivatives of the covariant
`H`-derivative, minus the three Christoffel corrections. One rewrite away
from the second-covariant-derivative `∇²H` form. -/
theorem g_covDeltaGammaDeriv_fderiv_form
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} {p : E}
    (hGd : ∀ y : E, DifferentiableAt ℝ G y)
    (hGsymm : ∀ (y : E) (a b : E), G y a b = G y b a)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hHsymm : ∀ (y : E) (a b : E), H y a b = H y b a)
    (hVd : DifferentiableAt ℝ (fun y ↦ christoffelDerivOp G H y p) x)
    (hHd : DifferentiableAt ℝ H x)
    (hH2 : DifferentiableAt ℝ (fun y ↦ fderiv ℝ H y) x)
    (hΓd : ∀ a : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y a) x)
    (v z w : E) :
    G x (covDeltaGammaDeriv G H x v p z) w
      = (1 / 2 : ℝ) * ((fderiv ℝ (fun y ↦ covTensor2Deriv G H y p z w) x) v
          + (fderiv ℝ (fun y ↦ covTensor2Deriv G H y z p w) x) v
          - (fderiv ℝ (fun y ↦ covTensor2Deriv G H y w p z) x) v)
        - G x (christoffelDerivOp G H x
            (christoffelClosedOp G x v p) z) w
        - G x (christoffelDerivOp G H x p
            (christoffelClosedOp G x v z)) w
        - G x (christoffelDerivOp G H x p z)
            (christoffelClosedOp G x v w) := by
  rw [g_covDeltaGammaDeriv_lichnerowicz hGd hGsymm hinv hHsymm hVd v z w,
    fderiv_lichnerowicz_sum hHd hH2 hΓd v p z w]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **`G(∇δΓ,w)` IN SECOND-COVARIANT-DERIVATIVE FORM**: the metric pairing
of the covariant Christoffel-variation derivative is the Lichnerowicz
half-sum of second covariant derivatives `∇²H`, plus the lower-slot
Christoffel corrections of `∇H`, minus the value-slot corrections of `δΓ`.
The closed Bochner form, ready for the basis contraction. -/
theorem g_covDeltaGammaDeriv_sndDeriv_form
    {G H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} {p : E}
    (hGd : ∀ y : E, DifferentiableAt ℝ G y)
    (hGsymm : ∀ (y : E) (a b : E), G y a b = G y b a)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hHsymm : ∀ (y : E) (a b : E), H y a b = H y b a)
    (hVd : DifferentiableAt ℝ (fun y ↦ christoffelDerivOp G H y p) x)
    (hHd : DifferentiableAt ℝ H x)
    (hH2 : DifferentiableAt ℝ (fun y ↦ fderiv ℝ H y) x)
    (hΓd : ∀ a : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y a) x)
    (v z w : E) :
    G x (covDeltaGammaDeriv G H x v p z) w
      = (1 / 2 : ℝ) * ((covTensor2SndDeriv G H x v p z w
            + covTensor2Deriv G H x (christoffelClosedOp G x v p) z w
            + covTensor2Deriv G H x p (christoffelClosedOp G x v z) w
            + covTensor2Deriv G H x p z (christoffelClosedOp G x v w))
          + (covTensor2SndDeriv G H x v z p w
            + covTensor2Deriv G H x (christoffelClosedOp G x v z) p w
            + covTensor2Deriv G H x z (christoffelClosedOp G x v p) w
            + covTensor2Deriv G H x z p (christoffelClosedOp G x v w))
          - (covTensor2SndDeriv G H x v w p z
            + covTensor2Deriv G H x (christoffelClosedOp G x v w) p z
            + covTensor2Deriv G H x w (christoffelClosedOp G x v p) z
            + covTensor2Deriv G H x w p (christoffelClosedOp G x v z)))
        - G x (christoffelDerivOp G H x
            (christoffelClosedOp G x v p) z) w
        - G x (christoffelDerivOp G H x p
            (christoffelClosedOp G x v z)) w
        - G x (christoffelDerivOp G H x p z)
            (christoffelClosedOp G x v w) := by
  rw [g_covDeltaGammaDeriv_fderiv_form hGd hGsymm hinv hHsymm hVd hHd hH2
      hΓd v z w, fderiv_covTensor2Deriv_eq, fderiv_covTensor2Deriv_eq,
    fderiv_covTensor2Deriv_eq]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The metric trace of the Ricci form is the scalar curvature**:
`Σⱼ Ric(♯bʲ, bⱼ) = R` — contracting the Ricci form against the inverse
metric recovers `coordScalar`. The `tr_g Ric = R` identity, the precursor
to `tr_g H = −2R` for the Ricci-flow direction. -/
theorem coordRicciForm_metric_trace
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x) :
    (∑ j, coordRicciForm G x hdiff
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j))
      = coordScalar G x := by
  unfold coordScalar
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coordRicciForm_apply]
  exact coordRicci_symm hGC2 hGsymm hinv hdiff _ _

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The metric trace of a scalar multiple of the Ricci form**:
`Σⱼ (c·Ric)(♯bʲ, bⱼ) = c·R`. For the Ricci-flow direction `H = −2 Ric`
this gives `tr_g H = −2R`, the trace data of the variation tensor that
enters the scalar evolution. -/
theorem metricTrace_smul_coordRicciForm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGC2 : ContDiff ℝ 2 G)
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (hdiff : ∀ u : E,
      DifferentiableAt ℝ (fun y ↦ christoffelClosedOp G y u) x)
    (c : ℝ) :
    (∑ j, (c • coordRicciForm G x hdiff)
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j))
      = c * coordScalar G x := by
  rw [← coordRicciForm_metric_trace hGC2 hGsymm hinv hdiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The covariant derivative of a 1-form**: `(∇_v α)(w) = D_v(α(w)) −
α(Γ(v,w))` — the flat derivative of the covector field corrected by the
Christoffel action on the test slot. The object whose metric trace is the
divergence of `α`. -/
noncomputable def covTensor1Deriv (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (α : E → E →L[ℝ] ℝ) (x v w : E) : ℝ :=
  (fderiv ℝ α x v) w - α x (christoffelClosedOp G x v w)

/-- The covariant 1-form derivative vanishes on constant data. -/
theorem covTensor1Deriv_const_eq_zero (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (α₀ : E →L[ℝ] ℝ) (x v w : E) :
    covTensor1Deriv (fun _ : E ↦ G₀) (fun _ : E ↦ α₀) x v w = 0 := by
  unfold covTensor1Deriv
  simp [fderiv_fun_const, christoffelClosedOp_const_eq_zero]

/-- The covariant 1-form derivative is additive in its test slot. -/
theorem covTensor1Deriv_add_test (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (α : E → E →L[ℝ] ℝ) (x v w₁ w₂ : E) :
    covTensor1Deriv G α x v (w₁ + w₂)
      = covTensor1Deriv G α x v w₁ + covTensor1Deriv G α x v w₂ := by
  unfold covTensor1Deriv
  simp only [map_add]
  ring

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The covariant derivative of the differential is the covariant
Hessian**: `(∇_v df)(w) = Hess f(v,w)`. Identifies the abstract 1-form
covariant derivative applied to `df` with the metric covariant Hessian,
so the metric trace of `∇dR` is the curved Laplacian — the bridge from
`div Ric` to `Δ_g R`. -/
theorem covTensor1Deriv_fderiv_eq_covariantHessian
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (f : E → ℝ) (v w : E) :
    covTensor1Deriv G (fun y ↦ fderiv ℝ f y) x v w
      = covariantHessian G (fun y ↦ metricBilin (G y))
          (fun y ↦ metricBilin_nondeg (hGsymm y) (hinv y)) f x v w := by
  unfold covTensor1Deriv covariantHessian
  rw [christoffelClosedOp_eq_christoffelAt G (metricBilin (G x))
    (metricBilin_nondeg (hGsymm x) (hinv x))
    (fun a b ↦ metricBilin_apply (G x) a b)]

end RicciFlow

namespace RicciFlow

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The divergence of a gradient is the curved Laplacian**: `div(df) =
Δ_g f` — the metric trace of the covariant derivative of the differential
is the Laplace–Beltrami operator. The second-divergence identity that,
applied to `R`, gives `div div Ric = ½ Δ_g R`. -/
theorem metricTrace_covTensor1Deriv_fderiv
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hGsymm : ∀ (y : E) (p q : E), G y p q = G y q p)
    (hinv : ∀ y : E, (G y).IsInvertible)
    (f : E → ℝ) :
    (∑ j, covTensor1Deriv G (fun y ↦ fderiv ℝ f y) x
        ((G x).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord j)))
        ((Module.finBasis ℝ E) j))
      = curvedLaplacian G (fun y ↦ metricBilin (G y))
          (fun y ↦ metricBilin_nondeg (hGsymm y) (hinv y)) f x := by
  rw [curvedLaplacian_eq_raised_sum G hGsymm hinv f]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact covTensor1Deriv_fderiv_eq_covariantHessian hGsymm hinv f _ _

end RicciFlow
