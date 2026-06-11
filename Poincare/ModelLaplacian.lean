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
