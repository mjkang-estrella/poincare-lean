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
