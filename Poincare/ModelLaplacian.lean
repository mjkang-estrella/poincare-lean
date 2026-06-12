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
