import Poincare.Global.CartanMap

/-!
# Existence of the Cartan tangent alignment

This file removes the remaining parameter from the Cartan-map opener.  The
linear algebra input is that two positive-definite symmetric real bilinear
forms on the finite-dimensional model space are isometric.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace Poincare

universe u

namespace CartanMap

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/-- A tagged copy of the model space carrying the inner product induced by `B`. -/
def BilinFormSpace (_ : LinearMap.BilinForm ℝ E) := E

namespace BilinFormSpace

instance (B : LinearMap.BilinForm ℝ E) : AddCommGroup (BilinFormSpace B) :=
  inferInstanceAs (AddCommGroup E)

instance (B : LinearMap.BilinForm ℝ E) : Module ℝ (BilinFormSpace B) :=
  inferInstanceAs (Module ℝ E)

instance (B : LinearMap.BilinForm ℝ E) : FiniteDimensional ℝ (BilinFormSpace B) :=
  inferInstanceAs (FiniteDimensional ℝ E)

@[simps! apply]
def ofModel (B : LinearMap.BilinForm ℝ E) : E ≃ₗ[ℝ] BilinFormSpace B :=
  LinearEquiv.refl ℝ E

@[simps! apply]
def toModel (B : LinearMap.BilinForm ℝ E) : BilinFormSpace B ≃ₗ[ℝ] E :=
  LinearEquiv.refl ℝ E

/-- The inner-product core associated to a positive-definite symmetric bilinear form. -/
@[reducible]
def innerProductCore (B : LinearMap.BilinForm ℝ E)
    (hsym : ∀ u v : E, B u v = B v u)
    (hpos : ∀ {v : E}, v ≠ 0 → 0 < B v v) :
    InnerProductSpace.Core ℝ (BilinFormSpace B) where
  inner x y := B (toModel B x) (toModel B y)
  conj_inner_symm x y := by
    simp only [RCLike.conj_to_real]
    exact hsym _ _
  re_inner_nonneg x := by
    by_cases hx : toModel B x = 0
    · simp [hx]
    · exact le_of_lt (hpos hx)
  add_left x y z := by
    change B (toModel B (x + y)) (toModel B z) =
      B (toModel B x) (toModel B z) + B (toModel B y) (toModel B z)
    simp [toModel]
  smul_left x y r := by
    change B (toModel B (r • x)) (toModel B y) =
      r * B (toModel B x) (toModel B y)
    simp [toModel]
  definite x hx := by
    by_contra hx0
    have hposx : 0 < B (toModel B x) (toModel B x) := hpos (by
      intro h
      apply hx0
      exact (toModel B).injective h)
    exact (ne_of_gt hposx) hx

end BilinFormSpace

open BilinFormSpace

/--
Any two positive-definite symmetric real bilinear forms on the model space are
isometric.
-/
def positiveDefiniteBilinFormIsometryEquiv
    (B₁ B₂ : LinearMap.BilinForm ℝ E)
    (hsym₁ : ∀ u v : E, B₁ u v = B₁ v u)
    (hpos₁ : ∀ {v : E}, v ≠ 0 → 0 < B₁ v v)
    (hsym₂ : ∀ u v : E, B₂ u v = B₂ v u)
    (hpos₂ : ∀ {v : E}, v ≠ 0 → 0 < B₂ v v) :
    B₁.IsometryEquiv B₂ := by
  let core₁ : InnerProductSpace.Core ℝ (BilinFormSpace B₁) :=
    innerProductCore B₁ hsym₁ hpos₁
  letI : InnerProductSpace.Core ℝ (BilinFormSpace B₁) := core₁
  letI : NormedAddCommGroup (BilinFormSpace B₁) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := BilinFormSpace B₁)
  letI : NormedSpace ℝ (BilinFormSpace B₁) :=
    InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ) (F := BilinFormSpace B₁)
  letI : InnerProductSpace ℝ (BilinFormSpace B₁) := InnerProductSpace.ofCore core₁.toCore
  let core₂ : InnerProductSpace.Core ℝ (BilinFormSpace B₂) :=
    innerProductCore B₂ hsym₂ hpos₂
  letI : InnerProductSpace.Core ℝ (BilinFormSpace B₂) := core₂
  letI : NormedAddCommGroup (BilinFormSpace B₂) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := BilinFormSpace B₂)
  letI : NormedSpace ℝ (BilinFormSpace B₂) :=
    InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ) (F := BilinFormSpace B₂)
  letI : InnerProductSpace ℝ (BilinFormSpace B₂) := InnerProductSpace.ofCore core₂.toCore
  let b₁ := stdOrthonormalBasis ℝ (BilinFormSpace B₁)
  let b₂ := stdOrthonormalBasis ℝ (BilinFormSpace B₂)
  have hfin :
      Module.finrank ℝ (BilinFormSpace B₁) =
        Module.finrank ℝ (BilinFormSpace B₂) := rfl
  let e : Fin (Module.finrank ℝ (BilinFormSpace B₁)) ≃
      Fin (Module.finrank ℝ (BilinFormSpace B₂)) := finCongr hfin
  let f : BilinFormSpace B₁ ≃ₗᵢ[ℝ] BilinFormSpace B₂ :=
    Orthonormal.equiv (v := b₁.toBasis) b₁.orthonormal
      (v' := b₂.toBasis) b₂.orthonormal e
  refine
    { toLinearEquiv :=
        (ofModel B₁).trans
          ((f : BilinFormSpace B₁ ≃ₗ[ℝ] BilinFormSpace B₂).trans (toModel B₂))
      map_app' := ?_ }
  intro u v
  have hinner := f.inner_map_map (ofModel B₁ u) (ofModel B₁ v)
  change B₂ (toModel B₂ (f (ofModel B₁ u)))
      (toModel B₂ (f (ofModel B₁ v))) = B₁ u v
  exact hinner

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The Cartan tangent alignment exists without extra parameters. -/
theorem tangentAlignment_nonempty
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    Nonempty (TangentAlignment g x₀ p₀) := by
  refine ⟨positiveDefiniteBilinFormIsometryEquiv
    (sourceAnchorBilinForm g x₀) (targetAnchorBilinForm p₀) ?_ ?_ ?_ ?_⟩
  · intro u v
    simpa using sourceAnchorChartMetric_symm g x₀ u v
  · intro v hv
    simpa using sourceAnchorChartMetric_pos g x₀ hv
  · intro u v
    simpa using targetAnchorChartMetric_symm p₀ u v
  · intro v hv
    simpa using targetAnchorChartMetric_pos p₀ hv

/--
Unconditional Cartan opener: after choosing a tangent alignment existentially,
the Cartan map restricts to its source-target homeomorphism and sends the source
anchor to the chosen round-sphere anchor.
-/
theorem exists_sourceTargetHomeomorph_cartanMap_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    ∃ L : TangentAlignment g x₀ p₀,
      ∃ _ : (openPartialHomeomorph g x₀ p₀ L).source ≃ₜ
          (openPartialHomeomorph g x₀ p₀ L).target,
        cartanMap g x₀ p₀ L x₀ = p₀ := by
  rcases tangentAlignment_nonempty g x₀ p₀ with ⟨L⟩
  exact ⟨L, sourceTargetHomeomorph g x₀ p₀ L, cartanMap_anchor g x₀ p₀ L⟩

end CartanMap
end Poincare
