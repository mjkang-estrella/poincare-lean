/-
The flat connection on a normed space and its vanishing curvature.

Mathlib defines `CovariantDerivative` abstractly but provides no concrete
instance.  This module constructs the flat covariant derivative `∇_X σ = Dσ·X`
on a normed space (the tangent bundle of the model space), and proves the
model-case curvature computation: the Riemann curvature operator of the flat
connection vanishes at every point where the field is twice differentiable
with symmetric second derivative.  This grounds the curvature theory of
`Poincare.RiemannCurvatureOperator` in its first concrete example — Euclidean
space is flat.
-/

import Poincare.RiemannCurvatureOperator
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

noncomputable section

open Bundle Set VectorField
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
A vector field on a vector space is manifold-differentiable at `x` iff it is
differentiable at `x` in the ordinary sense.
-/
lemma mdiffAt_vectorSpace_iff_differentiableAt
    {σ : Π x : E, TangentSpace 𝓘(𝕜, E) x} {x : E} :
    MDiffAt (T% σ) x ↔ DifferentiableAt 𝕜 σ x := by
  rw [mdifferentiableAt_section]
  simp only [trivializationAt_model_space_apply]
  exact mdifferentiableAt_iff_differentiableAt

variable (𝕜 E) in
/--
The flat covariant derivative on a normed space: `∇_X σ = (Dσ)(X)` via the
ordinary Fréchet derivative.
-/
def flatCovariantDerivative :
    CovariantDerivative 𝓘(𝕜, E) E (TangentSpace 𝓘(𝕜, E) : E → Type _) where
  toFun σ x := fderiv 𝕜 σ x
  isCovariantDerivativeOnUniv :=
    { add := by
        intro σ σ' x hσ hσ' _
        have h1 := mdiffAt_vectorSpace_iff_differentiableAt.mp hσ
        have h2 := mdiffAt_vectorSpace_iff_differentiableAt.mp hσ'
        letI : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E) x) :=
          ‹NormedAddCommGroup E›
        letI : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E) x) := ‹NormedSpace 𝕜 E›
        exact fderiv_add h1 h2
      leibniz := by
        intro σ g x hσ hg _
        have h1 := mdiffAt_vectorSpace_iff_differentiableAt.mp hσ
        have h2 : DifferentiableAt 𝕜 g x :=
          mdifferentiableAt_iff_differentiableAt.mp hg
        have h3 := (h2.hasFDerivAt.smul h1.hasFDerivAt).fderiv
        refine h3.trans ?_
        congr 1
        ext v
        simp only [extDerivFun, mfderiv_eq_fderiv,
          ContinuousLinearMap.smulRight_apply]
        rfl }

@[simp]
lemma flatCovariantDerivative_apply
    (σ : Π x : E, TangentSpace 𝓘(𝕜, E) x) (x : E) :
    flatCovariantDerivative 𝕜 E σ x = fderiv 𝕜 σ x :=
  rfl

/--
The model-space Lie bracket is the ordinary vector-field Lie bracket.
-/
lemma mlieBracket_vectorSpace_eq
    (V W : Π x : E, TangentSpace 𝓘(𝕜, E) x) :
    mlieBracket 𝓘(𝕜, E) V W = lieBracket 𝕜 V W := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin,
    lieBracketWithin_univ]

/--
**Euclidean space is flat.**  The Riemann curvature operator of the flat
connection vanishes at every point where the field `Z` is differentiable with
differentiable derivative and symmetric second derivative (e.g. at any point
where `Z` is `C²` over `ℝ` or `ℂ`).
-/
theorem flatCovariantDerivative_curvatureOp_eq_zero
    {V W Z : Π x : E, TangentSpace 𝓘(𝕜, E) x} {x : E}
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x)
    (hZ' : DifferentiableAt 𝕜 (fderiv 𝕜 Z) x)
    (hsymm : IsSymmSndFDerivAt 𝕜 Z x) :
    CovariantDerivative.curvatureOp (flatCovariantDerivative 𝕜 E) V W Z x
      = 0 := by
  rw [CovariantDerivative.curvatureOp_apply]
  show (fderiv 𝕜 (fun y ↦ (fderiv 𝕜 Z y) (W y)) x) (V x)
      - (fderiv 𝕜 (fun y ↦ (fderiv 𝕜 Z y) (V y)) x) (W x)
      - (fderiv 𝕜 Z x) (mlieBracket 𝓘(𝕜, E) V W x) = (0 : E)
  rw [fderiv_clm_apply hZ' hW, fderiv_clm_apply hZ' hV,
    mlieBracket_vectorSpace_eq]
  simp only [VectorField.lieBracket, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, map_sub]
  rw [hsymm (V x) (W x)]
  abel

/-! ## The flat connection is Levi-Civita for the Euclidean metric

The two defining properties of the Levi-Civita connection — vanishing torsion
and metric compatibility — hold for the flat connection on an inner product
space.
-/

/-- The flat connection is torsion-free. -/
theorem flatCovariantDerivative_torsion_eq_zero
    [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] :
    (flatCovariantDerivative 𝕜 E).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  rw [mlieBracket_vectorSpace_eq]
  rfl

open scoped RealInnerProductSpace in
/--
The flat connection is compatible with the Euclidean metric: the derivative
of the pointwise inner product of two vector fields obeys the Riemannian
product rule.  Together with `flatCovariantDerivative_torsion_eq_zero`, this
identifies the flat connection as the Levi-Civita connection of Euclidean
space.
-/
theorem flatCovariantDerivative_inner_compatible
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Y Z : F → F} {x : F}
    (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x) (v : F) :
    fderiv ℝ (fun y ↦ ⟪Y y, Z y⟫) x v =
      ⟪Z x, flatCovariantDerivative ℝ F Y x v⟫ +
        ⟪Y x, flatCovariantDerivative ℝ F Z x v⟫ := by
  rw [fderiv_inner_apply ℝ hY hZ v,
    real_inner_comm (Z x) (fderiv ℝ Y x v)]
  simp only [flatCovariantDerivative_apply]
  exact add_comm _ _
