/-
The first Bianchi identity.

For a torsion-free affine connection, the cyclic sum of the Riemann curvature
operator vanishes on `C²` vector fields:
`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`.  The proof groups the iterated covariant
derivatives by differentiation direction, converts each group to a single
covariant derivative of a Lie bracket using torsion-freeness at the section
level, applies torsion-freeness once more pointwise, and closes with the
Jacobi (Leibniz) identity for the Lie bracket of vector fields.
-/

import Poincare.RiemannCurvatureOperator
import Poincare.LeviCivitaUniqueness

noncomputable section

open Bundle Set VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [IsManifold I 3 M] [CompleteSpace E]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
variable [ContMDiffCovariantDerivative cov 1]

/--
**First Bianchi identity.**  For a torsion-free connection and `C²` vector
fields, the cyclic sum of the curvature operator vanishes at every point.
-/
theorem bianchi_first
    (htf : ∀ y : M, TorsionFreeAt cov y)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z)) :
    curvatureOp cov X Y Z x + curvatureOp cov Y Z X x
      + curvatureOp cov Z X Y x = 0 := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    exact_mod_cast (inferInstance : IsManifold I 3 M)
  have hX1 : ∀ y, MDiffAt (T% X) y :=
    fun y ↦ (hX y).mdifferentiableAt two_ne_zero
  have hY1 : ∀ y, MDiffAt (T% Y) y :=
    fun y ↦ (hY y).mdifferentiableAt two_ne_zero
  have hZ1 : ∀ y, MDiffAt (T% Z) y :=
    fun y ↦ (hZ y).mdifferentiableAt two_ne_zero
  -- Torsion-freeness at the level of sections.
  have hsec : ∀ (A B : Π y : M, TangentSpace I y),
      (∀ y, MDiffAt (T% A) y) → (∀ y, MDiffAt (T% B) y) →
        ((fun y ↦ cov B y (A y)) - fun y ↦ cov A y (B y)) =
          mlieBracket I A B := by
    intro A B hA hB
    funext y
    simpa using htf y (hA y) (hB y)
  -- Covariant derivative of a difference of sections, at `x`.
  have hsub : ∀ {σ σ' : Π y : M, TangentSpace I y},
      MDiffAt (T% σ) x → MDiffAt (T% σ') x →
        cov (σ - σ') x = cov σ x - cov σ' x := by
    intro σ σ' hσ hσ'
    have hns : -σ' = (-1 : ℝ) • σ' := (neg_one_smul ℝ σ').symm
    have hd : MDiffAt (T% (-σ')) x := by
      rw [hns]
      exact mdifferentiableAt_const.smul_section hσ'
    have hneg : cov (-σ') x = - cov σ' x := by
      rw [hns,
        cov.isCovariantDerivativeOnUniv.smul_const (-1 : ℝ) hσ']
      simp
    calc cov (σ - σ') x = cov (σ + -σ') x := by rw [sub_eq_add_neg]
      _ = cov σ x + cov (-σ') x := cov.isCovariantDerivativeOnUniv.add hσ hd
      _ = cov σ x - cov σ' x := by rw [hneg, sub_eq_add_neg]
  -- Differentiability of the inner covariant-derivative sections at `x`.
  have hDZY := derivRegularAt_of_contMDiff cov hZ x (hY1 x)
  have hDYZ := derivRegularAt_of_contMDiff cov hY x (hZ1 x)
  have hDXZ := derivRegularAt_of_contMDiff cov hX x (hZ1 x)
  have hDZX := derivRegularAt_of_contMDiff cov hZ x (hX1 x)
  have hDYX := derivRegularAt_of_contMDiff cov hY x (hX1 x)
  have hDXY := derivRegularAt_of_contMDiff cov hX x (hY1 x)
  -- Differentiability of brackets at `x`.
  have hbr : ∀ {A B : Π y : M, TangentSpace I y},
      CMDiff 2 (T% A) → CMDiff 2 (T% B) →
        MDiffAt (T% (mlieBracket I A B)) x := by
    intro A B hA hB
    have h2 : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ ((2 : ℕ∞) : ℕ∞ω) := by
      simp
      norm_num
    exact (ContMDiffAt.mlieBracket_vectorField (m := 1) (n := 2)
      (hA x) (hB x) h2).mdifferentiableAt one_ne_zero
  -- Direction-grouped torsion conversions.
  have e1 : cov (fun y ↦ cov Z y (Y y)) x (X x)
      - cov (fun y ↦ cov Y y (Z y)) x (X x)
      = cov (mlieBracket I Y Z) x (X x) := by
    rw [← ContinuousLinearMap.sub_apply, ← hsub (hDZY) (hDYZ),
      hsec Y Z hY1 hZ1]
  have e2 : cov (fun y ↦ cov X y (Z y)) x (Y x)
      - cov (fun y ↦ cov Z y (X y)) x (Y x)
      = cov (mlieBracket I Z X) x (Y x) := by
    rw [← ContinuousLinearMap.sub_apply, ← hsub (hDXZ) (hDZX),
      hsec Z X hZ1 hX1]
  have e3 : cov (fun y ↦ cov Y y (X y)) x (Z x)
      - cov (fun y ↦ cov X y (Y y)) x (Z x)
      = cov (mlieBracket I X Y) x (Z x) := by
    rw [← ContinuousLinearMap.sub_apply, ← hsub (hDYX) (hDXY),
      hsec X Y hX1 hY1]
  -- Pointwise torsion-freeness against the brackets.
  have t1 : cov (mlieBracket I Y Z) x (X x) - cov X x (mlieBracket I Y Z x)
      = mlieBracket I X (mlieBracket I Y Z) x := htf x (hX1 x) (hbr hY hZ)
  have t2 : cov (mlieBracket I Z X) x (Y x) - cov Y x (mlieBracket I Z X x)
      = mlieBracket I Y (mlieBracket I Z X) x := htf x (hY1 x) (hbr hZ hX)
  have t3 : cov (mlieBracket I X Y) x (Z x) - cov Z x (mlieBracket I X Y x)
      = mlieBracket I Z (mlieBracket I X Y) x := htf x (hZ1 x) (hbr hX hY)
  -- The Jacobi identity in cyclic form.
  have mX : CMDiffAt (minSmoothness ℝ 2) (T% X) x := by simpa using hX x
  have mY : CMDiffAt (minSmoothness ℝ 2) (T% Y) x := by simpa using hY x
  have mZ : CMDiffAt (minSmoothness ℝ 2) (T% Z) x := by simpa using hZ x
  have l1 := leibniz_identity_mlieBracket_apply (x := x) mX mY mZ
  have l2 := leibniz_identity_mlieBracket_apply (x := x) mY mZ mX
  have l3 := leibniz_identity_mlieBracket_apply (x := x) mZ mX mY
  have l4 := leibniz_identity_mlieBracket_apply (x := x) mY mX mZ
  have l5 := leibniz_identity_mlieBracket_apply (x := x) mZ mY mX
  have l6 := leibniz_identity_mlieBracket_apply (x := x) mX mZ mY
  have s1 : mlieBracket I (mlieBracket I X Y) Z x
      = - mlieBracket I Z (mlieBracket I X Y) x := mlieBracket_swap_apply
  have s2 : mlieBracket I (mlieBracket I Y Z) X x
      = - mlieBracket I X (mlieBracket I Y Z) x := mlieBracket_swap_apply
  have s3 : mlieBracket I (mlieBracket I Z X) Y x
      = - mlieBracket I Y (mlieBracket I Z X) x := mlieBracket_swap_apply
  have s4 : mlieBracket I (mlieBracket I Y X) Z x
      = - mlieBracket I Z (mlieBracket I Y X) x := mlieBracket_swap_apply
  have s5 : mlieBracket I (mlieBracket I Z Y) X x
      = - mlieBracket I X (mlieBracket I Z Y) x := mlieBracket_swap_apply
  have s6 : mlieBracket I (mlieBracket I X Z) Y x
      = - mlieBracket I Y (mlieBracket I X Z) x := mlieBracket_swap_apply
  have h1 : (2 : ℝ) • (mlieBracket I X (mlieBracket I Y Z) x
      + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x)
      = mlieBracket I Y (mlieBracket I X Z) x
        + mlieBracket I Z (mlieBracket I Y X) x
        + mlieBracket I X (mlieBracket I Z Y) x := by
    linear_combination (norm := module) l1 + l2 + l3 + s1 + s2 + s3
  have h2 : (2 : ℝ) • (mlieBracket I Y (mlieBracket I X Z) x
      + mlieBracket I Z (mlieBracket I Y X) x
      + mlieBracket I X (mlieBracket I Z Y) x)
      = mlieBracket I X (mlieBracket I Y Z) x
        + mlieBracket I Y (mlieBracket I Z X) x
        + mlieBracket I Z (mlieBracket I X Y) x := by
    linear_combination (norm := module) l4 + l5 + l6 + s4 + s5 + s6
  have jac : mlieBracket I X (mlieBracket I Y Z) x
      + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x = 0 := by
    linear_combination (norm := module)
      ((1 : ℝ)/3) • ((2 : ℝ) • h1 + h2)
  -- Assemble.
  simp only [curvatureOp_apply]
  linear_combination (norm := module) e1 + e2 + e3 + t1 + t2 + t3 + jac

end CovariantDerivative
