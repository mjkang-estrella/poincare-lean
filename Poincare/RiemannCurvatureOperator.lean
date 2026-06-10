/-
Riemann curvature operator of an affine connection.

Mathlib (as of this toolchain) provides covariant derivatives on vector
bundles and the torsion tensor of an affine connection, but no curvature.
This module defines the Riemann curvature operator

  R(X, Y) Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_[X,Y] Z

of a covariant derivative on the tangent bundle, as a bare trilinear-in-shape
operator on vector fields, and proves its first real properties:
antisymmetry in `X, Y` and vanishing on the diagonal.  This is the first
content-bearing building block toward stating the Ricci tensor, Ricci flow,
and the curvature conditions used by the finite-extinction pillar.
-/

import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [IsManifold I 1 M]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/--
The Riemann curvature operator of an affine connection, as a bare operator on
vector fields: `R(X, Y) Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_[X,Y] Z`.

Recall the Mathlib convention `cov σ x (X x) = (∇_X σ) x`.
-/
def curvatureOp (X Y Z : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun x ↦
    cov (fun y ↦ cov Z y (Y y)) x (X x)
      - cov (fun y ↦ cov Z y (X y)) x (Y x)
      - cov Z x (VectorField.mlieBracket I X Y x)

theorem curvatureOp_apply (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    curvatureOp cov X Y Z x =
      cov (fun y ↦ cov Z y (Y y)) x (X x)
        - cov (fun y ↦ cov Z y (X y)) x (Y x)
        - cov Z x (VectorField.mlieBracket I X Y x) :=
  rfl

/-- The curvature operator is antisymmetric in its first two arguments. -/
theorem curvatureOp_antisymm (X Y Z : Π x : M, TangentSpace I x) :
    curvatureOp cov X Y Z = - curvatureOp cov Y X Z := by
  funext x
  rw [Pi.neg_apply, curvatureOp_apply, curvatureOp_apply,
    VectorField.mlieBracket_swap_apply, map_neg]
  abel

/-- The curvature operator vanishes when its first two arguments agree. -/
@[simp]
theorem curvatureOp_self (X Z : Π x : M, TangentSpace I x) :
    curvatureOp cov X X Z = 0 := by
  funext x
  simp [curvatureOp]

/-- Pointwise antisymmetry of the curvature operator. -/
theorem curvatureOp_antisymm_apply (X Y Z : Π x : M, TangentSpace I x)
    (x : M) :
    curvatureOp cov X Y Z x = - curvatureOp cov Y X Z x := by
  rw [curvatureOp_antisymm]
  rfl

/--
Flatness of an affine connection: the curvature operator vanishes on all
vector fields.  The model flat case and the `dim = 3` curvature conditions of
the finite-extinction pillar will be stated against this predicate.
-/
def IsFlat : Prop :=
  ∀ X Y Z : Π x : M, TangentSpace I x, curvatureOp cov X Y Z = 0

theorem isFlat_iff :
    IsFlat cov ↔
      ∀ X Y Z : Π x : M, TangentSpace I x, curvatureOp cov X Y Z = 0 :=
  Iff.rfl

end CovariantDerivative
