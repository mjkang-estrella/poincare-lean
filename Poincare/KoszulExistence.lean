/-
Towards Levi-Civita existence: the Koszul functional.

The Koszul formula determines `2 g(∇_X Y, Z)` from the metric and brackets.
To *construct* the Levi-Civita connection one must know that the Koszul
right-hand side is tensorial in the test field `Z`; this module defines the
functional and proves that tensoriality: the derivative cross terms cancel
against the bracket correction terms by symmetry of the metric.
-/

import Poincare.CurvatureTensoriality

noncomputable section

open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

namespace CovariantDerivative

/-- The product rule for the exterior derivative of scalar functions. -/
theorem extDerivFun_mul {p q : M → ℝ} {x : M}
    (hp : MDiffAt p x) (hq : MDiffAt q x) (v : TangentSpace I x) :
    extDerivFun (I := I) (p * q) x v =
      p x * extDerivFun q x v + extDerivFun p x v * q x := by
  unfold extDerivFun
  rw [(hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mfderiv]
  have key : ∀ a b A B : ℝ, a • A + MulOpposite.op b • B = a * A + B * b := by
    intro a b A B
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  exact key (p x) (q x) ((mfderiv% q x) v) ((mfderiv% p x) v)

variable (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)

/--
The Koszul right-hand side: the expression determining `2 g(∇_X Y, Z)` for
the Levi-Civita connection of `g`.
-/
def koszulRHS (X Y Z : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  extDerivFun (fun y ↦ g y (Y y) (Z y)) x (X x)
    + extDerivFun (fun y ↦ g y (X y) (Z y)) x (Y x)
    - extDerivFun (fun y ↦ g y (X y) (Y y)) x (Z x)
    + g x (mlieBracket I X Y x) (Z x)
    - g x (mlieBracket I X Z x) (Y x)
    - g x (mlieBracket I Y Z x) (X x)

variable {g}

/--
**Tensoriality of the Koszul functional in the test field** (smul law):
the derivative cross terms cancel against the bracket corrections by
symmetry of the metric.
-/
theorem koszulRHS_smul_right {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    {f : M → ℝ} (hf : MDiffAt f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x)
    (hPYZ : MDiffAt (fun y ↦ g y (Y y) (Z y)) x)
    (hPXZ : MDiffAt (fun y ↦ g y (X y) (Z y)) x) :
    koszulRHS g X Y (f • Z) x = f x * koszulRHS g X Y Z x := by
  -- The pairings against `f • Z` are products.
  have hfun : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ g y (W y) ((f • Z) y)) = f * fun y ↦ g y (W y) (Z y) := by
    intro W
    funext y
    simp [smul_eq_mul]
  -- Expand the two derivative terms by the product rule.
  have e1 : extDerivFun (fun y ↦ g y (Y y) ((f • Z) y)) x (X x) =
      f x * extDerivFun (fun y ↦ g y (Y y) (Z y)) x (X x)
        + extDerivFun f x (X x) * g x (Y x) (Z x) := by
    rw [hfun Y, extDerivFun_mul hf hPYZ]
  have e2 : extDerivFun (fun y ↦ g y (X y) ((f • Z) y)) x (Y x) =
      f x * extDerivFun (fun y ↦ g y (X y) (Z y)) x (Y x)
        + extDerivFun f x (Y x) * g x (X x) (Z x) := by
    rw [hfun X, extDerivFun_mul hf hPXZ]
  -- The third derivative term is pointwise linear in the direction.
  have e3 : extDerivFun (fun y ↦ g y (X y) (Y y)) x ((f • Z) x) =
      f x * extDerivFun (fun y ↦ g y (X y) (Y y)) x (Z x) := by
    have : (f • Z) x = f x • Z x := rfl
    rw [this, map_smul]
    simp
  -- The bracket terms via the smul law for the Lie bracket.
  have e4 : g x (mlieBracket I X (f • Z) x) (Y x) =
      extDerivFun f x (X x) * g x (Z x) (Y x)
        + f x * g x (mlieBracket I X Z x) (Y x) := by
    rw [mlieBracket_smul_right hf hZ]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  have e5 : g x (mlieBracket I Y (f • Z) x) (X x) =
      extDerivFun f x (Y x) * g x (Z x) (X x)
        + f x * g x (mlieBracket I Y Z x) (X x) := by
    rw [mlieBracket_smul_right hf hZ]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  -- The pair term is pointwise linear in the second slot.
  have e6 : g x (mlieBracket I X Y x) ((f • Z) x) =
      f x * g x (mlieBracket I X Y x) (Z x) := by
    have : (f • Z) x = f x • Z x := rfl
    rw [this, map_smul]
    simp
  unfold koszulRHS
  rw [e1, e2, e3, e4, e5, e6]
  linear_combination
    extDerivFun (I := I) f x (X x) * hgsymm (Y x) (Z x)
      + extDerivFun (I := I) f x (Y x) * hgsymm (X x) (Z x)

/--
**Additivity of the Koszul functional in the test field.**
-/
theorem koszulRHS_add_right {X Y Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x)
    (hPYZ : MDiffAt (fun y ↦ g y (Y y) (Z y)) x)
    (hPYZ' : MDiffAt (fun y ↦ g y (Y y) (Z' y)) x)
    (hPXZ : MDiffAt (fun y ↦ g y (X y) (Z y)) x)
    (hPXZ' : MDiffAt (fun y ↦ g y (X y) (Z' y)) x) :
    koszulRHS g X Y (Z + Z') x =
      koszulRHS g X Y Z x + koszulRHS g X Y Z' x := by
  have hfun : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ g y (W y) ((Z + Z') y)) =
        (fun y ↦ g y (W y) (Z y)) + fun y ↦ g y (W y) (Z' y) := by
    intro W
    funext y
    simp
  have e1 : extDerivFun (fun y ↦ g y (Y y) ((Z + Z') y)) x (X x) =
      extDerivFun (fun y ↦ g y (Y y) (Z y)) x (X x)
        + extDerivFun (fun y ↦ g y (Y y) (Z' y)) x (X x) := by
    rw [hfun Y, extDerivFun_add hPYZ hPYZ']
    simp
  have e2 : extDerivFun (fun y ↦ g y (X y) ((Z + Z') y)) x (Y x) =
      extDerivFun (fun y ↦ g y (X y) (Z y)) x (Y x)
        + extDerivFun (fun y ↦ g y (X y) (Z' y)) x (Y x) := by
    rw [hfun X, extDerivFun_add hPXZ hPXZ']
    simp
  have e3 : extDerivFun (fun y ↦ g y (X y) (Y y)) x ((Z + Z') x) =
      extDerivFun (fun y ↦ g y (X y) (Y y)) x (Z x)
        + extDerivFun (fun y ↦ g y (X y) (Y y)) x (Z' x) := by
    have h : (Z + Z') x = Z x + Z' x := rfl
    rw [h, map_add]
  have e4 : g x (mlieBracket I X (Z + Z') x) (Y x) =
      g x (mlieBracket I X Z x) (Y x)
        + g x (mlieBracket I X Z' x) (Y x) := by
    rw [mlieBracket_add_right hZ hZ']
    simp
  have e5 : g x (mlieBracket I Y (Z + Z') x) (X x) =
      g x (mlieBracket I Y Z x) (X x)
        + g x (mlieBracket I Y Z' x) (X x) := by
    rw [mlieBracket_add_right hZ hZ']
    simp
  have e6 : g x (mlieBracket I X Y x) ((Z + Z') x) =
      g x (mlieBracket I X Y x) (Z x)
        + g x (mlieBracket I X Y x) (Z' x) := by
    have h : (Z + Z') x = Z x + Z' x := rfl
    rw [h, map_add]
  unfold koszulRHS
  rw [e1, e2, e3, e4, e5, e6]
  ring

end CovariantDerivative
