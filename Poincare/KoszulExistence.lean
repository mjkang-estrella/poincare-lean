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

section ValueDependence

variable [FiniteDimensional ℝ E] [T2Space M]

private theorem extDerivFun_congr' {f f' : M → ℝ} {x : M}
    (h : f =ᶠ[𝓝 x] f') :
    extDerivFun (I := I) f x = extDerivFun (I := I) f' x := by
  unfold extDerivFun
  rw [h.mfderiv_eq, h.self_of_nhds]

/-- The Koszul functional vanishes on the zero test field. -/
theorem koszulRHS_zero_right {X Y : Π y : M, TangentSpace I y} {x : M} :
    koszulRHS g X Y 0 x = 0 := by
  have h0 : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ g y (W y) ((0 : Π y : M, TangentSpace I y) y)) =
        fun _ : M ↦ (0 : ℝ) := by
    intro W
    funext y
    simp
  have hED : extDerivFun (I := I) (fun _ : M ↦ (0 : ℝ)) x = 0 := by
    unfold extDerivFun
    rw [(hasMFDerivAt_const (0 : ℝ) x).mfderiv]
    ext v
    simp
  unfold koszulRHS
  rw [h0 Y, h0 X, hED]
  simp [VectorField.mlieBracket_zero_right]

/-- Germ locality of the Koszul functional in the test field. -/
theorem koszulRHS_congr_of_eventuallyEq
    {X Y Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hZZ' : Z =ᶠ[𝓝 x] Z') :
    koszulRHS g X Y Z x = koszulRHS g X Y Z' x := by
  have hpair : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ g y (W y) (Z y)) =ᶠ[𝓝 x] fun y ↦ g y (W y) (Z' y) := by
    intro W
    filter_upwards [hZZ'] with y hy
    rw [hy]
  have hx0 : Z x = Z' x := hZZ'.self_of_nhds
  unfold koszulRHS
  rw [extDerivFun_congr' (hpair Y), extDerivFun_congr' (hpair X), hx0,
    Filter.EventuallyEq.mlieBracket_vectorField_eq
      (Filter.EventuallyEq.rfl (f := X)) hZZ',
    Filter.EventuallyEq.mlieBracket_vectorField_eq
      (Filter.EventuallyEq.rfl (f := Y)) hZZ']

/-- The Koszul functional distributes over finite sums of test fields. -/
theorem koszulRHS_finsetSum_right {ι : Type*} [DecidableEq ι]
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (s : Finset ι) (Zs : ι → Π y : M, TangentSpace I y)
    (hZs : ∀ i, MDiffAt (T% (Zs i)) x) :
    koszulRHS g X Y (fun y ↦ ∑ i ∈ s, Zs i y) x =
      ∑ i ∈ s, koszulRHS g X Y (Zs i) x := by
  induction s using Finset.induction with
  | empty => simpa using koszulRHS_zero_right (g := g) (X := X) (Y := Y)
  | insert a s ha ih =>
    have hsum : (fun y ↦ ∑ i ∈ insert a s, Zs i y) =
        Zs a + fun y ↦ ∑ i ∈ s, Zs i y := by
      funext y
      simp [Finset.sum_insert ha]
    have hsd : MDiffAt (T% (fun y ↦ ∑ i ∈ s, Zs i y)) x :=
      MDifferentiableAt.sum_section fun i ↦ hZs i
    rw [hsum, koszulRHS_add_right (hZs a) hsd
      (hP _ _ hY (hZs a)) (hP _ _ hY hsd)
      (hP _ _ hX (hZs a)) (hP _ _ hX hsd),
      Finset.sum_insert ha, ih]

open Trivialization in
/-- The Koszul functional vanishes on differentiable fields vanishing at the
point. -/
theorem koszulRHS_eq_zero_of_value_eq_zero
    {X Y D : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (hD : MDiffAt (T% D) x) (hDx : D x = 0) :
    koszulRHS g X Y D x = 0 := by
  classical
  set e := trivializationAt E (TangentSpace I) x with he
  set b := Module.finBasis ℝ E with hb
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hev := e.eventually_eq_localFrame_sum_coeff_smul (I := I) b
    (s := D) hxe
  have hframe : ∀ i, MDiffAt (T% (e.localFrame b i)) x := fun i ↦
    (contMDiffAt_localFrame_of_mem (I := I) (n := 1) (e := e) (b := b) i
      hxe).mdifferentiableAt one_ne_zero
  have hcoeff : ∀ i, MDiffAt (fun y ↦ e.localFrame_coeff I b i y (D y)) x :=
    fun i ↦ (mdifferentiableAt_iff_localFrame_coeff (I := I) (e := e)
      (b := b) hxe).mp hD i
  set Zs : _ → Π y : M, TangentSpace I y := fun i ↦
    (fun y ↦ e.localFrame_coeff I b i y (D y)) • e.localFrame b i with hZs
  have hsummand : ∀ i, MDiffAt (T% (Zs i)) x := fun i ↦
    (hcoeff i).smul_section (hframe i)
  have h1 : koszulRHS g X Y D x =
      koszulRHS g X Y (fun y ↦ ∑ i, Zs i y) x := by
    apply koszulRHS_congr_of_eventuallyEq
    filter_upwards [hev] with y hy
    simpa [hZs] using hy
  rw [h1, koszulRHS_finsetSum_right hgsymm hX hY hP Finset.univ Zs
    hsummand]
  have hzero : ∀ i, koszulRHS g X Y (Zs i) x = 0 := by
    intro i
    rw [hZs]
    rw [koszulRHS_smul_right hgsymm (hcoeff i) hX hY (hframe i)
      (hP _ _ hY (hframe i)) (hP _ _ hX (hframe i))]
    have hc0 : e.localFrame_coeff I b i x (D x) = 0 := by
      rw [hDx]
      exact map_zero _
    rw [hc0, zero_mul]
  simp [hzero]

/-- The Koszul functional depends only on the value of the test field. -/
theorem koszulRHS_congr_of_value_eq
    {X Y Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x)
    (hZZ' : Z x = Z' x) :
    koszulRHS g X Y Z x = koszulRHS g X Y Z' x := by
  have hns : MDiffAt (T% ((-1 : ℝ) • Z')) x :=
    mdifferentiableAt_const.smul_section hZ'
  have hD : MDiffAt (T% (Z + (-1 : ℝ) • Z')) x :=
    mdifferentiableAt_add_section hZ hns
  have hDx : (Z + (-1 : ℝ) • Z') x = 0 := by
    simp [hZZ']
  have h0 := koszulRHS_eq_zero_of_value_eq_zero hgsymm hX hY hP hD hDx
  rw [koszulRHS_add_right hZ hns (hP _ _ hY hZ) (hP _ _ hY hns)
    (hP _ _ hX hZ) (hP _ _ hX hns),
    show ((-1 : ℝ) • Z') = (fun _ : M ↦ (-1 : ℝ)) • Z' from rfl,
    koszulRHS_smul_right hgsymm mdifferentiableAt_const hX hY hZ'
      (hP _ _ hY hZ') (hP _ _ hX hZ')] at h0
  linarith

end ValueDependence

section Construction

open FiberBundle

variable [FiniteDimensional ℝ E] [T2Space M]
variable (g)

/--
The pointwise Koszul functional: the Koszul right-hand side as a linear
functional on the tangent space at `x`, through canonical extensions.
-/
noncomputable def koszulFunctionalAt {X Y : Π y : M, TangentSpace I y}
    {x : M}
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x) :
    TangentSpace I x →ₗ[ℝ] ℝ where
  toFun z := koszulRHS g X Y (extend E z) x
  map_add' z z' := by
    have h1 : koszulRHS g X Y (extend E (z + z')) x =
        koszulRHS g X Y (extend E z + extend E z') x :=
      koszulRHS_congr_of_value_eq hgsymm hX hY hP
        (mdifferentiableAt_extend ..)
        (mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
          (mdifferentiableAt_extend ..))
        (by simp)
    rw [h1, koszulRHS_add_right (mdifferentiableAt_extend ..)
      (mdifferentiableAt_extend ..)
      (hP _ _ hY (mdifferentiableAt_extend ..))
      (hP _ _ hY (mdifferentiableAt_extend ..))
      (hP _ _ hX (mdifferentiableAt_extend ..))
      (hP _ _ hX (mdifferentiableAt_extend ..))]
  map_smul' c z := by
    have h1 : koszulRHS g X Y (extend E (c • z)) x =
        koszulRHS g X Y ((fun _ : M ↦ c) • extend E z) x :=
      koszulRHS_congr_of_value_eq hgsymm hX hY hP
        (mdifferentiableAt_extend ..)
        (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..))
        (by simp)
    rw [h1, koszulRHS_smul_right hgsymm mdifferentiableAt_const hX hY
      (mdifferentiableAt_extend ..)
      (hP _ _ hY (mdifferentiableAt_extend ..))
      (hP _ _ hX (mdifferentiableAt_extend ..))]
    simp

/--
The Levi-Civita candidate value `∇_X Y (x)`: the metric dual of half the
Koszul functional.
-/
noncomputable def leviCivitaValueAt {X Y : Π y : M, TangentSpace I y}
    {x : M}
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (b : LinearMap.BilinForm ℝ (TangentSpace I x)) (hb : b.Nondegenerate) :
    TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := ‹FiniteDimensional ℝ E›
  (LinearMap.BilinForm.toDual b hb).symm
    ((1 / 2 : ℝ) • koszulFunctionalAt g hgsymm hX hY hP)

/--
**The defining property of the Levi-Civita value**: it satisfies the Koszul
formula against every tangent vector.
-/
theorem b_leviCivitaValueAt {X Y : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (b : LinearMap.BilinForm ℝ (TangentSpace I x)) (hb : b.Nondegenerate)
    (z : TangentSpace I x) :
    b (leviCivitaValueAt g hgsymm hX hY hP b hb) z =
      (1 / 2 : ℝ) * koszulRHS g X Y (extend E z) x := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := ‹FiniteDimensional ℝ E›
  unfold leviCivitaValueAt
  have h := LinearEquiv.apply_symm_apply (LinearMap.BilinForm.toDual b hb)
    ((1 / 2 : ℝ) • koszulFunctionalAt g hgsymm hX hY hP)
  have h2 := congrArg (fun ψ ↦ ψ z) h
  simp only at h2
  rw [show (LinearMap.BilinForm.toDual b hb)
      ((LinearMap.BilinForm.toDual b hb).symm
        ((1 / 2 : ℝ) • koszulFunctionalAt g hgsymm hX hY hP)) z =
      b ((LinearMap.BilinForm.toDual b hb).symm
        ((1 / 2 : ℝ) • koszulFunctionalAt g hgsymm hX hY hP)) z from
    (LinearMap.BilinForm.toDual_def hb)] at h2
  rw [h2]
  simp [koszulFunctionalAt]

/--
The Koszul swap identity: antisymmetrizing the Koszul functional in `(X,Y)`
leaves exactly twice the bracket pairing.
-/
theorem koszulRHS_sub_swap {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v) :
    koszulRHS g X Y Z x - koszulRHS g Y X Z x =
      2 * g x (mlieBracket I X Y x) (Z x) := by
  have hfun : (fun y ↦ g y (Y y) (X y)) = fun y ↦ g y (X y) (Y y) := by
    funext y
    exact hgsymm y (Y y) (X y)
  have hbr : g x (mlieBracket I Y X x) (Z x) =
      - g x (mlieBracket I X Y x) (Z x) := by
    rw [mlieBracket_swap_apply]
    simp
  unfold koszulRHS
  rw [hfun, hbr]
  ring

/--
**Torsion-freeness of the Levi-Civita candidate**: the symmetry defect of
the constructed value is the Lie bracket.
-/
theorem leviCivitaValueAt_torsionFree {X Y : Π y : M, TangentSpace I y}
    {x : M}
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (b : LinearMap.BilinForm ℝ (TangentSpace I x)) (hb : b.Nondegenerate)
    (hbg : ∀ v w : TangentSpace I x, b v w = g x v w) :
    leviCivitaValueAt g (hgsymm x) hX hY hP b hb
      - leviCivitaValueAt g (hgsymm x) hY hX hP b hb
      = mlieBracket I X Y x := by
  apply sub_eq_zero.mp
  apply hb.1
  intro z
  simp only [map_sub, LinearMap.sub_apply]
  rw [b_leviCivitaValueAt g (hgsymm x) hX hY hP b hb z,
    b_leviCivitaValueAt g (hgsymm x) hY hX hP b hb z,
    hbg (mlieBracket I X Y x) z]
  have hsw := koszulRHS_sub_swap (g := g) (X := X) (Y := Y)
    (Z := extend E z) (x := x) hgsymm
  rw [extend_apply_self] at hsw
  linarith

/--
The Koszul sum identity: symmetrizing the Koszul functional over the last
two fields gives twice the derivative of the pairing.
-/
theorem koszulRHS_add_swap_last {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v) :
    koszulRHS g X Y Z x + koszulRHS g X Z Y x =
      2 * extDerivFun (fun y ↦ g y (Y y) (Z y)) x (X x) := by
  have hfun : (fun y ↦ g y (Z y) (Y y)) = fun y ↦ g y (Y y) (Z y) := by
    funext y
    exact hgsymm y (Z y) (Y y)
  have hbr : g x (mlieBracket I Z Y x) (X x) =
      - g x (mlieBracket I Y Z x) (X x) := by
    rw [mlieBracket_swap_apply]
    simp
  unfold koszulRHS
  rw [hfun, hbr]
  ring

/--
**Metric compatibility of the Levi-Civita candidate**: the derivative of the
pairing along `X` is the Riemannian product rule with the constructed
values.
-/
theorem leviCivitaValueAt_compat {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (b : LinearMap.BilinForm ℝ (TangentSpace I x)) (hb : b.Nondegenerate)
    (hbg : ∀ v w : TangentSpace I x, b v w = g x v w) :
    extDerivFun (fun y ↦ g y (Y y) (Z y)) x (X x) =
      g x (leviCivitaValueAt g (hgsymm x) hX hY hP b hb) (Z x)
        + g x (Y x) (leviCivitaValueAt g (hgsymm x) hX hZ hP b hb) := by
  have h1 : g x (leviCivitaValueAt g (hgsymm x) hX hY hP b hb) (Z x) =
      (1 / 2 : ℝ) * koszulRHS g X Y Z x := by
    rw [← hbg, b_leviCivitaValueAt g (hgsymm x) hX hY hP b hb (Z x)]
    congr 1
    exact koszulRHS_congr_of_value_eq (hgsymm x) hX hY hP
      (mdifferentiableAt_extend ..) hZ (by simp)
  have h2 : g x (Y x) (leviCivitaValueAt g (hgsymm x) hX hZ hP b hb) =
      (1 / 2 : ℝ) * koszulRHS g X Z Y x := by
    rw [hgsymm x (Y x) _, ← hbg,
      b_leviCivitaValueAt g (hgsymm x) hX hZ hP b hb (Y x)]
    congr 1
    exact koszulRHS_congr_of_value_eq (hgsymm x) hX hZ hP
      (mdifferentiableAt_extend ..) hY (by simp)
  have hsum := koszulRHS_add_swap_last (g := g) (X := X) (Y := Y) (Z := Z)
    (x := x) hgsymm
  linarith

end Construction

end CovariantDerivative
