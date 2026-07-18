/-
Uniqueness of the Levi-Civita connection.

This module states pointwise metric compatibility and torsion-freeness for an
affine connection against an abstract fibrewise metric, and proves the
uniqueness half of the fundamental theorem of Riemannian geometry: two
torsion-free metric-compatible connections agree on differentiable sections.
The proof is the classical S₃ permutation argument on
`θ(X, Y, Z) = g((∇ - ∇')_X Y, Z)`, which is symmetric in `(X, Y)` by equal
torsion and antisymmetric in `(Y, Z)` by shared compatibility, hence zero.
-/

import Poincare.RiemannCurvatureOperator

noncomputable section

open Bundle Set FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [IsManifold I 1 M]
variable (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
variable (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))

/--
Pointwise metric compatibility of a connection with a fibrewise metric `g`:
the derivative of `g(Y, Z)` along any tangent vector obeys the Riemannian
product rule at `x`.
-/
def MetricCompatibleAt (x : M) : Prop :=
  ∀ {Y Z : Π y : M, TangentSpace I y},
    MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      ∀ v : TangentSpace I x,
        extDerivFun (fun y ↦ g y (Y y) (Z y)) x v =
          g x (cov Y x v) (Z x) + g x (Y x) (cov Z x v)

/--
Pointwise torsion-freeness of a connection: the symmetry defect of the
covariant derivative is the Lie bracket at `x`.
-/
def TorsionFreeAt (x : M) : Prop :=
  ∀ {X Y : Π y : M, TangentSpace I y},
    MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x

variable {g cov cov'} {x : M}

/--
**Uniqueness of the Levi-Civita connection** (pointwise form).  If `g` is
symmetric and nondegenerate at `x` and two connections are both
metric-compatible and torsion-free at `x`, then they agree at `x` on every
section differentiable at `x`.
-/
theorem leviCivita_unique_at
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hgnd : ∀ v : TangentSpace I x, (∀ w, g x v w = 0) → v = 0)
    (hc : MetricCompatibleAt g cov x) (hc' : MetricCompatibleAt g cov' x)
    (ht : TorsionFreeAt cov x) (ht' : TorsionFreeAt cov' x)
    {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov' σ x := by
  -- The difference of the two connections, evaluated on vector fields.
  set D : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) →
      TangentSpace I x :=
    fun X Y ↦ cov Y x (X x) - cov' Y x (X x) with hD
  -- Antisymmetry of `g (D X Y) (Z x)` in `(Y, Z)`, from shared compatibility.
  have hA : ∀ {X Y Z : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        g x (D X Y) (Z x) = - g x (D X Z) (Y x) := by
    intro X Y Z hX hY hZ
    have h3 : g x (cov Y x (X x)) (Z x) + g x (Y x) (cov Z x (X x)) =
        g x (cov' Y x (X x)) (Z x) + g x (Y x) (cov' Z x (X x)) :=
      (hc hY hZ (X x)).symm.trans (hc' hY hZ (X x))
    have e1 : g x (D X Y) (Z x) =
        g x (cov Y x (X x)) (Z x) - g x (cov' Y x (X x)) (Z x) := by
      simp [hD, map_sub]
    have e2 : g x (D X Z) (Y x) =
        g x (Y x) (cov Z x (X x)) - g x (Y x) (cov' Z x (X x)) := by
      rw [hgsymm]
      simp [hD, map_sub]
    linarith
  -- Symmetry of `D` in its two arguments, from equal torsion.
  have hB : ∀ {X Y : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x → D X Y = D Y X := by
    intro X Y hX hY
    have t1 := ht hX hY
    have t1' := ht' hX hY
    have : (cov Y x (X x) - cov X x (Y x)) -
        (cov' Y x (X x) - cov' X x (Y x)) = 0 := by
      rw [t1, t1']
      abel
    simp only [hD]
    linear_combination (norm := module) this
  -- The S₃ permutation argument: `θ` is zero.
  have hS3 : ∀ {X Y Z : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        g x (D X Y) (Z x) = 0 := by
    intro X Y Z hX hY hZ
    have s1 : g x (D X Y) (Z x) = - g x (D X Z) (Y x) := hA hX hY hZ
    have s2 : g x (D X Z) (Y x) = g x (D Z X) (Y x) := by rw [hB hX hZ]
    have s3 : g x (D Z X) (Y x) = - g x (D Z Y) (X x) := hA hZ hX hY
    have s4 : g x (D Z Y) (X x) = g x (D Y Z) (X x) := by rw [hB hZ hY]
    have s5 : g x (D Y Z) (X x) = - g x (D Y X) (Z x) := hA hY hZ hX
    have s6 : g x (D Y X) (Z x) = g x (D X Y) (Z x) := by rw [hB hY hX]
    linarith
  -- Conclude by nondegeneracy, testing against extended sections.
  ext v
  have hv : D (extend E v) σ = cov σ x v - cov' σ x v := by
    simp [hD]
  refine sub_eq_zero.mp (hgnd _ fun w ↦ ?_)
  have h0 : g x (D (extend E v) σ) (extend E w x) = 0 :=
    hS3 (mdifferentiableAt_extend ..) hσ (mdifferentiableAt_extend ..)
  rw [hv] at h0
  simpa using h0

/--
Pointwise-value form of Levi-Civita uniqueness.  This is the same S₃
argument as `leviCivita_unique_at`, but it only assumes two value operators at
the fixed point `x` rather than globally bundled covariant derivatives.
-/
theorem leviCivita_unique_at_values
    (cov cov' :
      (Π y : M, TangentSpace I y) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hgnd : ∀ v : TangentSpace I x, (∀ w, g x v w = 0) → v = 0)
    (hc : ∀ {Y Z : Π y : M, TangentSpace I y},
      MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        ∀ v : TangentSpace I x,
          extDerivFun (fun y ↦ g y (Y y) (Z y)) x v =
            g x (cov Y v) (Z x) + g x (Y x) (cov Z v))
    (hc' : ∀ {Y Z : Π y : M, TangentSpace I y},
      MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        ∀ v : TangentSpace I x,
          extDerivFun (fun y ↦ g y (Y y) (Z y)) x v =
            g x (cov' Y v) (Z x) + g x (Y x) (cov' Z v))
    (ht : ∀ {X Y : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
        cov Y (X x) - cov X (Y x) = VectorField.mlieBracket I X Y x)
    (ht' : ∀ {X Y : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
        cov' Y (X x) - cov' X (Y x) = VectorField.mlieBracket I X Y x)
    {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    cov σ = cov' σ := by
  set D : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) →
      TangentSpace I x :=
    fun X Y ↦ cov Y (X x) - cov' Y (X x) with hD
  have hA : ∀ {X Y Z : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        g x (D X Y) (Z x) = - g x (D X Z) (Y x) := by
    intro X Y Z hX hY hZ
    have h3 : g x (cov Y (X x)) (Z x) + g x (Y x) (cov Z (X x)) =
        g x (cov' Y (X x)) (Z x) + g x (Y x) (cov' Z (X x)) :=
      (hc hY hZ (X x)).symm.trans (hc' hY hZ (X x))
    have e1 : g x (D X Y) (Z x) =
        g x (cov Y (X x)) (Z x) - g x (cov' Y (X x)) (Z x) := by
      simp [hD, map_sub]
    have e2 : g x (D X Z) (Y x) =
        g x (Y x) (cov Z (X x)) - g x (Y x) (cov' Z (X x)) := by
      rw [hgsymm]
      simp [hD, map_sub]
    linarith
  have hB : ∀ {X Y : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x → D X Y = D Y X := by
    intro X Y hX hY
    have t1 := ht hX hY
    have t1' := ht' hX hY
    have : (cov Y (X x) - cov X (Y x)) -
        (cov' Y (X x) - cov' X (Y x)) = 0 := by
      rw [t1, t1']
      abel
    simp only [hD]
    linear_combination (norm := module) this
  have hS3 : ∀ {X Y Z : Π y : M, TangentSpace I y},
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        g x (D X Y) (Z x) = 0 := by
    intro X Y Z hX hY hZ
    have s1 : g x (D X Y) (Z x) = - g x (D X Z) (Y x) := hA hX hY hZ
    have s2 : g x (D X Z) (Y x) = g x (D Z X) (Y x) := by rw [hB hX hZ]
    have s3 : g x (D Z X) (Y x) = - g x (D Z Y) (X x) := hA hZ hX hY
    have s4 : g x (D Z Y) (X x) = g x (D Y Z) (X x) := by rw [hB hZ hY]
    have s5 : g x (D Y Z) (X x) = - g x (D Y X) (Z x) := hA hY hZ hX
    have s6 : g x (D Y X) (Z x) = g x (D X Y) (Z x) := by rw [hB hY hX]
    linarith
  ext v
  have hv : D (extend E v) σ = cov σ v - cov' σ v := by
    simp [hD]
  refine sub_eq_zero.mp (hgnd _ fun w ↦ ?_)
  have h0 : g x (D (extend E v) σ) (extend E w x) = 0 :=
    hS3 (mdifferentiableAt_extend ..) hσ (mdifferentiableAt_extend ..)
  rw [hv] at h0
  simpa using h0

end CovariantDerivative

namespace CovariantDerivative

variable [IsManifold I 1 M]
variable {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)} {x : M}

/--
**The Koszul formula.**  Any torsion-free metric-compatible connection
satisfies
`2 g(∇_X Y, Z) = X g(Y,Z) + Y g(X,Z) - Z g(X,Y)
  + g([X,Y],Z) - g([X,Z],Y) - g([Y,Z],X)`,
so the metric determines the connection on differentiable fields.  This is
the computational core of both halves of the fundamental theorem of
Riemannian geometry.
-/
theorem koszul_formula
    (hgsymm : ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hc : MetricCompatibleAt g cov x) (ht : TorsionFreeAt cov x)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * g x (cov Y x (X x)) (Z x) =
      extDerivFun (fun y ↦ g y (Y y) (Z y)) x (X x)
        + extDerivFun (fun y ↦ g y (X y) (Z y)) x (Y x)
        - extDerivFun (fun y ↦ g y (X y) (Y y)) x (Z x)
        + g x (VectorField.mlieBracket I X Y x) (Z x)
        - g x (VectorField.mlieBracket I X Z x) (Y x)
        - g x (VectorField.mlieBracket I Y Z x) (X x) := by
  have c1 := hc hY hZ (X x)
  have c2 := hc hX hZ (Y x)
  have c3 := hc hX hY (Z x)
  have p1 : g x (cov Y x (X x)) (Z x) - g x (cov X x (Y x)) (Z x)
      = g x (VectorField.mlieBracket I X Y x) (Z x) := by
    rw [← ContinuousLinearMap.sub_apply, ← map_sub, ht hX hY]
  have p2 : g x (cov Z x (X x)) (Y x) - g x (cov X x (Z x)) (Y x)
      = g x (VectorField.mlieBracket I X Z x) (Y x) := by
    rw [← ContinuousLinearMap.sub_apply, ← map_sub, ht hX hZ]
  have p3 : g x (cov Z x (Y x)) (X x) - g x (cov Y x (Z x)) (X x)
      = g x (VectorField.mlieBracket I Y Z x) (X x) := by
    rw [← ContinuousLinearMap.sub_apply, ← map_sub, ht hY hZ]
  have sy1 : g x (Y x) (cov Z x (X x)) = g x (cov Z x (X x)) (Y x) :=
    hgsymm _ _
  have sy2 : g x (X x) (cov Z x (Y x)) = g x (cov Z x (Y x)) (X x) :=
    hgsymm _ _
  have sy3 : g x (X x) (cov Y x (Z x)) = g x (cov Y x (Z x)) (X x) :=
    hgsymm _ _
  linarith

end CovariantDerivative

/-!
Generated shape equality contracts for `scripts/shape_contract_audit.sh`.
These record the exposed definition names without changing the definitions.
-/

namespace CovariantDerivative

/-- Shape contract for `MetricCompatibleAt`. -/
theorem metricCompatibleAt_eq :
    @CovariantDerivative.MetricCompatibleAt = @CovariantDerivative.MetricCompatibleAt :=
  rfl

/-- Shape contract for `TorsionFreeAt`. -/
theorem torsionFreeAt_eq :
    @CovariantDerivative.TorsionFreeAt = @CovariantDerivative.TorsionFreeAt :=
  rfl

end CovariantDerivative

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

namespace CovariantDerivative

/-- Theorem contract for `leviCivita_unique_at`. -/
theorem leviCivita_unique_at_eq :
    @CovariantDerivative.leviCivita_unique_at = @CovariantDerivative.leviCivita_unique_at :=
  rfl

/-- Theorem contract for `leviCivita_unique_at_values`. -/
theorem leviCivita_unique_at_values_eq :
    @CovariantDerivative.leviCivita_unique_at_values =
      @CovariantDerivative.leviCivita_unique_at_values :=
  rfl

/-- Theorem contract for `koszul_formula`. -/
theorem koszul_formula_eq :
    @CovariantDerivative.koszul_formula = @CovariantDerivative.koszul_formula :=
  rfl

end CovariantDerivative
