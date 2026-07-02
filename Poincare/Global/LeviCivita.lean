import Poincare.Global.RiemannianContext
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Levi-Civita uniqueness in the global Mathlib manifold layer

This file records the uniqueness half of the Levi-Civita theorem for the
project's closed smooth Riemannian context.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- A tangent vector field is differentiable at a point as a section of the tangent bundle. -/
abbrev MDiffAtTangentField
    (X : ∀ y : M, TangentSpace (closedSmoothModelWithCorners n) y) (x : M) : Prop :=
  MDifferentiableAt (closedSmoothModelWithCorners n)
    ((closedSmoothModelWithCorners n).prod 𝓘(ℝ, ClosedSmoothModel n))
    (fun y : M =>
      (X y : TotalSpace (ClosedSmoothModel n)
        (TangentSpace (closedSmoothModelWithCorners n) : M → Type _))) x

/--
Metric compatibility of a covariant derivative on the tangent bundle with a
smooth Riemannian metric.

The derivative is written using `extDerivFun`, Mathlib's scalar exterior
derivative wrapper around `mfderiv`.  The hypotheses are pointwise `MDiffAt`
section hypotheses, matching `CovariantDerivative.torsion_apply` and
`CovariantDerivative.difference`; in particular, Mathlib's locally defined
`extend` sections can be used in the uniqueness proof below.
-/
def IsMetricCompatible (g : ClosedSmoothRiemannianMetric n M)
    (cov : CovariantDerivative (closedSmoothModelWithCorners n) (ClosedSmoothModel n)
      (TangentSpace (closedSmoothModelWithCorners n) : M → Type _)) : Prop :=
  ∀ ⦃x : M⦄
    ⦃X Y : ∀ y : M, TangentSpace (closedSmoothModelWithCorners n) y⦄,
    MDiffAtTangentField X x → MDiffAtTangentField Y x →
      ∀ v : TangentSpace (closedSmoothModelWithCorners n) x,
        extDerivFun (I := closedSmoothModelWithCorners n)
            (fun y : M => g.inner y (X y) (Y y)) x v =
          g.inner x (cov X x v) (Y x) + g.inner x (X x) (cov Y x v)

namespace LeviCivita

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

variable (g : ClosedSmoothRiemannianMetric n M)

private lemma difference_apply_tangent (cov cov' : CovariantDerivative I E TM)
    {x : M} {X : ∀ y : M, TM y}
    (hX : MDiffAtTangentField X x) :
    (cov.difference cov') x (X x) = cov X x - cov' X x := by
  simpa [CovariantDerivative.difference] using
    (IsCovariantDerivativeOn.difference_apply
      (cov.isCovariantDerivativeOn (s := Set.univ))
      (cov'.isCovariantDerivativeOn (s := Set.univ))
      (x := x) (σ := X) (s := Set.univ) (by trivial)
      (by simpa [MDiffAtTangentField] using hX))

private lemma metric_difference_antisymm (cov cov' : CovariantDerivative I E TM)
    (hc : IsMetricCompatible g cov)
    (hc' : IsMetricCompatible g cov') {x : M}
    {Y Z : ∀ y : M, TM y} (hY : MDiffAtTangentField Y x)
    (hZ : MDiffAtTangentField Z x)
    (v : TM x) :
    g.inner x ((cov.difference cov') x (Y x) v) (Z x) =
      -g.inner x ((cov.difference cov') x (Z x) v) (Y x) := by
  have hcompat :
      g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v) =
        g.inner x (cov' Y x v) (Z x) + g.inner x (Y x) (cov' Z x v) :=
    (hc hY hZ v).symm.trans (hc' hY hZ v)
  have hYdiff :
      (cov.difference cov') x (Y x) v = cov Y x v - cov' Y x v := by
    simpa using congrArg (fun L => L v) (difference_apply_tangent cov cov' hY)
  have hZdiff :
      (cov.difference cov') x (Z x) v = cov Z x v - cov' Z x v := by
    simpa using congrArg (fun L => L v) (difference_apply_tangent cov cov' hZ)
  rw [hYdiff, hZdiff]
  rw [g.inner_symm x (Y x) (cov Z x v),
    g.inner_symm x (Y x) (cov' Z x v)] at hcompat
  simp [map_sub]
  linarith

private lemma difference_symmetric_of_torsion_eq_zero (cov cov' : CovariantDerivative I E TM)
    (ht : cov.torsion = 0) (ht' : cov'.torsion = 0) (x : M) (v w : TM x) :
    (cov.difference cov') x w v = (cov.difference cov') x v w := by
  rw [CovariantDerivative.torsion_eq_zero_iff] at ht
  rw [CovariantDerivative.torsion_eq_zero_iff] at ht'
  let X : ∀ y : M, TM y := extend E v
  let Y : ∀ y : M, TM y := extend E w
  have hX : MDiffAtTangentField X x := by
    simpa [MDiffAtTangentField, X] using (mdifferentiableAt_extend ..)
  have hY : MDiffAtTangentField Y x := by
    simpa [MDiffAtTangentField, Y] using (mdifferentiableAt_extend ..)
  have hcov_torsion := ht (by simpa [MDiffAtTangentField] using hX)
    (by simpa [MDiffAtTangentField] using hY)
  have hcov'_torsion := ht' (by simpa [MDiffAtTangentField] using hX)
    (by simpa [MDiffAtTangentField] using hY)
  have hXx : X x = v := by simp [X]
  have hYx : Y x = w := by simp [Y]
  have hdiffY :
      (cov.difference cov') x w v = cov Y x v - cov' Y x v := by
    simpa [hXx, hYx] using
      congrArg (fun L => L v) (difference_apply_tangent cov cov' hY)
  have hdiffX :
      (cov.difference cov') x v w = cov X x w - cov' X x w := by
    simpa [hXx, hYx] using
      congrArg (fun L => L w) (difference_apply_tangent cov cov' hX)
  rw [hdiffY, hdiffX]
  have hsub :
      (cov Y x v - cov X x w) - (cov' Y x v - cov' X x w) = 0 := by
    simpa [hXx, hYx] using congrArg₂ (fun a b => a - b) hcov_torsion hcov'_torsion
  linear_combination (norm := module) hsub

private lemma difference_inner_zero (cov cov' : CovariantDerivative I E TM)
    (hc : IsMetricCompatible g cov)
    (hc' : IsMetricCompatible g cov') (ht : cov.torsion = 0) (ht' : cov'.torsion = 0)
    {x : M} {Y : ∀ y : M, TM y} (hY : MDiffAtTangentField Y x) (v z : TM x) :
    g.inner x ((cov.difference cov') x (Y x) v) z = 0 := by
  let V : ∀ y : M, TM y := extend E v
  let Z : ∀ y : M, TM y := extend E z
  have hV : MDiffAtTangentField V x := by
    simpa [MDiffAtTangentField, V] using (mdifferentiableAt_extend ..)
  have hZ : MDiffAtTangentField Z x := by
    simpa [MDiffAtTangentField, Z] using (mdifferentiableAt_extend ..)
  have hVx : V x = v := by simp [V]
  have hZx : Z x = z := by simp [Z]
  have s1 :
      g.inner x ((cov.difference cov') x (Y x) v) z =
        -g.inner x ((cov.difference cov') x (Z x) v) (Y x) := by
    simpa [hZx] using
      metric_difference_antisymm g cov cov' hc hc' hY hZ v
  have s2 :
      g.inner x ((cov.difference cov') x (Z x) v) (Y x) =
        g.inner x ((cov.difference cov') x (V x) z) (Y x) := by
    rw [hVx, hZx]
    rw [difference_symmetric_of_torsion_eq_zero cov cov' ht ht' x v z]
  have s3 :
      g.inner x ((cov.difference cov') x (V x) z) (Y x) =
        -g.inner x ((cov.difference cov') x (Y x) z) (V x) := by
    exact metric_difference_antisymm g cov cov' hc hc' hV hY z
  have s4 :
      g.inner x ((cov.difference cov') x (Y x) z) (V x) =
        g.inner x ((cov.difference cov') x (Z x) (Y x)) (V x) := by
    rw [hZx]
    rw [difference_symmetric_of_torsion_eq_zero cov cov' ht ht' x z (Y x)]
  have s5 :
      g.inner x ((cov.difference cov') x (Z x) (Y x)) (V x) =
        -g.inner x ((cov.difference cov') x (V x) (Y x)) (Z x) := by
    exact metric_difference_antisymm g cov cov' hc hc' hZ hV (Y x)
  have s6 :
      g.inner x ((cov.difference cov') x (V x) (Y x)) (Z x) =
        g.inner x ((cov.difference cov') x (Y x) v) z := by
    rw [hVx, hZx]
    rw [difference_symmetric_of_torsion_eq_zero cov cov' ht ht' x v (Y x)]
  linarith

end LeviCivita

/--
Uniqueness of the Levi-Civita connection, in pointwise form on vector fields
that are differentiable at the point.  The conclusion is equality of the two
connection values as maps from directions to the tangent fiber at that point.
-/
theorem levi_civita_unique (g : ClosedSmoothRiemannianMetric n M)
    {cov cov' : CovariantDerivative (closedSmoothModelWithCorners n) (ClosedSmoothModel n)
      (TangentSpace (closedSmoothModelWithCorners n) : M → Type _)}
    (hc : IsMetricCompatible g cov) (hc' : IsMetricCompatible g cov')
    (ht : cov.torsion = 0) (ht' : cov'.torsion = 0)
    {x : M} {X : ∀ y : M, TangentSpace (closedSmoothModelWithCorners n) y}
    (hX : MDiffAtTangentField X x) :
    cov X x = cov' X x := by
  ext v
  have hdiff :
      (cov.difference cov') x (X x) v = cov X x v - cov' X x v := by
    simpa using
      congrArg (fun L => L v) (LeviCivita.difference_apply_tangent cov cov' hX)
  have hzero :
      (cov.difference cov') x (X x) v = 0 := by
    by_contra hne
    have hdiag := LeviCivita.difference_inner_zero g cov cov'
      hc hc' ht ht' hX v ((cov.difference cov') x (X x) v)
    have hpos := g.inner_pos x hne
    rw [hdiag] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  rw [hdiff] at hzero
  exact sub_eq_zero.mp hzero

end Poincare
