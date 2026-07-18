import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UnitInterval

/-!
# Continuous interpolation of finitely many unit-interval nodes

This file constructs an endpoint-preserving continuous self-map of the unit
interval that realizes prescribed values at the uniformly spaced nodes
`j / N`.  The construction interpolates the values by a real Lagrange
polynomial and then projects its values back to `[0, 1]`.

The interpolant is not asserted to be monotone.  This is nevertheless enough
for `Path.reparam`: continuity and the two endpoint equations are its only
hypotheses, while projection leaves every prescribed unit-interval node fixed.
-/

noncomputable section

open Set
open scoped Polynomial

namespace Poincare.FiniteUnitIntervalInterpolation

/-- The real value `j / N` underlying the `j`th uniform subdivision node. -/
def uniformNodeValue (N : ℕ) (j : Fin (N + 1)) : ℝ :=
  (j.val : ℝ) / (N : ℝ)

/-- The `j`th node of the uniform subdivision of the unit interval into `N` pieces. -/
def uniformNode (N : ℕ) (j : Fin (N + 1)) : unitInterval :=
  ⟨uniformNodeValue N j,
    unitInterval.div_mem (Nat.cast_nonneg j.val) (Nat.cast_nonneg N) (by
      exact_mod_cast Nat.le_of_lt_succ j.isLt)⟩

/-- Uniform subdivision nodes are distinct when there is at least one piece. -/
theorem uniformNodeValue_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (uniformNodeValue N) := by
  intro i j hij
  change (i.val : ℝ) / (N : ℝ) = (j.val : ℝ) / (N : ℝ) at hij
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have hij' : (i.val : ℝ) = (j.val : ℝ) :=
    (div_left_inj' hN0).mp hij
  apply Fin.ext
  exact_mod_cast hij'

@[simp]
theorem uniformNode_zero (N : ℕ) : uniformNode N 0 = 0 := by
  apply Subtype.ext
  simp [uniformNode, uniformNodeValue]

@[simp]
theorem uniformNode_last {N : ℕ} (hN : 0 < N) :
    uniformNode N (Fin.last N) = 1 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  apply Subtype.ext
  simp [uniformNode, uniformNodeValue, hN0]

/-- The real Lagrange polynomial through the prescribed unit-interval values. -/
def interpolationPolynomial (N : ℕ) (a : Fin (N + 1) → unitInterval) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (uniformNodeValue N) (fun j ↦ (a j : ℝ))

/-- The interpolation polynomial takes the prescribed value at every uniform node. -/
theorem interpolationPolynomial_eval_uniformNode
    {N : ℕ} (hN : 0 < N) (a : Fin (N + 1) → unitInterval) (j : Fin (N + 1)) :
    (interpolationPolynomial N a).eval (uniformNodeValue N j) = (a j : ℝ) := by
  apply Lagrange.eval_interpolate_at_node (fun j ↦ (a j : ℝ))
      (uniformNodeValue_injective hN).injOn
  simp

/--
The continuous unit-interval interpolant.  Projection back to `[0, 1]` does
not change any nodal value, because all prescribed values already lie there.
-/
def interpolation (N : ℕ) (a : Fin (N + 1) → unitInterval) :
    unitInterval → unitInterval := fun t ↦
  Set.projIcc 0 1 zero_le_one ((interpolationPolynomial N a).eval (t : ℝ))

/-- The projected polynomial interpolant is continuous. -/
theorem continuous_interpolation (N : ℕ) (a : Fin (N + 1) → unitInterval) :
    Continuous (interpolation N a) := by
  exact continuous_projIcc.comp
    ((interpolationPolynomial N a).continuous.comp continuous_subtype_val)

/-- The projected polynomial interpolant realizes every prescribed node exactly. -/
@[simp]
theorem interpolation_uniformNode
    {N : ℕ} (hN : 0 < N) (a : Fin (N + 1) → unitInterval) (j : Fin (N + 1)) :
    interpolation N a (uniformNode N j) = a j := by
  change Set.projIcc 0 1 zero_le_one
      ((interpolationPolynomial N a).eval (uniformNodeValue N j)) = a j
  rw [interpolationPolynomial_eval_uniformNode hN]
  exact Set.projIcc_val zero_le_one (a j)

/-- If the first prescribed value is `0`, then so is the interpolant's source. -/
theorem interpolation_zero
    {N : ℕ} (hN : 0 < N) (a : Fin (N + 1) → unitInterval) (ha0 : a 0 = 0) :
    interpolation N a 0 = 0 := by
  calc
    interpolation N a 0 = interpolation N a (uniformNode N 0) := by
      rw [uniformNode_zero]
    _ = a 0 := interpolation_uniformNode hN a 0
    _ = 0 := ha0

/-- If the last prescribed value is `1`, then so is the interpolant's target. -/
theorem interpolation_one
    {N : ℕ} (hN : 0 < N) (a : Fin (N + 1) → unitInterval)
    (ha1 : a (Fin.last N) = 1) : interpolation N a 1 = 1 := by
  calc
    interpolation N a 1 = interpolation N a (uniformNode N (Fin.last N)) := by
      rw [uniformNode_last hN]
    _ = a (Fin.last N) := interpolation_uniformNode hN a (Fin.last N)
    _ = 1 := ha1

/--
Any finite unit-interval data with prescribed endpoints admits a continuous,
endpoint-preserving interpolant through the uniformly spaced source nodes.
-/
theorem exists_continuous_endpoint_interpolation
    {N : ℕ} (hN : 0 < N) (a : Fin (N + 1) → unitInterval)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last N) = 1) :
    ∃ ψ : unitInterval → unitInterval,
      Continuous ψ ∧
        ψ 0 = 0 ∧
        ψ 1 = 1 ∧
        ∀ j : Fin (N + 1), ψ (uniformNode N j) = a j := by
  refine ⟨interpolation N a, continuous_interpolation N a,
    interpolation_zero hN a ha0, interpolation_one hN a ha1, ?_⟩
  exact interpolation_uniformNode hN a

/--
Convenience form for monotone nodal data.  The construction works for
arbitrary data, so the monotonicity assumption is intentionally not needed by
the proof.
-/
theorem exists_continuous_endpoint_interpolation_of_monotone
    {N : ℕ} (hN : 0 < N) (a : Fin (N + 1) → unitInterval) (_ha : Monotone a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last N) = 1) :
    ∃ ψ : unitInterval → unitInterval,
      Continuous ψ ∧
        ψ 0 = 0 ∧
        ψ 1 = 1 ∧
        ∀ j : Fin (N + 1), ψ (uniformNode N j) = a j :=
  exists_continuous_endpoint_interpolation hN a ha0 ha1

end Poincare.FiniteUnitIntervalInterpolation
