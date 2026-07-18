import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching

/-!
# Ricci quotient bound from a global eigenvalue floor

Hamilton's pointwise eigenvalue-floor inequality already bounds the normalized
Ricci quotient.  This module lifts that fact to the global slice predicates
used by the explicit normalized-reaction estimate and records positivity of
the resulting quadratic coefficient.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The quotient coefficient associated to an `epsilon R` Ricci-eigenvalue
floor is strictly positive for every real `epsilon`. -/
theorem pinchingQuotientCoefficient_pos (epsilon : ℝ) :
    0 < 1 - 4 * epsilon + 6 * epsilon ^ 2 := by
  nlinarith [sq_nonneg (3 * epsilon - 1)]

/-- A positive-scalar metric with a global `epsilon R` Ricci-eigenvalue floor
has the corresponding global normalized Ricci quotient bound. -/
theorem
    ClosedSmoothRiemannianMetric.globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {epsilon : ℝ}
    (hScalarPos : ∀ x : M, 0 < g.scalarAt x)
    (hFloor : GlobalRicciEigenvalueFloor3 g epsilon) :
    GlobalPinchingQuotientBound3 g
      (1 - 4 * epsilon + 6 * epsilon ^ 2) := by
  intro x
  exact g.pinchingQuotientAt_le_of_eigenvalue_pinched
    rfl (hScalarPos x) (hFloor x)

end Poincare
