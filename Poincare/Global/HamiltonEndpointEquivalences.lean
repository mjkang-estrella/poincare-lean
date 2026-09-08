import Poincare.Global.HamiltonFrontStatements
import Poincare.Global.PinchedLimitPositiveEinstein
import Poincare.Global.HamiltonPoincareReduction

/-!
# Universal Hamilton convergence is universal positive Einstein existence

The two landed per-manifold implications compose to the literal universal
equivalence.  Consequently the manifold-level Poincare conjecture also follows
from universal positive Einstein existence alone.  See
`harness/reports/hamilton-front-decomposition_done.md`, section 4, task 2.
-/

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
universe u
namespace Poincare

/-- The universal Hamilton endpoint and universal positive Einstein existence are equivalent. -/
theorem universalHamiltonConvergence_iff_universalPositiveEinstein :
    UniversalHamiltonConvergenceStatement.{u} ↔ UniversalPositiveEinsteinStatement.{u} := by
  constructor
  · intro h N _ _ _ _ _ _ _ _
    exact positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core
      ((hamiltonConvergencePinchedLimit3_iff_core (M := N)).mp (h N))
  · intro h N _ _ _ _ _ _ _ _
    exact hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3 (h N)

/-- The manifold-level Poincare conjecture from universal positive Einstein existence. -/
theorem poincareConjecture_of_universalPositiveEinstein
    (h : UniversalPositiveEinsteinStatement.{u}) : PoincareConjecture.{u} :=
  poincareConjecture_of_universalHamiltonConvergence
    (universalHamiltonConvergence_iff_universalPositiveEinstein.mpr h)

end Poincare
