import Poincare.Global.CartanSuppliedUnitRecognition
import Poincare.Global.HamiltonFrontStatements
import Poincare.Global.TopologicalCompletionBridge

/-!
# The Poincare conjecture from universal Hamilton convergence

With unit-curvature sphere recognition now a theorem on every closed simply
connected smooth 3-manifold, the manifold-level Poincare conjecture reduces to
the single registered Hamilton endpoint `UniversalHamiltonConvergenceStatement`.
That endpoint remains an open obligation of the `hamilton-front` mission.
The frozen topological statement then needs exactly one more premise, the
existence-shaped smoothability of compact simply connected topological
3-manifolds, which is also open.
-/

set_option autoImplicit false
namespace Poincare
universe u

/-- The manifold-level Poincare conjecture follows from the universal Hamilton
pinched-limit endpoint alone. -/
theorem poincareConjecture_of_universalHamiltonConvergence
    (hHamilton : UniversalHamiltonConvergenceStatement.{u}) : PoincareConjecture.{u} :=
  CartanSuppliedUnitRecognition.poincare_of_hamiltonConvergence hHamilton

/-- The frozen topological Poincare statement from existence-shaped
smoothability and universal Hamilton convergence.  Both premises remain open. -/
theorem poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence
    (smoothable : ExistsSmoothabilitySmoothManifoldStatement.{u})
    (hHamilton : UniversalHamiltonConvergenceStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture smoothable
    (poincareConjecture_of_universalHamiltonConvergence hHamilton)

end Poincare
