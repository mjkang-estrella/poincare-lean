import Poincare.Global.HamiltonChartDensityLocalDomination

/-!
# Reduced reaction core, registry names

Unprimed aliases of the reduced reaction core statement and its endpoint
reduction from `HamiltonChartDensityLocalDomination`, for the mission
registry, whose Lean exporter does not resolve primed names.
-/

set_option autoImplicit false
namespace Poincare
universe u v

/-- The reduced reaction core (local density domination derived), universal form. -/
def UniversalHamiltonReactionCoreReducedStatement : Prop :=
  HamiltonChartDensityLocalDomination.UniversalHamiltonReactionCoreStatement'.{u, v}

/-- The reduced reaction core discharges universal Hamilton convergence. -/
theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreReduced
    (h : UniversalHamiltonReactionCoreReducedStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} :=
  HamiltonChartDensityLocalDomination.universalHamiltonConvergence_of_universalHamiltonReactionCore' h

end Poincare
