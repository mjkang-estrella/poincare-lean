import Mathlib.Geometry.Manifold.PoincareConjecture
import Poincare.Global.Statement

/-!
# Alignment with Mathlib's Poincare statement

This file restates Mathlib's statement-only 3-dimensional topological
Poincare conjecture stub and records the formal relation to the project's
global smooth statement.
-/

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Mathlib's statement-only three-dimensional Poincare `proof_wanted` body,
restated because `proof_wanted` declarations are not available as importable
proof terms.  This definition deliberately avoids depending on that upstream
placeholder declaration.
-/
def MathlibPoincareStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (M ≃ₜ
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) (1 : ℝ))

/-
The two statements are not definitionally or logically identical at the
hypothesis level.  Mathlib's topological statement assumes only `T2Space`,
`ChartedSpace ℝ³`, `SimplyConnectedSpace`, and `CompactSpace`.  The local
`PoincareConjecture` in `Poincare.Global.Statement` additionally assumes
`SecondCountableTopology`, smooth compatibility via `IsManifold (𝓡 3) ∞`, and
`ConnectedSpace`.  `SimplyConnectedSpace` supplies connectedness in Mathlib,
but `ChartedSpace ℝ³ M` alone does not supply the smooth manifold hypothesis.
Accordingly this file proves only the implication from Mathlib's broader
topological statement to the local smooth-hypothesis statement, rather than
forcing an iff by weakening either side.
-/

/--
Mathlib's topological 3-dimensional statement implies the project's frozen
global statement, since the latter asks only for manifolds satisfying extra
local hypotheses.
-/
theorem poincareConjecture_of_mathlibPoincareStatement
    (h : MathlibPoincareStatement.{u}) :
    PoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _ _
  exact h M

end Poincare
