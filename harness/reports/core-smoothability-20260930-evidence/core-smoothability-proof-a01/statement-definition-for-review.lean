import Poincare.Statement

open scoped Manifold ContDiff

universe u

namespace Poincare

/--
Existence-shaped smoothability for the canonical topological statement.

The input topological atlas is used only to state that `M` is a topological
three-manifold.  The conclusion selects a possibly different charted-space
instance carrying a smooth structure.  This is the mathematically correct
quantifier order: it does not require every ambient topological atlas to be a
smooth atlas.
-/
def ExistsSmoothabilitySmoothManifoldStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
        IsManifold (𝓡 3) ∞ M

/-- The existence-shaped smoothability interface exposes its quantifiers. -/
theorem existsSmoothabilitySmoothManifoldStatement_eq :
    ExistsSmoothabilitySmoothManifoldStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
            letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
            IsManifold (𝓡 3) ∞ M) :=
  rfl

end Poincare
