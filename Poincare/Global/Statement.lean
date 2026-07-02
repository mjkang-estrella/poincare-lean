import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Global Poincare conjecture statement

This file records the manifold-level statement of the three-dimensional
Poincare conjecture.  It intentionally contains only definitions and
compile-time sanity checks.
-/

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The manifold-level Poincare conjecture.

Every Hausdorff, second-countable, compact, connected, simply connected smooth
3-manifold is homeomorphic to the standard 3-sphere.
-/
def PoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))

example :
    PoincareConjecture.{u} ↔
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
          Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))) :=
  Iff.rfl

#check (inferInstance :
  ChartedSpace (EuclideanSpace ℝ (Fin 3))
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)))

#check (inferInstance :
  IsManifold (𝓡 3) ∞
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)))

end Poincare
