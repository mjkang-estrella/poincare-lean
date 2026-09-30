import Poincare.Statement
open scoped Manifold ContDiff
universe u
example : Poincare.PoincareConjectureStatement.{u} =
  (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))) := rfl
#check Poincare.PoincareConjectureStatement.{u}
#print axioms Poincare.poincareConjectureStatement_eq
