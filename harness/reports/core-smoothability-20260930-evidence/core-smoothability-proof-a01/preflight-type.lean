import Poincare.Global.SmoothabilityExistenceStatement
open scoped Manifold ContDiff
universe u
example : Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u} = (∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M] [CompactSpace M], ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M, letI := C; IsManifold (𝓡 3) ((⊤ : ENat) : WithTop ENat) M) := rfl
