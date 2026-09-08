import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Finite triangulation interface

Foundation for a genuine triangulation-existence obligation, separated from
PL smoothing.  The compactness of a finite geometric complex is proved; the
existence statements are open and deliberately assert neither combinatorial
links, PL smoothability, nor sphere recognition.  See
`harness/reports/smoothability-bridge-survey_done.md`, sections 5.1 and 5.3.
-/

set_option autoImplicit false
universe u
namespace Poincare
namespace FiniteTriangulation

/-- The realization of a finite geometric simplicial complex is compact. -/
theorem isCompact_space_of_finite_faces (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hf : K.faces.Finite) : IsCompact K.space :=
  hf.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ

/-- A finite geometric complex of dimension at most three, in some Euclidean
space, whose realization is homeomorphic to `M`. -/
def FiniteTriangulationData3 (M : Type u) [TopologicalSpace M] : Prop :=
  ∃ n : ℕ, ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
    K.faces.Finite ∧ (∀ s ∈ K.faces, s.card ≤ 4) ∧ Nonempty (M ≃ₜ K.space)

/-- Open obligation: every compact Hausdorff simply connected topological
3-manifold admits a finite triangulation (Moise). -/
def FiniteTriangulationExistence3 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      FiniteTriangulationData3 M

end FiniteTriangulation
end Poincare
