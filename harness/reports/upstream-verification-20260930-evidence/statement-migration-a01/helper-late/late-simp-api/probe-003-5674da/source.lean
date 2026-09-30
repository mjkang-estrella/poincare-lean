import Mathlib.Topology.Subpath
universe u
variable {X : Type u} [TopologicalSpace X] {a b b' : X}
example (q : Path a b) (hy : b' = b) (U : Set X) (hq : Set.range q ⊆ U) :
    Set.range (q.cast rfl hy) ⊆ U := by
  simpa [Path.cast] using hq
example (q : Path a b) (hy : b' = b) (U : Set X) (hq : Set.range q ⊆ U) :
    Set.range (q.cast rfl hy) ⊆ U := by
  simpa only [Path.cast_coe] using hq
example (γ : Path a b) (u v : unitInterval) (U : Set X)
    (h : Set.range (γ.subpath u v) ⊆ U) :
    Set.range (γ.subpath u v) ⊆ U := by
  simpa only using h
