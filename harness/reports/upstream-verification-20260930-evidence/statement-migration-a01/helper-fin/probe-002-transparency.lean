import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Product
import Mathlib.Analysis.Convex.Contractible
set_option backward.isDefEq.respectTransparency false
universe u

example {Y : Type u} [TopologicalSpace Y] {L R : ℕ} {x₀ : Y}
    (tailPts : Fin (L + R + 1) → Y)
    (hclose : tailPts (Fin.last (L + R)) = x₀) :
    let uPts : Fin (R + 1) → Y := fun i => tailPts ⟨L + i.val, by omega⟩
    uPts (Fin.last R) = x₀ := by
  dsimp only
  let uPts : Fin (R + 1) → Y := fun i => tailPts ⟨L + i.val, by omega⟩
  change uPts (Fin.last R) = x₀
  simpa [uPts] using hclose

example {Y : Type u} [TopologicalSpace Y] {N : ℕ}
    (tailPts : Fin (N + 1) → Y) (start : Fin N) (V : Set Y)
    (h : tailPts start.castSucc ∈ V) : tailPts ⟨start.val, by omega⟩ ∈ V := by
  simpa using h

example {X : Type u} [TopologicalSpace X] {U : Set X} {a b : X}
    (γ : Path a b) (hU : IsOpen U) : IsOpen {t : unitInterval | γ t ∈ U} := by
  simpa using hU.preimage γ.continuous

example {X : Type u} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (z : X) (hz : z ∈ Set.range (p.trans q)) :
    z ∈ Set.range p ∪ Set.range q := by
  simpa [Path.trans_range] using hz
