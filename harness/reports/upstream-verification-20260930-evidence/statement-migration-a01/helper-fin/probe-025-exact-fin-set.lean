import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Product
import Mathlib.Analysis.Convex.Contractible
universe u

example {Y : Type u} [TopologicalSpace Y] {L R : ℕ} {x₀ : Y}
    (tailPts : Fin (L + R + 1) → Y)
    (hclose : tailPts (Fin.last (L + R)) = x₀) :
    let uPts : Fin (R + 1) → Y := fun i => tailPts ⟨L + i.val, by omega⟩
    uPts (Fin.last R) = x₀ := by
  dsimp only
  let uPts : Fin (R + 1) → Y := fun i => tailPts ⟨L + i.val, by omega⟩
  change uPts (Fin.last R) = x₀
  exact hclose

example {Y : Type u} [TopologicalSpace Y] {N : ℕ}
    (tailPts : Fin (N + 1) → Y) (start : Fin N) (V : Set Y)
    (h : tailPts start.castSucc ∈ V) : tailPts ⟨start.val, by omega⟩ ∈ V := by
  exact h

example {X : Type u} [TopologicalSpace X] {U : Set X} {a b : X}
    (γ : Path a b) (hU : IsOpen U) : IsOpen {t : unitInterval | γ t ∈ U} := by
  exact hU.preimage γ.continuous
