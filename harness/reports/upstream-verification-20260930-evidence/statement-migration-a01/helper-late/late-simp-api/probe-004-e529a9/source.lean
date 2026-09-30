import Mathlib.Topology.Subpath
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Type u} [TopologicalSpace X] {a b : X}
example (γ : Path a b) {N : ℕ} (t : Fin (N + 1) → unitInterval)
    {stop : Fin N} {L : ℕ} (hlen : L ≤ N - (stop.val + 1)) (U : Set X)
    (htail : ∀ k : Fin L,
      Set.range (γ.subpath
        (t (⟨stop.val + 1 + k.val, by omega⟩ : Fin N).castSucc)
        (t (⟨stop.val + 1 + k.val, by omega⟩ : Fin N).succ)) ⊆ U) :
    let tailPts : Fin (N - (stop.val + 1) + 1) → X := fun i =>
      γ (t ⟨stop.val + 1 + i.val, by omega⟩)
    let tailSegs : (k : Fin (N - (stop.val + 1))) →
      Path (tailPts k.castSucc) (tailPts k.succ) := fun k =>
        γ.subpath (t ⟨stop.val + 1 + k.val, by omega⟩)
          (t ⟨stop.val + 1 + (k.val + 1), by omega⟩)
    ∀ k : Fin L, Set.range (tailSegs ⟨k.val, by omega⟩) ⊆ U := by
  dsimp only
  intro k
  simpa only [Nat.add_assoc] using htail k
example (γ : Path a b) {N : ℕ} (t : Fin (N + 1) → unitInterval)
    {stop : Fin N} {L : ℕ} (hlen : L ≤ N - (stop.val + 1)) (U : Set X)
    (htail : ∀ k : Fin L,
      Set.range (γ.subpath
        (t (⟨stop.val + 1 + k.val, by omega⟩ : Fin N).castSucc)
        (t (⟨stop.val + 1 + k.val, by omega⟩ : Fin N).succ)) ⊆ U) :
    let tailPts : Fin (N - (stop.val + 1) + 1) → X := fun i =>
      γ (t ⟨stop.val + 1 + i.val, by omega⟩)
    let tailSegs : (k : Fin (N - (stop.val + 1))) →
      Path (tailPts k.castSucc) (tailPts k.succ) := fun k =>
        γ.subpath (t ⟨stop.val + 1 + k.val, by omega⟩)
          (t ⟨stop.val + 1 + (k.val + 1), by omega⟩)
    ∀ k : Fin L, Set.range (tailSegs ⟨k.val, by omega⟩) ⊆ U := by
  dsimp only
  intro k
  simpa [Nat.add_assoc] using htail k
