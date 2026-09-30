import Mathlib.Topology.Subpath
universe u
namespace Probe
set_option backward.isDefEq.respectTransparency false
theorem runBlockSource
    {Y : Type u} [TopologicalSpace Y] {x : Y} (γ : Path x x)
    {N : ℕ} (t : Fin (N + 1) → unitInterval) (S : Set Y)
    {start stop : Fin N}
    (hrun : ∀ j : Fin N, start.val ≤ j.val → j.val < stop.val →
      Set.range (γ.subpath (t j.castSucc) (t j.succ)) ⊆
        S) :
    let block : Fin ((stop.val - start.val) + 1) → unitInterval := fun i =>
      t ⟨start.val + i.val,
        by
          have hstop : stop.val < N := stop.isLt
          have hi : i.val < (stop.val - start.val) + 1 := i.isLt
          omega⟩
    ∀ k : Fin (stop.val - start.val),
      Set.range (γ.subpath (block k.castSucc) (block k.succ)) ⊆
        S := by
  intro block k
  let j : Fin N := ⟨start.val + k.val,
    by
      have hstop : stop.val < N := stop.isLt
      have hk : k.val < stop.val - start.val := k.isLt
      omega⟩
  have hjle : start.val ≤ j.val := by
    change start.val ≤ start.val + k.val
    omega
  have hjlt : j.val < stop.val := by
    change start.val + k.val < stop.val
    have hk : k.val < stop.val - start.val := k.isLt
    omega
  simpa [block, j] using hrun j hjle hjlt

theorem runBlockSource_assoc
    {Y : Type u} [TopologicalSpace Y] {x : Y} (γ : Path x x)
    {N : ℕ} (t : Fin (N + 1) → unitInterval) (S : Set Y)
    {start stop : Fin N}
    (hrun : ∀ j : Fin N, start.val ≤ j.val → j.val < stop.val →
      Set.range (γ.subpath (t j.castSucc) (t j.succ)) ⊆
        S) :
    let block : Fin ((stop.val - start.val) + 1) → unitInterval := fun i =>
      t ⟨start.val + i.val,
        by
          have hstop : stop.val < N := stop.isLt
          have hi : i.val < (stop.val - start.val) + 1 := i.isLt
          omega⟩
    ∀ k : Fin (stop.val - start.val),
      Set.range (γ.subpath (block k.castSucc) (block k.succ)) ⊆
        S := by
  intro block k
  let j : Fin N := ⟨start.val + k.val,
    by
      have hstop : stop.val < N := stop.isLt
      have hk : k.val < stop.val - start.val := k.isLt
      omega⟩
  have hjle : start.val ≤ j.val := by
    change start.val ≤ start.val + k.val
    omega
  have hjlt : j.val < stop.val := by
    change start.val + k.val < stop.val
    have hk : k.val < stop.val - start.val := k.isLt
    omega
  simpa [block, j, Nat.add_assoc] using hrun j hjle hjlt

end Probe
