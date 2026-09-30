import Mathlib.Topology.Subpath
universe u
namespace Probe
set_option backward.isDefEq.respectTransparency false
theorem path_concat_segment_range_subset_of_concat_range
    {Y : Type u} [TopologicalSpace Y] {S : Set Y} {N : ℕ}
    (p : Fin (N + 1) → Y)
    (F : (k : Fin N) → Path (p k.castSucc) (p k.succ))
    (hconcat : Set.range (Path.concat p F) ⊆ S) :
    ∀ k : Fin N, Set.range (F k) ⊆ S := by
  induction N with
  | zero =>
      intro k
      exact Fin.elim0 k
  | succ N ih =>
      intro k z hz
      by_cases hk : k = Fin.last N
      · subst k
        apply hconcat
        rw [Path.concat_succ]
        have hz' :
            z ∈ Set.range (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) ∪
              Set.range (F (Fin.last N)) := Or.inr hz
        simpa [Path.trans_range] using hz'
      · let k' : Fin N := ⟨k.val, by
          have hklt := k.isLt
          have hne : k.val ≠ N := by
            intro hval
            apply hk
            ext
            exact hval
          omega⟩
        have hkcast : k'.castSucc = k := by
          ext
          rfl
        have hprefix :
            Set.range (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) ⊆ S := by
          intro y hy
          apply hconcat
          rw [Path.concat_succ]
          have hy' :
              y ∈ Set.range (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) ∪
                Set.range (F (Fin.last N)) := Or.inl hy
          simpa [Path.trans_range] using hy'
        have hseg := ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hprefix k'
        change Set.range (F k'.castSucc) ⊆ S at hseg
        rw [hkcast] at hseg
        exact hseg hz

theorem path_concat_segment_range_subset_of_concat_range_simpOnly
    {Y : Type u} [TopologicalSpace Y] {S : Set Y} {N : ℕ}
    (p : Fin (N + 1) → Y)
    (F : (k : Fin N) → Path (p k.castSucc) (p k.succ))
    (hconcat : Set.range (Path.concat p F) ⊆ S) :
    ∀ k : Fin N, Set.range (F k) ⊆ S := by
  induction N with
  | zero =>
      intro k
      exact Fin.elim0 k
  | succ N ih =>
      intro k z hz
      by_cases hk : k = Fin.last N
      · subst k
        apply hconcat
        rw [Path.concat_succ]
        have hz' :
            z ∈ Set.range (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) ∪
              Set.range (F (Fin.last N)) := Or.inr hz
        simpa [Path.trans_range] using hz'
      · let k' : Fin N := ⟨k.val, by
          have hklt := k.isLt
          have hne : k.val ≠ N := by
            intro hval
            apply hk
            ext
            exact hval
          omega⟩
        have hkcast : k'.castSucc = k := by
          ext
          rfl
        have hprefix :
            Set.range (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) ⊆ S := by
          intro y hy
          apply hconcat
          rw [Path.concat_succ]
          have hy' :
              y ∈ Set.range (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) ∪
                Set.range (F (Fin.last N)) := Or.inl hy
          simpa [Path.trans_range] using hy'
        have hseg := ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hprefix k'
        exact hseg (by simpa only [hkcast] using hz)

end Probe
