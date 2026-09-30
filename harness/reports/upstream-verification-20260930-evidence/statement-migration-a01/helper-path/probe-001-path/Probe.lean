import Mathlib.Topology.Subpath
import Mathlib.Data.Set.Countable
universe u
namespace Probe
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
        rw [Path.trans_range]
        exact hz'
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
          rw [Path.trans_range]
          exact hy'
        have hseg := ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hprefix k'
        simp only [hkcast] at hseg
        exact hseg hz


theorem countable_subtype {Y : Type u} [TopologicalSpace Y] {s q : Set Y}
    (hs : s.Countable) :
    let t : Set q := {p : q | (p : Y) ∈ s}
    t.Countable := by
  intro t
  change (Subtype.val ⁻¹' s).Countable
  exact hs.preimage Subtype.val_injective
end Probe
