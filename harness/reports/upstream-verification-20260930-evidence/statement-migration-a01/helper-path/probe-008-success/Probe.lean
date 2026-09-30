import Mathlib.Geometry.Manifold.PoincareConjecture
import Mathlib.Topology.Subpath
import Mathlib.Data.Set.Countable
universe u
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
namespace PathProof
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


theorem countable_subtype {Y : Type u} [TopologicalSpace Y] {s q : Set Y}
    (hs : s.Countable) :
    let t : Set q := {p : q | (p : Y) ∈ s}
    t.Countable := by
  intro t
  change (Subtype.val ⁻¹' s).Countable
  exact hs.preimage Subtype.val_injective
end PathProof
namespace RunBlock
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

end RunBlock
namespace ChartDiff
abbrev E := EuclideanSpace ℝ (Fin 3)
variable {X : Type} [TopologicalSpace X] [Nonempty X]
variable (q : E)
variable [Nonempty ({q}ᶜ : Set E)]

theorem targetEmbedding : Topology.IsOpenEmbedding (Subtype.val : ({q}ᶜ : Set E) → E) :=
  isOpen_compl_singleton.isOpenEmbedding_subtypeVal

theorem sourceEmbedding (e : X ≃ₜ ({q}ᶜ : Set E)) :
    Topology.IsOpenEmbedding (fun p : X => (e p : E)) := by
  exact (targetEmbedding q).comp e.isOpenEmbedding

@[implicit_reducible]
noncomputable def sourceCharts (e : X ≃ₜ ({q}ᶜ : Set E)) : ChartedSpace E X :=
  (sourceEmbedding q e).singletonChartedSpace
@[implicit_reducible]
noncomputable def targetCharts : ChartedSpace E ({q}ᶜ : Set E) :=
  (targetEmbedding q).singletonChartedSpace

noncomputable def diffeo_exact (e : X ≃ₜ ({q}ᶜ : Set E)) :
    letI : ChartedSpace E X := sourceCharts q e
    letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ ({q}ᶜ : Set E) := by
  letI : ChartedSpace E X := sourceCharts q e
  letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
  let hsource := sourceEmbedding q e
  let htarget := targetEmbedding q
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := htarget) (by
          exact contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) hsource)
      contMDiff_invFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := hsource)
          ((contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) htarget).congr
            (fun x => by
              exact congrArg Subtype.val (e.apply_symm_apply x))) }

end ChartDiff
