import Mathlib.Topology.Subpath
universe u
example {Y : Type u} [TopologicalSpace Y] {A B C : ℕ} {x₀ : Y}
    (tailPts : Fin (A + (B + 1) + C + 1) → Y)
    (tailSegs : (k : Fin (A + (B + 1) + C)) → Path (tailPts k.castSucc) (tailPts k.succ))
    (p : Path x₀ (tailPts 0)) : True := by
  let prefixPts : Fin (A + 1) → Y := fun i => tailPts ⟨i.val, by omega⟩
  let prefixSegs : (k : Fin A) → Path (prefixPts k.castSucc) (prefixPts k.succ) := fun k => tailSegs ⟨k.val, by omega⟩
  let oppPts : Fin (B + 1) → Y := fun i => tailPts ⟨A + i.val, by omega⟩
  let oppSegs : (k : Fin B) → Path (oppPts k.castSucc) (oppPts k.succ) := fun k => tailSegs ⟨A + k.val, by omega⟩
  let returnPts : Fin (1 + 1) → Y := fun i => tailPts ⟨A + (B + i.val), by omega⟩
  let returnSegs : (k : Fin 1) → Path (returnPts k.castSucc) (returnPts k.succ) := fun k => tailSegs ⟨A + (B + k.val), by omega⟩
  let afterPts : Fin (C + 1) → Y := fun i => tailPts ⟨A + (B + 1) + i.val, by omega⟩
  let afterSegs : (k : Fin C) → Path (afterPts k.castSucc) (afterPts k.succ) := fun k => tailSegs ⟨A + (B + 1) + k.val, by omega⟩
  let P := Path.concat prefixPts prefixSegs
  let O := Path.concat oppPts oppSegs
  let R := Path.concat returnPts returnSegs
  let T := Path.concat afterPts afterSegs
  have hjoin : oppPts 0 = prefixPts (Fin.last A) := by rfl
  have hCastEq :
      ((((p.trans P).trans (O.cast hjoin.symm rfl)).trans R).trans T) =
      ((((p.trans P).trans O).trans R).trans T) := by
    apply Path.ext
    rfl
  have hCastEq' : O.cast hjoin.symm rfl = O := by
    apply Path.ext
    rfl
  have hTRange : Set.range T ⊆ Set.range ((((p.trans P).trans O).trans R).trans T) := by
    intro z hz
    simp only [P, O, R, T, prefixPts, oppPts, returnPts, afterPts, Path.trans_range]
    exact Or.inr hz
  trivial
