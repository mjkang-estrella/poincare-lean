import Mathlib.Topology.Subpath
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}
example (γ : Path x x) {N : ℕ} (t : Fin (N + 1) → unitInterval)
    {start : Fin N} (hstart0 : start.val ≠ 0) :
    let A : ℕ := start.val - 1
    let B : ℕ := N - start.val - 1
    let u : Fin (A + 2) → unitInterval := fun i => t ⟨i.val, by omega⟩
    let v : Fin (B + 2) → unitInterval := fun i => t ⟨start.val + i.val, by omega⟩
    ∀ (hstartEq : γ (t 0) = γ (u 0))
      (hendEq : γ (t (Fin.last N)) = γ (v (Fin.last (B + 1)))),
      (γ.subpath (u 0) (v (Fin.last (B + 1)))).cast hstartEq hendEq =
        γ.subpath (t 0) (t (Fin.last N)) := by
  dsimp only
  intro hstartEq hendEq
  apply Path.ext
  funext s
  change (γ.subpath (t 0) (t ⟨start.val + (N - start.val - 1 + 1), by omega⟩)) s =
    (γ.subpath (t 0) (t (Fin.last N))) s
  have hi : (⟨start.val + (N - start.val - 1 + 1), by omega⟩ : Fin (N + 1)) = Fin.last N := by
    apply Fin.ext
    change start.val + (N - start.val - 1 + 1) = N
    omega
  rw [hi]
example (γ : Path x x) {N : ℕ} (t : Fin (N + 1) → unitInterval)
    {start : Fin N} (hstart0 : start.val ≠ 0) :
    let A : ℕ := start.val - 1
    let B : ℕ := N - start.val - 1
    let u : Fin (A + 2) → unitInterval := fun i => t ⟨i.val, by omega⟩
    let v : Fin (B + 2) → unitInterval := fun i => t ⟨start.val + i.val, by omega⟩
    ∀ (hcloseLocal : γ (v (Fin.last (B + 1))) = γ (u 0))
      (hclose : γ (t (Fin.last N)) = γ (t 0))
      (hstartEq : γ (t 0) = γ (u 0))
      (hendEq : γ (t (Fin.last N)) = γ (v (Fin.last (B + 1)))),
      (((Path.refl (γ (u 0))).cast rfl hcloseLocal).cast hstartEq hendEq) =
        ((Path.refl (γ (t 0))).cast rfl hclose) := by
  dsimp only
  intro hcloseLocal hclose hstartEq hendEq
  apply Path.ext
  funext s
  rfl
example (γ : Path x x) {y z : X} (hx : y = x) (hy : z = x)
    (h : (γ.cast hx hy).Homotopic ((Path.refl x).cast hx hy)) :
    γ.Homotopic (Path.refl x) := by
  have h' := h.pathCast hx.symm hy.symm
  convert h' using 1 <;> apply Path.ext <;> funext s <;> rfl
