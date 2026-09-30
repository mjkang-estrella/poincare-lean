import Mathlib.Topology.Subpath
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}
example (γ : Path x x) {N : ℕ} (t : Fin (N+1) → unitInterval)
    (h0 : t 0 = 0) (h1 : t (Fin.last N) = 1)
    (h : (γ.cast (by simp [h0]) (by simp [h1]) : Path (γ (t 0)) (γ (t (Fin.last N)))).Homotopic
      ((Path.refl x).cast (by simp [h0]) (by simp [h1]))) :
    γ.Homotopic (Path.refl x) := by
  have h' := h.pathCast
    (show x = γ (t 0) from by simp [h0])
    (show x = γ (t (Fin.last N)) from by simp [h1])
  convert h' using 1 <;> apply Path.ext <;> funext s <;> rfl
example (γ : Path x x) {N : ℕ} (t : Fin (N+1) → unitInterval)
    (h0 : t 0 = 0) (h1 : t (Fin.last N) = 1)
    (h : (γ.cast (by simp [h0]) (by simp [h1]) : Path (γ (t 0)) (γ (t (Fin.last N)))).Homotopic
      ((Path.refl x).cast (by simp [h0]) (by simp [h1]))) :
    γ.Homotopic (Path.refl x) := by
  have h' := h.pathCast (by simp [h0]) (by simp [h1])
  convert h' using 1 <;> apply Path.ext <;> funext s <;> rfl
