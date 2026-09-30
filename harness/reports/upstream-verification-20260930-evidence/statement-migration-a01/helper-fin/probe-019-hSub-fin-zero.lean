import Mathlib.Topology.Subpath
universe u
example {Y : Type u} [TopologicalSpace Y] {N M : ℕ} {x₀ : Y}
    (γ : Path x₀ x₀)
    (t : Fin ((N + 1) + (M + 1) + 1) → unitInterval)
    (h0 : t 0 = 0) (h1 : t (Fin.last ((N + 1) + (M + 1))) = 1) : True := by
  let u : Fin (N + 2) → unitInterval := fun i => t ((i.castAdd (M + 1)).cast (by omega))
  let v : Fin (M + 2) → unitInterval := fun j => t ((j.natAdd (N + 1)).cast (by omega))
  have hu0 : u 0 = 0 := by
    simpa [u, Fin.cast, Fin.castAdd, Fin.castLE] using h0
  have hv1 : v (Fin.last (M + 1)) = 1 := by
    simpa [v] using h1
  have hclose : γ (t (Fin.last ((N + 1) + (M + 1)))) = γ (t 0) := by
    rw [h1, h0]
    exact γ.target.trans γ.source.symm
  have hlocalclose : γ (v (Fin.last (M + 1))) = γ (u 0) := by
    rw [hv1, hu0]
    exact γ.target.trans γ.source.symm
  have hTest :
      (Path.Homotopic (γ.subpath (u 0) (v (Fin.last (M + 1))))
        ((Path.refl (γ (u 0))).cast rfl hlocalclose)) →
      (Path.Homotopic (γ.subpath (t 0) (t (Fin.last ((N + 1) + (M + 1)))))
        ((Path.refl (γ (t 0))).cast rfl hclose)) := by
    intro hSub
    simpa [u, v, Fin.cast, Fin.castAdd, Fin.castLE] using hSub
  trivial
