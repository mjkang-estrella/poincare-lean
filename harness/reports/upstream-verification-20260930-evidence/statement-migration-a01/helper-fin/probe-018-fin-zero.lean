import Mathlib.Topology.Subpath
universe u
example {Y : Type u} [TopologicalSpace Y] {N M : ℕ}
    (t : Fin ((N + 1) + (M + 1) + 1) → unitInterval) (h0 : t 0 = 0) :
    let u : Fin (N + 2) → unitInterval := fun i => t ((i.castAdd (M + 1)).cast (by omega))
    u 0 = 0 := by
  dsimp only
  let u : Fin (N + 2) → unitInterval := fun i => t ((i.castAdd (M + 1)).cast (by omega))
  change u 0 = 0
  simpa [u, Fin.cast, Fin.castAdd, Fin.castLE] using h0
