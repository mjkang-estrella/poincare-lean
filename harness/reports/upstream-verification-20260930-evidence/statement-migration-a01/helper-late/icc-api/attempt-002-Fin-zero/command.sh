LEAN_NUM_THREADS=1 lake env lean --stdin <<'LEAN'
import Mathlib.Topology.Subpath
set_option backward.isDefEq.respectTransparency false
example (N M : ℕ) (t : Fin ((N + 1) + (M + 1) + 1) → unitInterval)
    (h0 : t 0 = 0) :
    (let u : Fin (N + 2) → unitInterval := fun i => t ((i.castAdd (M + 1)).cast (by omega)); u 0 = 0) := by
  dsimp only
  simpa [Fin.castAdd, Fin.cast] using h0
example (N M L K T R A₀ : ℕ)
    (t : Fin ((N + 1) + (M + 1) + (L + 1) + (K + 1) + (T + 1) + (R + 1) + (A₀ + 1) + 1) → unitInterval)
    (h0 : t 0 = 0) :
    (let u : Fin (N + 2) → unitInterval :=
      fun i => t ((i.castAdd ((M + 1) + (L + 1) + (K + 1) + (T + 1) + (R + 1) + (A₀ + 1))).cast (by omega)); u 0 = 0) := by
  dsimp only
  simpa [Fin.castAdd, Fin.cast] using h0
LEAN