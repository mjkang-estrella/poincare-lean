LEAN_NUM_THREADS=1 lake env lean --stdin <<'LEAN'
import Mathlib.Topology.Subpath
set_option backward.isDefEq.respectTransparency false
universe u
example {X : Type u} [TopologicalSpace X] {x : X} (γ : Path x x)
    (N M : ℕ) (t : Fin ((N + 1) + (M + 1) + 1) → unitInterval)
    (h0 : t 0 = 0) (h1 : t (Fin.last ((N + 1) + (M + 1))) = 1) :
    let u : Fin (N + 2) → unitInterval := fun i => t ((i.castAdd (M + 1)).cast (by omega))
    let v : Fin (M + 2) → unitInterval := fun j => t ((j.natAdd (N + 1)).cast (by omega))
    ∀ (hu0 : u 0 = 0) (hv1 : v (Fin.last (M + 1)) = 1),
      Path.Homotopic (γ.subpath (u 0) (v (Fin.last (M + 1))))
        ((Path.refl (γ (u 0))).cast rfl (by rw [hv1, hu0]; exact γ.target.trans γ.source.symm)) →
      Path.Homotopic (γ.subpath (t 0) (t (Fin.last ((N + 1) + (M + 1)))))
        ((Path.refl (γ (t 0))).cast rfl (by rw [h1, h0]; exact γ.target.trans γ.source.symm)) := by
  dsimp only
  intro hu0 hv1 hSub
  simpa [Fin.castAdd, Fin.cast] using hSub
example {X : Type u} [TopologicalSpace X] {x : X} (γ : Path x x)
    (N M L K T R A₀ : ℕ)
    (t : Fin ((N + 1) + (M + 1) + (L + 1) + (K + 1) + (T + 1) + (R + 1) + (A₀ + 1) + 1) → unitInterval)
    (h0 : t 0 = 0)
    (h1 : t (Fin.last ((N + 1) + (M + 1) + (L + 1) + (K + 1) + (T + 1) + (R + 1) + (A₀ + 1))) = 1) :
    let u : Fin (N + 2) → unitInterval :=
      fun i => t ((i.castAdd ((M + 1) + (L + 1) + (K + 1) + (T + 1) + (R + 1) + (A₀ + 1))).cast (by omega))
    let a : Fin (A₀ + 2) → unitInterval :=
      fun b => t ((b.natAdd ((N + 1) + (M + 1) + (L + 1) + (K + 1) + (T + 1) + (R + 1))).cast (by omega))
    ∀ (hu0 : u 0 = 0) (ha1 : a (Fin.last (A₀ + 1)) = 1),
      Path.Homotopic (γ.subpath (u 0) (a (Fin.last (A₀ + 1))))
        ((Path.refl (γ (u 0))).cast rfl (by rw [ha1, hu0]; exact γ.target.trans γ.source.symm)) →
      Path.Homotopic
        (γ.subpath (t 0)
          (t (Fin.last ((N + 1) + (M + 1) + (L + 1) + (K + 1) + (T + 1) + (R + 1) + (A₀ + 1)))))
        ((Path.refl (γ (t 0))).cast rfl (by rw [h1, h0]; exact γ.target.trans γ.source.symm)) := by
  dsimp only
  intro hu0 ha1 hSub
  simpa [Fin.castAdd, Fin.cast] using hSub
LEAN