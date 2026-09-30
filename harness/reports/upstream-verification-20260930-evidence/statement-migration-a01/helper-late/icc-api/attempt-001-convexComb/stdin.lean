import Mathlib.Topology.Subpath
universe u
namespace PoincareProbe
theorem path_homotopy_subpathTransSubpathRefl_forall_mem_of_forall_mem
    {X : Type u} [TopologicalSpace X] {S : Set X} {x₀ x₁ : X}
    (p : Path x₀ x₁) (hp : ∀ t, p t ∈ S)
    (t₀ t₁ t₂ : unitInterval) :
    ∀ t, Path.Homotopy.subpathTransSubpathRefl p t₀ t₁ t₂ t ∈ S := by
  intro t
  change ((p.subpath t₀ (Set.Icc.convexComb t₁ t₂ t.1)).trans
    (p.subpath (Set.Icc.convexComb t₁ t₂ t.1) t₂)) t.2 ∈ S
  rw [Path.trans_apply]
  split_ifs <;> change p _ ∈ S <;> exact hp _
end PoincareProbe
