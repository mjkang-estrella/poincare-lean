import Poincare.TopologyExtraction

namespace Poincare

/--
The named one-point compactification homeomorphism identifies the two-puncture
compactification complement with the corresponding two-puncture complement in
the project `ThreeSphere`.
-/
noncomputable def onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (_hqp : q ≠ p) :
    (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere) := by
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  exact e.subtype (fun x => by
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro hx hxImage
      rcases hxImage with hxp | hxq
      · exact hx (Or.inl (e.injective hxp))
      · exact hx (Or.inr (e.injective hxq))
    · intro hx hxSource
      rcases hxSource with hxp | hxq
      · exact hx (Or.inl (by rw [hxp]))
      · exact hx (Or.inr (by rw [hxq])))

/--
The two-puncture compactification complement is simply connected by transporting
it to the corresponding `ThreeSphere` two-puncture complement.
-/
theorem onePoint_threeSpace_twoPointComplement_simplyConnectedSpace_via_threeSphere
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    SimplyConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  letI : SimplyConnectedSpace (({e p} ∪ {e q})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hImage
  exact
    (onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp).toHomotopyEquiv.simplyConnectedSpace

end Poincare
