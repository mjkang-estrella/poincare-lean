import Poincare.TopologyExtraction

namespace Poincare

/--
Transport a recognized one-point compactification target's single-puncture
complement to the Euclidean chart of the model compactification.
-/
noncomputable def homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3) := by
  let eM : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)) := Classical.choice h
  let hCompl :
      ({x}ᶜ : Set M) ≃ₜ
        ({eM x}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    eM.subtype (fun y => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · intro hy hyeq
        exact hy (eM.injective hyeq)
      · intro hy hyx
        exact hy (by rw [hyx]))
  exact hCompl.trans
    (onePoint_threeSpace_compl_singleton_homeomorph_euclidean (eM x))

/--
Every single-puncture complement of a space recognized as the one-point
compactification of `R^3` is contractible.
-/
theorem compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) :=
  (homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    h x).contractibleSpace

/--
Transport a recognized one-point compactification target's two-puncture
complement to the punctured Euclidean chart of the model compactification.
-/
theorem exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  rcases h with ⟨eM⟩
  have hImage : eM y ≠ eM x := by
    intro hxy
    exact hyx (eM.injective hxy)
  let puncture : EuclideanSpace ℝ (Fin 3) :=
    onePoint_threeSpace_compl_singleton_homeomorph_euclidean (eM x)
      (onePoint_threeSpace_pointInComplement hImage)
  let hCompl :
      (({x} ∪ {y})ᶜ : Set M) ≃ₜ
        (({eM x} ∪ {eM y})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    eM.subtype (fun z => by
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hz hzImage
        rcases hzImage with hzx | hzy
        · exact hz (Or.inl (eM.injective hzx))
        · exact hz (Or.inr (eM.injective hzy))
      · intro hz hzSource
        rcases hzSource with hzx | hzy
        · exact hz (Or.inl (by rw [hzx]))
        · exact hz (Or.inr (by rw [hzy])))
  exact ⟨puncture,
    ⟨hCompl.trans
      (onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean
        hImage)⟩⟩

/--
Every two-puncture complement of a space recognized as the one-point
compactification of `R^3` is simply connected.
-/
theorem twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  rcases h with ⟨eM⟩
  have hImage : eM y ≠ eM x := by
    intro hxy
    exact hyx (eM.injective hxy)
  let hCompl :
      (({x} ∪ {y})ᶜ : Set M) ≃ₜ
        (({eM x} ∪ {eM y})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    eM.subtype (fun z => by
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hz hzImage
        rcases hzImage with hzx | hzy
        · exact hz (Or.inl (eM.injective hzx))
        · exact hz (Or.inr (eM.injective hzy))
      · intro hz hzSource
        rcases hzSource with hzx | hzy
        · exact hz (Or.inl (by rw [hzx]))
        · exact hz (Or.inr (by rw [hzy])))
  letI : SimplyConnectedSpace
      (({eM x} ∪ {eM y})ᶜ :
        Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hImage
  exact hCompl.toHomotopyEquiv.simplyConnectedSpace

/--
The based fundamental group of every two-puncture complement of a recognized
one-point compactification target is trivial.
-/
theorem twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  infer_instance

/--
The same single-puncture Euclidean chart transport, stated from recognition as
the project `ThreeSphere`.
-/
noncomputable def homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
Every single-puncture complement of a space recognized as `ThreeSphere` is
contractible.
-/
theorem compl_singleton_contractibleSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) :=
  (homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
    h x).contractibleSpace

/--
Every two-puncture complement of a space recognized as `ThreeSphere` is simply
connected.
-/
theorem twoPointComplement_simplyConnectedSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
The based fundamental group of every two-puncture complement of a space
recognized as `ThreeSphere` is trivial.
-/
theorem twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint

end Poincare
