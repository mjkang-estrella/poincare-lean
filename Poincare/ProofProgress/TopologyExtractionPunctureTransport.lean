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
Every single-puncture complement of a space recognized as the one-point
compactification of `R^3` is path-connected.
-/
theorem compl_singleton_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    PathConnectedSpace ({x}ᶜ : Set M) := by
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace
      h x
  infer_instance

/--
Any two points in the single-puncture complement of a recognized one-point
compactification target are joined by a path.
-/
theorem compl_singleton_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Nonempty (Path a b) := by
  intro a b
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h x
  exact PathConnectedSpace.joined a b

/--
The path component of any point in the single-puncture complement of a
recognized one-point compactification target is the whole complement.
-/
theorem compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    pathComponent basepoint = Set.univ := by
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h x
  ext z
  constructor
  · intro _hz
    exact Set.mem_univ z
  · intro _hz
    exact PathConnectedSpace.joined basepoint z

/--
Every single-puncture complement of a space recognized as the one-point
compactification of `R^3` is simply connected.
-/
theorem compl_singleton_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    SimplyConnectedSpace ({x}ᶜ : Set M) := by
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace
      h x
  infer_instance

/--
The based fundamental group of every single-puncture complement of a recognized
one-point compactification target is trivial.
-/
theorem compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) := by
  letI : SimplyConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h x
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  infer_instance

/--
The first homotopy group formulation of single-puncture complement collapse for
a recognized one-point compactification target.
-/
theorem compl_singleton_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ({x}ᶜ : Set M))
      (x := basepoint)).subsingleton_congr).mpr
        (compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
          h x basepoint)

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
compactification of `R^3` is path-connected.
-/
theorem twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  rcases
    exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
      h hyx with ⟨puncture, chartNonempty⟩
  rcases chartNonempty with ⟨chart⟩
  letI : PathConnectedSpace ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    euclideanThree_compl_singleton_pathConnectedSpace puncture
  exact chart.symm.surjective.pathConnectedSpace chart.symm.continuous

/--
Any two points in the two-puncture complement of a recognized one-point
compactification target are joined by a path.
-/
theorem twoPointComplement_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Nonempty (Path a b) := by
  intro a b
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  exact PathConnectedSpace.joined a b

/--
The path component of any point in the two-puncture complement of a recognized
one-point compactification target is the whole complement.
-/
theorem twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    pathComponent basepoint = Set.univ := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  ext z
  constructor
  · intro _hz
    exact Set.mem_univ z
  · intro _hz
    exact PathConnectedSpace.joined basepoint z

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
The first homotopy group formulation of two-puncture complement collapse for a
recognized one-point compactification target.
-/
theorem twoPointComplement_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := (({x} ∪ {y})ᶜ : Set M))
      (x := basepoint)).subsingleton_congr).mpr
        (twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
          h hyx basepoint)

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
Every single-puncture complement of a space recognized as `ThreeSphere` is
path-connected.
-/
theorem compl_singleton_pathConnectedSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    PathConnectedSpace ({x}ᶜ : Set M) :=
  compl_singleton_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
Any two points in the single-puncture complement of a `ThreeSphere`-recognized
space are joined by a path.
-/
theorem compl_singleton_path_nonempty_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Nonempty (Path a b) :=
  compl_singleton_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
The path component of any point in the single-puncture complement of a
`ThreeSphere`-recognized space is the whole complement.
-/
theorem compl_singleton_pathComponent_eq_univ_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    pathComponent basepoint = Set.univ :=
  compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x
    basepoint

/--
Every single-puncture complement of a space recognized as `ThreeSphere` is
simply connected.
-/
theorem compl_singleton_simplyConnectedSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    SimplyConnectedSpace ({x}ᶜ : Set M) :=
  compl_singleton_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
The based fundamental group of every single-puncture complement of a
`ThreeSphere`-recognized space is trivial.
-/
theorem compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) :=
  compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x
    basepoint

/--
The first homotopy group formulation of single-puncture complement collapse for
a `ThreeSphere`-recognized space.
-/
theorem compl_singleton_piOne_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
  compl_singleton_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x
    basepoint

/--
Every two-puncture complement of a space recognized as `ThreeSphere` is
path-connected.
-/
theorem twoPointComplement_pathConnectedSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Any two points in the two-puncture complement of a `ThreeSphere`-recognized
space are joined by a path.
-/
theorem twoPointComplement_path_nonempty_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Nonempty (Path a b) :=
  twoPointComplement_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
The path component of any point in the two-puncture complement of a
`ThreeSphere`-recognized space is the whole complement.
-/
theorem twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    pathComponent basepoint = Set.univ :=
  twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint

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

/--
The first homotopy group formulation of two-puncture complement collapse for a
`ThreeSphere`-recognized space.
-/
theorem twoPointComplement_piOne_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  twoPointComplement_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint

end Poincare
