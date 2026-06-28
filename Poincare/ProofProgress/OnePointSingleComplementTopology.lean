import Poincare.TopologyExtraction

open scoped Manifold ContDiff

namespace Poincare

/--
Deleting one point from the one-point compactification model leaves a
contractible space, by transporting Euclidean contractibility across the
compactification chart.
-/
theorem onePoint_threeSpace_compl_singleton_contractibleSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ContractibleSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  (onePoint_threeSpace_compl_singleton_homeomorph_euclidean p).contractibleSpace

/--
Deleting one point from the one-point compactification model leaves a
path-connected space.
-/
theorem onePoint_threeSpace_compl_singleton_pathConnectedSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : ContractibleSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_contractibleSpace p
  infer_instance

/--
Any two points in the singleton complement are joined by a path.
-/
theorem onePoint_threeSpace_compl_singleton_path_nonempty
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∀ (x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))),
      Nonempty (Path x y) := by
  intro x y
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  exact PathConnectedSpace.joined x y

/--
The path component of any point in the singleton complement is the whole
singleton complement.
-/
theorem onePoint_threeSpace_compl_singleton_pathComponent_eq_univ
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    pathComponent x = Set.univ := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  ext y
  constructor
  · intro _hy
    exact Set.mem_univ y
  · intro _hy
    exact PathConnectedSpace.joined x y

/--
The zeroth homotopy quotient of the singleton complement has only one class.
-/
theorem onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Subsingleton
      (ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

/--
Any two zeroth-homotopy classes in the singleton complement agree.
-/
theorem onePoint_threeSpace_compl_singleton_zerothHomotopy_mk_eq
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ZerothHomotopy.mk x = ZerothHomotopy.mk y := by
  letI : Subsingleton
      (ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p
  exact Subsingleton.elim _ _

/--
The zeroth homotopy quotient of the singleton complement has a unique class.
-/
theorem onePoint_threeSpace_compl_singleton_zerothHomotopy_exists_unique
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∃ baseClass :
      ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∀ homotopyClass :
        ZerothHomotopy
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        homotopyClass = baseClass := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  let basePoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (PathConnectedSpace.nonempty
        (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))))
  exact ⟨ZerothHomotopy.mk basePoint, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The zeroth homotopy group formulation of the singleton-complement collapse.
-/
theorem onePoint_threeSpace_compl_singleton_piZero_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := x)).subsingleton_congr).mpr
        (onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p)

/--
Any two zeroth homotopy group classes in the singleton complement agree.
-/
theorem onePoint_threeSpace_compl_singleton_piZero_eq
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (a b :
      HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :
    a = b := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_piZero_subsingleton p x
  exact Subsingleton.elim _ _

/--
The zeroth homotopy group of the singleton complement has a unique class.
-/
theorem onePoint_threeSpace_compl_singleton_piZero_exists_unique
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ baseClass :
      HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
      ∀ homotopyClass :
        HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_piZero_subsingleton p x
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
Simple-connectedness of the singleton complement collapses its based
fundamental group.
-/
theorem onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton (FundamentalGroup
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  letI : SimplyConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/--
The equivalent first homotopy group formulation of singleton-complement
triviality.
-/
theorem onePoint_threeSpace_compl_singleton_piOne_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton (HomotopyGroup.Pi 1
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := x)).subsingleton_congr).mpr
        (onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton p x)

/--
The singleton complement is connected as a direct consequence of the named
path-connectedness theorem above.
-/
theorem onePoint_threeSpace_compl_singleton_connectedSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

/--
The singleton complement is nonempty, witnessed by its path-connected topology.
-/
theorem onePoint_threeSpace_compl_singleton_nonempty
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Nonempty
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

end Poincare
