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
The singleton complement is path-connected because the compactification chart
has already recovered contractibility.
-/
theorem onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : ContractibleSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_contractibleSpace p
  infer_instance

/--
The singleton complement is connected, via the path-connected structure obtained
from contractibility.
-/
theorem onePoint_threeSpace_compl_singleton_connectedSpace_of_contractible
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible p
  infer_instance

/--
The singleton complement is nonempty, witnessed by its path-connected structure.
-/
theorem onePoint_threeSpace_compl_singleton_nonempty_of_contractible
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Nonempty
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible p
  infer_instance

/--
Any two points in a singleton complement of the one-point compactification
model are joined by a path.
-/
theorem onePoint_threeSpace_compl_singleton_path_nonempty_of_contractible
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty (Path x y) := by
  intro x y
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible p
  exact PathConnectedSpace.joined x y

/--
The path component of any point in a singleton complement is the whole
singleton complement.
-/
theorem onePoint_threeSpace_compl_singleton_pathComponent_eq_univ_of_contractible
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    pathComponent x = Set.univ := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible p
  ext y
  constructor
  · intro _hy
    exact Set.mem_univ y
  · intro _hy
    exact PathConnectedSpace.joined x y

/--
The zeroth homotopy quotient of a singleton complement has one class.
-/
theorem onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Subsingleton
      (ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible p
  infer_instance

/--
The zeroth homotopy group formulation of singleton-complement collapse.
-/
theorem onePoint_threeSpace_compl_singleton_piZero_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := basepoint)).subsingleton_congr).mpr
        (onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p)

/--
The fundamental group of a singleton complement is trivial at every basepoint.
-/
theorem onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (FundamentalGroup
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  letI : SimplyConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  infer_instance

/--
The first homotopy group formulation of singleton-complement collapse.
-/
theorem onePoint_threeSpace_compl_singleton_piOne_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := basepoint)).subsingleton_congr).mpr
        (onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton
          p basepoint)

/--
Low-homotopy collapse package for singleton complements of the one-point
compactification model.
-/
theorem onePoint_threeSpace_compl_singleton_lowHomotopy_package
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    SimplyConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (ZerothHomotopy
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path x y)) ∧
      (∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  exact
    ⟨ onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
    , onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p
    , onePoint_threeSpace_compl_singleton_piZero_subsingleton p basepoint
    , onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton
        p basepoint
    , onePoint_threeSpace_compl_singleton_piOne_subsingleton p basepoint
    , onePoint_threeSpace_compl_singleton_path_nonempty_of_contractible p
    , onePoint_threeSpace_compl_singleton_pathComponent_eq_univ_of_contractible p
    ⟩

/--
The singleton-complement low-homotopy collapse as explicit equality
eliminators for path components, `π₀`, the fundamental group, and `π₁`.
-/
theorem onePoint_threeSpace_compl_singleton_lowHomotopy_eq_package
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ZerothHomotopy.mk x = ZerothHomotopy.mk y) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b :
        FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) := by
  letI : Subsingleton
      (ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p
  letI : Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    onePoint_threeSpace_compl_singleton_piZero_subsingleton p basepoint
  letI : Subsingleton
      (FundamentalGroup
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton
      p basepoint
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    onePoint_threeSpace_compl_singleton_piOne_subsingleton p basepoint
  exact
    ⟨ fun _x _y => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    ⟩

/--
The singleton complement package needed by downstream puncture topology:
contractibility, ordinary connectedness consequences, and the already
transported simple/local path-connected structures.
-/
theorem onePoint_threeSpace_compl_singleton_contractible_topology_package
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ContractibleSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      LocPathConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  exact
    ⟨onePoint_threeSpace_compl_singleton_contractibleSpace p,
      onePoint_threeSpace_compl_singleton_nonempty_of_contractible p,
      onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible p,
      onePoint_threeSpace_compl_singleton_connectedSpace_of_contractible p,
      onePoint_threeSpace_compl_singleton_simplyConnectedSpace p,
      onePoint_threeSpace_compl_singleton_locPathConnectedSpace p⟩

/--
The singleton complement topology package with its concrete Euclidean chart,
path-collapse fields, and transported simple/local path-connected structures.
-/
theorem onePoint_threeSpace_compl_singleton_euclidean_topology_package
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Nonempty
        (({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
      ContractibleSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      LocPathConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path x y)) ∧
      (∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  exact
    ⟨ ⟨onePoint_threeSpace_compl_singleton_homeomorph_euclidean p⟩
    , onePoint_threeSpace_compl_singleton_contractibleSpace p
    , onePoint_threeSpace_compl_singleton_nonempty_of_contractible p
    , onePoint_threeSpace_compl_singleton_pathConnectedSpace_of_contractible p
    , onePoint_threeSpace_compl_singleton_connectedSpace_of_contractible p
    , onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
    , onePoint_threeSpace_compl_singleton_locPathConnectedSpace p
    , onePoint_threeSpace_compl_singleton_path_nonempty_of_contractible p
    , onePoint_threeSpace_compl_singleton_pathComponent_eq_univ_of_contractible p
    ⟩

end Poincare
