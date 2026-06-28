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
