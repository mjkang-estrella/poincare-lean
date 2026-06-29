import Poincare.ProofProgress.TopologyExtractionPunctureTransport

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
The singleton-complement low-homotopy collapse as canonical uniqueness data:
the path-component quotient, `π₀`, the fundamental group, and `π₁` each have a
unique element at every basepoint.
-/
theorem onePoint_threeSpace_compl_singleton_lowHomotopy_unique_package
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Nonempty (Unique
        (ZerothHomotopy
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) := by
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
  let componentPoint :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_compl_singleton_nonempty_of_contractible p)
  exact
    ⟨ ⟨uniqueOfSubsingleton (ZerothHomotopy.mk componentPoint)⟩
    , ⟨uniqueOfSubsingleton (default :
        HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)⟩
    , ⟨uniqueOfSubsingleton (default :
        FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)⟩
    , ⟨uniqueOfSubsingleton (default :
        HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)⟩
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

/--
The singleton complement package with both the concrete Euclidean chart and the
canonical low-homotopy uniqueness data at a chosen basepoint.  This is the
combined endpoint needed by puncture-topology consumers that require ordinary
topology, simple/local path-connectedness, path-component collapse, and
canonical trivial `π₀`/`π₁` objects from one source.
-/
theorem onePoint_threeSpace_compl_singleton_euclidean_lowHomotopy_unique_package
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
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
      Nonempty (Unique
        (ZerothHomotopy
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path x y)) ∧
      (∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  rcases onePoint_threeSpace_compl_singleton_euclidean_topology_package p with
    ⟨ chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , pathNonempty
    , pathComponentEqUniv
    ⟩
  rcases
    onePoint_threeSpace_compl_singleton_lowHomotopy_unique_package
      p basepoint with
    ⟨zerothUnique, piZeroUnique, fundamentalGroupUnique, piOneUnique⟩
  exact
    ⟨ chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothUnique
    , piZeroUnique
    , fundamentalGroupUnique
    , piOneUnique
    , pathNonempty
    , pathComponentEqUniv
    ⟩

/--
At any externally supplied basepoint, the singleton-complement endpoint carries
the Euclidean chart, ordinary topology fields, canonical low-homotopy
uniqueness objects, equality eliminators, and path-collapse data without
selecting a new basepoint.
-/
theorem onePoint_threeSpace_compl_singleton_euclidean_complete_collapse_package
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
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
      Nonempty (Unique
        (ZerothHomotopy
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
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
        a = b) ∧
      (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path x y)) ∧
      (∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  rcases
      onePoint_threeSpace_compl_singleton_euclidean_lowHomotopy_unique_package
        p basepoint with
    ⟨ chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothUnique
    , piZeroUnique
    , fundamentalGroupUnique
    , piOneUnique
    , pathNonempty
    , pathComponentEqUniv
    ⟩
  rcases onePoint_threeSpace_compl_singleton_lowHomotopy_eq_package
      p basepoint with
    ⟨zerothEq, piZeroEq, fundamentalGroupEq, piOneEq⟩
  exact
    ⟨ chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothUnique
    , piZeroUnique
    , fundamentalGroupUnique
    , piOneUnique
    , zerothEq
    , piZeroEq
    , fundamentalGroupEq
    , piOneEq
    , pathNonempty
    , pathComponentEqUniv
    ⟩

/--
Transported singleton-complement collapse for any space recognized as the
one-point compactification model.  The supplied source basepoint is retained
through the Euclidean chart, ordinary topology fields, canonical low-homotopy
uniqueness objects, equality eliminators, and path-collapse data.
-/
theorem compl_singleton_euclidean_complete_collapse_package_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
      ContractibleSpace ({x}ᶜ : Set M) ∧
      Nonempty ({x}ᶜ : Set M) ∧
      PathConnectedSpace ({x}ᶜ : Set M) ∧
      ConnectedSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace ({x}ᶜ : Set M) ∧
      LocPathConnectedSpace ({x}ᶜ : Set M) ∧
      Nonempty (Unique (ZerothHomotopy ({x}ᶜ : Set M))) ∧
      Nonempty (Unique (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint)) ∧
      Nonempty (Unique (FundamentalGroup ({x}ᶜ : Set M) basepoint)) ∧
      Nonempty (Unique (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint)) ∧
      (∀ y z : ({x}ᶜ : Set M), ZerothHomotopy.mk y = ZerothHomotopy.mk z) ∧
      (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint, a = b) ∧
      (∀ a b : FundamentalGroup ({x}ᶜ : Set M) basepoint, a = b) ∧
      (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint, a = b) ∧
      (∀ y z : ({x}ᶜ : Set M), Nonempty (Path y z)) ∧
      (∀ y : ({x}ᶜ : Set M), pathComponent y = Set.univ) := by
  let chart :=
    homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
      h x
  letI : ContractibleSpace ({x}ᶜ : Set M) := chart.contractibleSpace
  letI : PathConnectedSpace ({x}ᶜ : Set M) := inferInstance
  letI : ConnectedSpace ({x}ᶜ : Set M) := inferInstance
  letI : SimplyConnectedSpace ({x}ᶜ : Set M) :=
    chart.toHomotopyEquiv.simplyConnectedSpace
  letI : LocPathConnectedSpace ({x}ᶜ : Set M) := by
    letI : LocPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) := inferInstance
    exact chart.isOpenEmbedding.locPathConnectedSpace
  letI : Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) := inferInstance
  letI : Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) :=
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := ({x}ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
        inferInstance
  letI : Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) := by
    change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
    infer_instance
  letI : Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ({x}ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
        inferInstance
  exact
    ⟨ ⟨chart⟩
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , ⟨uniqueOfSubsingleton (ZerothHomotopy.mk basepoint)⟩
    , ⟨uniqueOfSubsingleton (default :
        HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint)⟩
    , ⟨uniqueOfSubsingleton (default :
        FundamentalGroup ({x}ᶜ : Set M) basepoint)⟩
    , ⟨uniqueOfSubsingleton (default :
        HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint)⟩
    , fun _y _z => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun y z => PathConnectedSpace.joined y z
    , fun y => by
        ext z
        constructor
        · intro _hz
          exact Set.mem_univ z
        · intro _hz
          exact PathConnectedSpace.joined y z
    ⟩

/--
The transported singleton-complement collapse can also be consumed without an
externally supplied source basepoint.  The Euclidean complement chart supplies
nonemptiness of `{x}ᶜ`, and the selected endpoint carries the same full
collapse package: Euclidean chart, contractibility, low-homotopy uniqueness,
equality eliminators, and path-collapse data.
-/
theorem compl_singleton_euclidean_complete_collapse_package_with_basepoint_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ∃ basepoint : ({x}ᶜ : Set M),
      Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        PathConnectedSpace ({x}ᶜ : Set M) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        LocPathConnectedSpace ({x}ᶜ : Set M) ∧
        Nonempty (Unique (ZerothHomotopy ({x}ᶜ : Set M))) ∧
        Nonempty (Unique (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint)) ∧
        Nonempty (Unique (FundamentalGroup ({x}ᶜ : Set M) basepoint)) ∧
        Nonempty (Unique (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint)) ∧
        (∀ y z : ({x}ᶜ : Set M),
          ZerothHomotopy.mk y = ZerothHomotopy.mk z) ∧
        (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint, a = b) ∧
        (∀ a b : FundamentalGroup ({x}ᶜ : Set M) basepoint, a = b) ∧
        (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint, a = b) ∧
        (∀ y z : ({x}ᶜ : Set M), Nonempty (Path y z)) ∧
        (∀ y : ({x}ᶜ : Set M), pathComponent y = Set.univ) := by
  let chart :=
    homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
      h x
  letI : ContractibleSpace ({x}ᶜ : Set M) := chart.contractibleSpace
  let basepoint : ({x}ᶜ : Set M) :=
    Classical.choice (show Nonempty ({x}ᶜ : Set M) by infer_instance)
  exact
    ⟨ basepoint
    , compl_singleton_euclidean_complete_collapse_package_of_homeomorph_to_onePoint_threeSpace
        h x basepoint
    ⟩

/--
The singleton complement package can be produced without an externally chosen
basepoint: contractibility supplies a point of the complement, and the full
Euclidean/low-homotopy uniqueness package is then available at that selected
basepoint.
-/
theorem onePoint_threeSpace_compl_singleton_euclidean_lowHomotopy_unique_package_with_basepoint
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∃ basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
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
        Nonempty (Unique
          (ZerothHomotopy
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path x y)) ∧
        (∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_compl_singleton_nonempty_of_contractible p)
  exact
    ⟨ basepoint
    , onePoint_threeSpace_compl_singleton_euclidean_lowHomotopy_unique_package
        p basepoint
    ⟩

/--
The singleton complement equality-eliminator package can also be produced
without an externally chosen basepoint.  The selected endpoint carries the
Euclidean chart, ordinary topology fields, explicit low-homotopy equality
eliminators, and the path-collapse data at the chosen basepoint.
-/
theorem onePoint_threeSpace_compl_singleton_euclidean_lowHomotopy_eq_package_with_basepoint
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∃ basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
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
          a = b) ∧
        (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path x y)) ∧
        (∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_compl_singleton_nonempty_of_contractible p)
  rcases onePoint_threeSpace_compl_singleton_euclidean_topology_package p with
    ⟨ chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , pathNonempty
    , pathComponentEqUniv
    ⟩
  rcases onePoint_threeSpace_compl_singleton_lowHomotopy_eq_package
      p basepoint with
    ⟨zerothEq, piZeroEq, fundamentalGroupEq, piOneEq⟩
  exact
    ⟨ basepoint
    , chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothEq
    , piZeroEq
    , fundamentalGroupEq
    , piOneEq
    , pathNonempty
    , pathComponentEqUniv
    ⟩

/--
The selected singleton-complement endpoint carries both canonical uniqueness
objects and equality eliminators at the same basepoint.  This keeps the
Euclidean chart, contractibility, transported simple/local path-connectedness,
path-collapse data, and low-homotopy collapse witnesses synchronized for
downstream puncture-topology consumers.
-/
theorem onePoint_threeSpace_compl_singleton_euclidean_complete_collapse_package_with_basepoint
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∃ basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
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
        Nonempty (Unique
          (ZerothHomotopy
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
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
          a = b) ∧
        (∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path x y)) ∧
        (∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_compl_singleton_nonempty_of_contractible p)
  rcases
      onePoint_threeSpace_compl_singleton_euclidean_lowHomotopy_unique_package
        p basepoint with
    ⟨ chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothUnique
    , piZeroUnique
    , fundamentalGroupUnique
    , piOneUnique
    , pathNonempty
    , pathComponentEqUniv
    ⟩
  rcases onePoint_threeSpace_compl_singleton_lowHomotopy_eq_package
      p basepoint with
    ⟨zerothEq, piZeroEq, fundamentalGroupEq, piOneEq⟩
  exact
    ⟨ basepoint
    , chart
    , contractible
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothUnique
    , piZeroUnique
    , fundamentalGroupUnique
    , piOneUnique
    , zerothEq
    , piZeroEq
    , fundamentalGroupEq
    , piOneEq
    , pathNonempty
    , pathComponentEqUniv
    ⟩

end Poincare
