import Poincare.ProofProgress.TopologyExtractionPunctureTransport
import Poincare.TopologyExtraction

open scoped Manifold ContDiff

namespace Poincare

/--
The complement of two distinct points in the one-point compactification model is
path-connected.  The proof uses the existing punctured-Euclidean chart for the
actual two-point complement and transports path-connectedness back from `ℝ³`
with one point removed.
-/
theorem onePoint_threeSpace_twoPointComplement_pathConnectedSpace
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  let puncture : EuclideanSpace ℝ (Fin 3) :=
    onePoint_threeSpace_compl_singleton_homeomorph_euclidean p
      (onePoint_threeSpace_pointInComplement hqp)
  let e := onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean hqp
  letI : PathConnectedSpace ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    euclideanThree_compl_singleton_pathConnectedSpace puncture
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

/--
The two-point complement is connected as a direct consequence of the named
path-connectedness theorem above.
-/
theorem onePoint_threeSpace_twoPointComplement_connectedSpace
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  infer_instance

/--
The two-point complement is nonempty, witnessed by its path-connected topology.
-/
theorem onePoint_threeSpace_twoPointComplement_nonempty
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    Nonempty
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  infer_instance

/--
Any two points in a two-point complement of the one-point compactification
model are joined by a path.
-/
theorem onePoint_threeSpace_twoPointComplement_path_nonempty
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ x y :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty (Path x y) := by
  intro x y
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  exact PathConnectedSpace.joined x y

/--
Every path component of a two-point complement is the whole complement.
-/
theorem onePoint_threeSpace_twoPointComplement_pathComponent_eq_univ
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    pathComponent x = Set.univ := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  ext y
  constructor
  · intro _hy
    exact Set.mem_univ y
  · intro _hy
    exact PathConnectedSpace.joined x y

/--
The zeroth homotopy quotient of a two-point complement has one class.
-/
theorem onePoint_threeSpace_twoPointComplement_zerothHomotopy_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    Subsingleton
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  infer_instance

/--
The `π₀` formulation of two-point complement path-component collapse.
-/
theorem onePoint_threeSpace_twoPointComplement_piZero_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := (({p} ∪ {q})ᶜ :
        Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := basepoint)).subsingleton_congr).mpr
        (onePoint_threeSpace_twoPointComplement_zerothHomotopy_subsingleton
          hqp)

/--
The `π₁` formulation of two-point complement simple-connected collapse.
-/
theorem onePoint_threeSpace_twoPointComplement_piOne_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := (({p} ∪ {q})ᶜ :
        Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := basepoint)).subsingleton_congr).mpr
        (onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton
          hqp basepoint)

/--
The two-point compactification complement package with its concrete punctured
Euclidean chart, ordinary topology fields, simple/local path-connectedness,
low-homotopy collapse, and path-component collapse at a supplied basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_puncturedEuclidean_lowHomotopy_package
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Nonempty
        ((({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          ({onePoint_threeSpace_compl_singleton_homeomorph_euclidean p
              (onePoint_threeSpace_pointInComplement hqp)}ᶜ :
            Set (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      LocPathConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ x y :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path x y)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  exact
    ⟨ ⟨onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean
          hqp⟩
    , onePoint_threeSpace_twoPointComplement_nonempty hqp
    , onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
    , onePoint_threeSpace_twoPointComplement_connectedSpace hqp
    , onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hqp
    , onePoint_threeSpace_twoPointComplement_locPathConnectedSpace hqp
    , onePoint_threeSpace_twoPointComplement_zerothHomotopy_subsingleton hqp
    , onePoint_threeSpace_twoPointComplement_piZero_subsingleton hqp
        basepoint
    , onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton
        hqp basepoint
    , onePoint_threeSpace_twoPointComplement_piOne_subsingleton hqp basepoint
    , onePoint_threeSpace_twoPointComplement_path_nonempty hqp
    , onePoint_threeSpace_twoPointComplement_pathComponent_eq_univ hqp
    ⟩

/--
The two-point compactification complement package with explicit collapsed
low-homotopy base classes at a supplied basepoint.  This strengthens the
subsingleton-level package by retaining equality eliminators for `π₀`, the
fundamental group, and `π₁`, plus named base classes to which every class
collapses.
-/
theorem onePoint_threeSpace_twoPointComplement_lowHomotopy_baseclass_collapse_package
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Nonempty
        ((({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          ({onePoint_threeSpace_compl_singleton_homeomorph_euclidean p
              (onePoint_threeSpace_pointInComplement hqp)}ᶜ :
            Set (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      LocPathConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ x y :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ZerothHomotopy.mk x = ZerothHomotopy.mk y) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b :
        FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∃ baseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∀ x y :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path x y)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  rcases
    onePoint_threeSpace_twoPointComplement_puncturedEuclidean_lowHomotopy_package
      hqp basepoint with
    ⟨ chart
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalGroupSubsingleton
    , piOneSubsingleton
    , pathNonempty
    , pathComponentEqUniv
    ⟩
  exact
    ⟨ chart
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalGroupSubsingleton
    , piOneSubsingleton
    , fun x y => Subsingleton.elim (ZerothHomotopy.mk x) (ZerothHomotopy.mk y)
    , fun a b => Subsingleton.elim a b
    , fun a b => Subsingleton.elim a b
    , fun a b => Subsingleton.elim a b
    , ⟨ ZerothHomotopy.mk basepoint
      , fun homotopyClass =>
          Subsingleton.elim homotopyClass (ZerothHomotopy.mk basepoint)⟩
    , ⟨ default
      , fun homotopyClass => Subsingleton.elim homotopyClass default⟩
    , ⟨ default
      , fun fundamentalClass => Subsingleton.elim fundamentalClass default⟩
    , ⟨ default
      , fun homotopyClass => Subsingleton.elim homotopyClass default⟩
    , pathNonempty
    , pathComponentEqUniv
    ⟩

/--
The two-point compactification complement package is available uniformly at
every supplied basepoint.  This all-basepoint consumer form is the endpoint
needed by topology extraction routes that quantify over puncture-complement
basepoints instead of selecting one basepoint before opening the low-homotopy
collapse data.
-/
theorem onePoint_threeSpace_twoPointComplement_all_basepoint_lowHomotopy_baseclass_collapse_package
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty
          ((({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
            ({onePoint_threeSpace_compl_singleton_homeomorph_euclidean p
                (onePoint_threeSpace_pointInComplement hqp)}ᶜ :
              Set (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        LocPathConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ x y :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk x = ZerothHomotopy.mk y) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ x y :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path x y)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  intro basepoint
  exact
    onePoint_threeSpace_twoPointComplement_lowHomotopy_baseclass_collapse_package
      hqp basepoint

/--
A recognized one-point compactification source has the same all-basepoint
two-puncture complement collapse package as the model compactification.  The
transported punctured-Euclidean chart supplies path connectedness,
connectedness, simple connectedness, local path connectedness, all low-homotopy
subsingleton fields, equality eliminators, named base classes, and
path-component collapse for every supplied basepoint of the two-point
complement.
-/
theorem twoPointComplement_recognition_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = baseClass) ∧
        (∃ baseClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ fundamentalClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = baseClass) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
        (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ) := by
  intro basepoint
  rcases
    exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
      h hyx with
    ⟨puncture, ⟨chart⟩⟩
  let source := (({x} ∪ {y})ᶜ : Set M)
  let target := ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))
  letI : PathConnectedSpace target :=
    euclideanThree_compl_singleton_pathConnectedSpace puncture
  letI : ConnectedSpace target := inferInstance
  letI : SimplyConnectedSpace target :=
    euclideanThree_compl_singleton_simplyConnectedSpace puncture
  letI : LocPathConnectedSpace target :=
    (euclideanThree_compl_singleton_isOpenEmbedding puncture).locPathConnectedSpace
  letI : PathConnectedSpace source :=
    chart.symm.surjective.pathConnectedSpace chart.symm.continuous
  letI : ConnectedSpace source := inferInstance
  letI : Nonempty source := inferInstance
  letI : SimplyConnectedSpace source :=
    chart.toHomotopyEquiv.simplyConnectedSpace
  letI : LocPathConnectedSpace source :=
    chart.isOpenEmbedding.locPathConnectedSpace
  letI : Subsingleton (ZerothHomotopy source) := inferInstance
  letI : Subsingleton (HomotopyGroup.Pi 0 source basepoint) :=
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := source) (x := basepoint)).subsingleton_congr).mpr inferInstance
  letI : Subsingleton (FundamentalGroup source basepoint) := by
    change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
    infer_instance
  letI : Subsingleton (HomotopyGroup.Pi 1 source basepoint) :=
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := source) (x := basepoint)).subsingleton_congr).mpr inferInstance
  exact
    ⟨ ⟨puncture, ⟨chart⟩⟩
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , fun z w => Subsingleton.elim (ZerothHomotopy.mk z) (ZerothHomotopy.mk w)
    , fun a b => Subsingleton.elim a b
    , fun a b => Subsingleton.elim a b
    , fun a b => Subsingleton.elim a b
    , ⟨ ZerothHomotopy.mk basepoint
      , fun homotopyClass =>
          Subsingleton.elim homotopyClass (ZerothHomotopy.mk basepoint)⟩
    , ⟨ default
      , fun homotopyClass => Subsingleton.elim homotopyClass default⟩
    , ⟨ default
      , fun fundamentalClass => Subsingleton.elim fundamentalClass default⟩
    , ⟨ default
      , fun homotopyClass => Subsingleton.elim homotopyClass default⟩
    , fun z w => PathConnectedSpace.joined z w
    , fun z => by
        ext w
        constructor
        · intro _hw
          exact Set.mem_univ w
        · intro _hw
          exact PathConnectedSpace.joined z w
    ⟩

/--
Supplied-basepoint recognized-source form of the two-point complement collapse.
This opens the all-basepoint package into named punctured-Euclidean chart data,
named collapsed base classes for `π₀`, the fundamental group, and `π₁`, plus the
path and path-component collapse fields at the chosen basepoint.
-/
theorem twoPointComplement_recognition_supplied_basepoint_named_baseclass_collapse_package_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
    ∃ _chart :
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
    ∃ zerothBaseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
    ∃ piZeroBaseClass :
      HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
    ∃ fundamentalBaseClass :
      FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
    ∃ piOneBaseClass :
      HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
      Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = zerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = piZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          fundamentalClass = fundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = piOneBaseClass) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
        (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ) := by
  rcases
    twoPointComplement_recognition_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint with
    ⟨ punctureChart
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalGroupSubsingleton
    , piOneSubsingleton
    , zerothEq
    , piZeroEq
    , fundamentalGroupEq
    , piOneEq
    , ⟨zerothBaseClass, zerothBaseClass_eq⟩
    , ⟨piZeroBaseClass, piZeroBaseClass_eq⟩
    , ⟨fundamentalBaseClass, fundamentalBaseClass_eq⟩
    , ⟨piOneBaseClass, piOneBaseClass_eq⟩
    , pathNonempty
    , pathComponentEq
    ⟩
  rcases punctureChart with ⟨puncture, chart⟩
  exact
    ⟨ puncture
    , chart
    , zerothBaseClass
    , piZeroBaseClass
    , fundamentalBaseClass
    , piOneBaseClass
    , nonempty
    , pathConnected
    , connected
    , simplyConnected
    , locPathConnected
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalGroupSubsingleton
    , piOneSubsingleton
    , zerothEq
    , piZeroEq
    , fundamentalGroupEq
    , piOneEq
    , zerothBaseClass_eq
    , piZeroBaseClass_eq
    , fundamentalBaseClass_eq
    , piOneBaseClass_eq
    , pathNonempty
    , pathComponentEq
    ⟩

/--
Sphere-recognized sources inherit the same all-basepoint two-puncture
collapse package by first converting the sphere recognition to the one-point
compactification route.  This is the topology-extraction-facing bridge for
consumers whose recognition output is stated as a `ThreeSphere`
homeomorphism.
-/
theorem twoPointComplement_recognition_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere))
    {x y : M} (hyx : y ≠ x) :
    ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = baseClass) ∧
        (∃ baseClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ fundamentalClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = baseClass) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
        (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ) :=
  twoPointComplement_recognition_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Supplied-basepoint version of the sphere-recognized two-puncture collapse
bridge.  It opens the all-basepoint package at the chosen basepoint and names
the punctured-Euclidean chart and collapsed base classes.
-/
theorem twoPointComplement_recognition_supplied_basepoint_named_baseclass_collapse_package_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
    ∃ _chart :
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
    ∃ zerothBaseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
    ∃ piZeroBaseClass :
      HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
    ∃ fundamentalBaseClass :
      FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
    ∃ piOneBaseClass :
      HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
      Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = zerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = piZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          fundamentalClass = fundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = piOneBaseClass) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
        (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ) :=
  twoPointComplement_recognition_supplied_basepoint_named_baseclass_collapse_package_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint

/--
Uniform all-distinct-pairs version of the sphere-recognized two-puncture
collapse bridge.  Topology-extraction consumers can quantify over every
ordered pair of distinct points and still obtain the full all-basepoint
low-homotopy/baseclass collapse package for the complement.
-/
theorem twoPointComplement_recognition_all_distinct_points_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∀ x y : M,
    ∀ _hyx : y ≠ x,
    ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = baseClass) ∧
        (∃ baseClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ fundamentalClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = baseClass) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
        (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ) := by
  intro x y hyx
  exact
    twoPointComplement_recognition_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_threeSphere
      h hyx

/--
One `ThreeSphere` recognition witness supplies both complement families needed
by topology extraction: every singleton complement is Euclidean, contractible,
and locally path connected, while every ordered pair of distinct punctures has
the full two-puncture low-homotopy/baseclass collapse package at every
basepoint.  This keeps the one-puncture and two-puncture routes synchronized
under the same recognition input.
-/
theorem threeSphere_recognition_singleton_topology_and_twoPoint_lowHomotopy_collapse_families
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    (∀ x : M,
      Nonempty (M ≃ₜ ThreeSphere) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        PathConnectedSpace ({x}ᶜ : Set M) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        LocPathConnectedSpace ({x}ᶜ : Set M)) ∧
      (∀ x y : M,
      ∀ _hyx : y ≠ x,
      ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
          Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
          PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
          Subsingleton
            (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
          Subsingleton
            (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
          (∀ z w : (({x} ∪ {y})ᶜ : Set M),
            ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
          (∀ a b :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
            a = b) ∧
          (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
            a = b) ∧
          (∀ a b :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
            a = b) ∧
          (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
            ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
            homotopyClass = baseClass) ∧
          (∃ baseClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
            homotopyClass = baseClass) ∧
          (∃ baseClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
            ∀ fundamentalClass :
              FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
            fundamentalClass = baseClass) ∧
          (∃ baseClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
            homotopyClass = baseClass) ∧
          (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
          (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ)) := by
  constructor
  · intro x
    let source := ({x}ᶜ : Set M)
    let chart :=
      homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
        h x
    letI : ContractibleSpace source := chart.contractibleSpace
    letI : Nonempty source := inferInstance
    letI : PathConnectedSpace source := inferInstance
    letI : ConnectedSpace source := inferInstance
    letI : SimplyConnectedSpace source := inferInstance
    letI : LocPathConnectedSpace source := chart.isOpenEmbedding.locPathConnectedSpace
    exact
      ⟨ h
      , homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h
      , ⟨chart⟩
      , inferInstance
      , inferInstance
      , inferInstance
      , inferInstance
      , inferInstance
      , inferInstance
      ⟩
  · exact
      twoPointComplement_recognition_all_distinct_points_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_threeSphere
        h

/--
Fixed-target opened form of the synchronized singleton/two-puncture topology
route.  A single `ThreeSphere` recognition witness names the singleton
Euclidean chart at `x` and the supplied-basepoint two-puncture chart/baseclass
collapse package for `{x,y}` simultaneously.
-/
theorem threeSphere_recognition_fixed_singleton_chart_and_twoPoint_named_baseclass_collapse_payload
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere))
    (x y : M) (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ singletonChart : (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)),
    ∃ twoPointPuncture : EuclideanSpace ℝ (Fin 3),
    ∃ _twoPointChart :
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({twoPointPuncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
    ∃ zerothBaseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
    ∃ piZeroBaseClass :
      HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
    ∃ fundamentalBaseClass :
      FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
    ∃ piOneBaseClass :
      HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
      singletonChart =
        homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
          h x ∧
        Nonempty (M ≃ₜ ThreeSphere) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        PathConnectedSpace ({x}ᶜ : Set M) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        LocPathConnectedSpace ({x}ᶜ : Set M) ∧
        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          a = b) ∧
        (∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = zerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = piZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          fundamentalClass = fundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
          homotopyClass = piOneBaseClass) ∧
        (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
        (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ) := by
  let singletonSource := ({x}ᶜ : Set M)
  let singletonChart :
      singletonSource ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
      h x
  letI : ContractibleSpace singletonSource := singletonChart.contractibleSpace
  letI : Nonempty singletonSource := inferInstance
  letI : PathConnectedSpace singletonSource := inferInstance
  letI : ConnectedSpace singletonSource := inferInstance
  letI : SimplyConnectedSpace singletonSource := inferInstance
  letI : LocPathConnectedSpace singletonSource :=
    singletonChart.isOpenEmbedding.locPathConnectedSpace
  rcases
    twoPointComplement_recognition_supplied_basepoint_named_baseclass_collapse_package_of_homeomorph_to_threeSphere
      h hyx basepoint with
    ⟨ twoPointPuncture
    , twoPointChart
    , zerothBaseClass
    , piZeroBaseClass
    , fundamentalBaseClass
    , piOneBaseClass
    , twoPointNonempty
    , twoPointPathConnected
    , twoPointConnected
    , twoPointSimplyConnected
    , twoPointLocPathConnected
    , twoPointZerothSubsingleton
    , twoPointPiZeroSubsingleton
    , twoPointFundamentalSubsingleton
    , twoPointPiOneSubsingleton
    , twoPointZerothEq
    , twoPointPiZeroEq
    , twoPointFundamentalEq
    , twoPointPiOneEq
    , twoPointZerothBaseClassEq
    , twoPointPiZeroBaseClassEq
    , twoPointFundamentalBaseClassEq
    , twoPointPiOneBaseClassEq
    , twoPointPathNonempty
    , twoPointPathComponentEq
    ⟩
  exact
    ⟨ singletonChart
    , twoPointPuncture
    , twoPointChart
    , zerothBaseClass
    , piZeroBaseClass
    , fundamentalBaseClass
    , piOneBaseClass
    , rfl
    , h
    , homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h
    , ⟨singletonChart⟩
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , twoPointNonempty
    , twoPointPathConnected
    , twoPointConnected
    , twoPointSimplyConnected
    , twoPointLocPathConnected
    , twoPointZerothSubsingleton
    , twoPointPiZeroSubsingleton
    , twoPointFundamentalSubsingleton
    , twoPointPiOneSubsingleton
    , twoPointZerothEq
    , twoPointPiZeroEq
    , twoPointFundamentalEq
    , twoPointPiOneEq
    , twoPointZerothBaseClassEq
    , twoPointPiZeroBaseClassEq
    , twoPointFundamentalBaseClassEq
    , twoPointPiOneBaseClassEq
    , twoPointPathNonempty
    , twoPointPathComponentEq
    ⟩

/--
Uniform fixed-singleton/two-puncture payload.  This keeps the concrete
singleton Euclidean chart at `x` synchronized with the all-basepoint
two-puncture low-homotopy collapse route for `{x,y}`.
-/
theorem threeSphere_recognition_fixed_singleton_chart_and_twoPoint_all_basepoint_lowHomotopy_collapse_payload
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere))
    (x y : M) (hyx : y ≠ x) :
    ∃ singletonChart : (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)),
      singletonChart =
        homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
          h x ∧
        Nonempty (M ≃ₜ ThreeSphere) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        PathConnectedSpace ({x}ᶜ : Set M) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        LocPathConnectedSpace ({x}ᶜ : Set M) ∧
        (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
            Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
            PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
            Subsingleton
              (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
            Subsingleton
              (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
            (∀ z w : (({x} ∪ {y})ᶜ : Set M),
              ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
            (∀ a b :
              HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
              a = b) ∧
            (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
              a = b) ∧
            (∀ a b :
              HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
              a = b) ∧
            (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
              ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
              homotopyClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
              homotopyClass = baseClass) ∧
            (∃ baseClass :
              FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
              ∀ fundamentalClass :
                FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
              fundamentalClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
              homotopyClass = baseClass) ∧
            (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
            (∀ z : (({x} ∪ {y})ᶜ : Set M), pathComponent z = Set.univ)) := by
  let singletonSource := ({x}ᶜ : Set M)
  let singletonChart :
      singletonSource ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
      h x
  letI : ContractibleSpace singletonSource := singletonChart.contractibleSpace
  letI : Nonempty singletonSource := inferInstance
  letI : PathConnectedSpace singletonSource := inferInstance
  letI : ConnectedSpace singletonSource := inferInstance
  letI : SimplyConnectedSpace singletonSource := inferInstance
  letI : LocPathConnectedSpace singletonSource :=
    singletonChart.isOpenEmbedding.locPathConnectedSpace
  exact
    ⟨ singletonChart
    , rfl
    , h
    , homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h
    , ⟨singletonChart⟩
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , twoPointComplement_recognition_all_basepoint_lowHomotopy_baseclass_collapse_package_of_homeomorph_to_threeSphere
        h hyx
    ⟩

/--
Family-level opened form of the synchronized singleton/two-puncture route.
For every selected singleton puncture it names the Euclidean singleton chart
once, then retains the supplied-basepoint two-puncture chart and collapsed
base classes for every distinct second puncture and every basepoint in the
two-puncture complement.
-/
theorem threeSphere_recognition_all_singleton_chart_and_all_twoPoint_named_baseclass_collapse_payload
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∀ x : M,
    ∃ singletonChart : (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)),
      singletonChart =
        homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
          h x ∧
        Nonempty (M ≃ₜ ThreeSphere) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        PathConnectedSpace ({x}ᶜ : Set M) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        LocPathConnectedSpace ({x}ᶜ : Set M) ∧
        (∀ y : M,
        ∀ _hyx : y ≠ x,
        ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
          ∃ twoPointPuncture : EuclideanSpace ℝ (Fin 3),
          ∃ _twoPointChart :
            Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
              ({twoPointPuncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
          ∃ zerothBaseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          ∃ piZeroBaseClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∃ fundamentalBaseClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∃ piOneBaseClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
            Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
            PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            LocPathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) ∧
            Subsingleton
              (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
            Subsingleton
              (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) ∧
            (∀ z w : (({x} ∪ {y})ᶜ : Set M),
              ZerothHomotopy.mk z = ZerothHomotopy.mk w) ∧
            (∀ a b :
              HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
              a = b) ∧
            (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
              a = b) ∧
            (∀ a b :
              HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
              a = b) ∧
            (∀ homotopyClass :
              ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
              homotopyClass = zerothBaseClass) ∧
            (∀ homotopyClass :
              HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
              homotopyClass = piZeroBaseClass) ∧
            (∀ fundamentalClass :
              FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
              fundamentalClass = fundamentalBaseClass) ∧
            (∀ homotopyClass :
              HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
              homotopyClass = piOneBaseClass) ∧
            (∀ z w : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path z w)) ∧
            (∀ z : (({x} ∪ {y})ᶜ : Set M),
              pathComponent z = Set.univ)) := by
  intro x
  let singletonSource := ({x}ᶜ : Set M)
  let singletonChart :
      singletonSource ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
      h x
  letI : ContractibleSpace singletonSource := singletonChart.contractibleSpace
  letI : Nonempty singletonSource := inferInstance
  letI : PathConnectedSpace singletonSource := inferInstance
  letI : ConnectedSpace singletonSource := inferInstance
  letI : SimplyConnectedSpace singletonSource := inferInstance
  letI : LocPathConnectedSpace singletonSource :=
    singletonChart.isOpenEmbedding.locPathConnectedSpace
  refine
    ⟨ singletonChart
    , rfl
    , h
    , homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h
    , ⟨singletonChart⟩
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , ?_
    ⟩
  intro y hyx basepoint
  rcases
    twoPointComplement_recognition_supplied_basepoint_named_baseclass_collapse_package_of_homeomorph_to_threeSphere
      h hyx basepoint with
    ⟨ twoPointPuncture
    , twoPointChart
    , zerothBaseClass
    , piZeroBaseClass
    , fundamentalBaseClass
    , piOneBaseClass
    , twoPointNonempty
    , twoPointPathConnected
    , twoPointConnected
    , twoPointSimplyConnected
    , twoPointLocPathConnected
    , twoPointZerothSubsingleton
    , twoPointPiZeroSubsingleton
    , twoPointFundamentalSubsingleton
    , twoPointPiOneSubsingleton
    , twoPointZerothEq
    , twoPointPiZeroEq
    , twoPointFundamentalEq
    , twoPointPiOneEq
    , twoPointZerothBaseClassEq
    , twoPointPiZeroBaseClassEq
    , twoPointFundamentalBaseClassEq
    , twoPointPiOneBaseClassEq
    , twoPointPathNonempty
    , twoPointPathComponentEq
    ⟩
  exact
    ⟨ twoPointPuncture
    , twoPointChart
    , zerothBaseClass
    , piZeroBaseClass
    , fundamentalBaseClass
    , piOneBaseClass
    , twoPointNonempty
    , twoPointPathConnected
    , twoPointConnected
    , twoPointSimplyConnected
    , twoPointLocPathConnected
    , twoPointZerothSubsingleton
    , twoPointPiZeroSubsingleton
    , twoPointFundamentalSubsingleton
    , twoPointPiOneSubsingleton
    , twoPointZerothEq
    , twoPointPiZeroEq
    , twoPointFundamentalEq
    , twoPointPiOneEq
    , twoPointZerothBaseClassEq
    , twoPointPiZeroBaseClassEq
    , twoPointFundamentalBaseClassEq
    , twoPointPiOneBaseClassEq
    , twoPointPathNonempty
    , twoPointPathComponentEq
    ⟩

end Poincare
