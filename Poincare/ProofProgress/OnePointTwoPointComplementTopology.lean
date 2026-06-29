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

end Poincare
