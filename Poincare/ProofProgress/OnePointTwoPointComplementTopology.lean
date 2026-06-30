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
Any two points in the two-point complement are joined by a path.
-/
theorem onePoint_threeSpace_twoPointComplement_path_nonempty
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ (x y : (({p} ∪ {q})ᶜ :
      Set (OnePoint (EuclideanSpace ℝ (Fin 3))))),
        Nonempty (Path x y) := by
  intro x y
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  exact PathConnectedSpace.joined x y

/--
The path component of any point in the two-point complement is the whole
two-point complement.
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
The zeroth homotopy quotient of the two-point complement has only one class.
-/
theorem onePoint_threeSpace_twoPointComplement_zerothHomotopy_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    Subsingleton
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  infer_instance

/--
The zeroth homotopy group formulation of the two-point complement collapse.
-/
theorem onePoint_threeSpace_twoPointComplement_piZero_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := (({p} ∪ {q})ᶜ :
        Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := x)).subsingleton_congr).mpr
        (onePoint_threeSpace_twoPointComplement_zerothHomotopy_subsingleton hqp)

/--
Any two zeroth homotopy group classes in the two-point complement agree.
-/
theorem onePoint_threeSpace_twoPointComplement_piZero_eq
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (a b :
      HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :
    a = b := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_twoPointComplement_piZero_subsingleton hqp x
  exact Subsingleton.elim _ _

/--
The zeroth homotopy group of the two-point complement has a unique class.
-/
theorem onePoint_threeSpace_twoPointComplement_piZero_exists_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ baseClass :
      HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
      ∀ homotopyClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_twoPointComplement_piZero_subsingleton hqp x
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
Any two based fundamental-group classes in the two-point complement agree.
-/
theorem onePoint_threeSpace_twoPointComplement_fundamentalGroup_eq
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (a b : FundamentalGroup
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :
    a = b := by
  letI : Subsingleton
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton hqp x
  exact Subsingleton.elim _ _

/--
The based fundamental group of the two-point complement has a unique class.
-/
theorem onePoint_threeSpace_twoPointComplement_fundamentalGroup_exists_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ baseClass :
      FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
      ∀ fundamentalClass :
        FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
        fundamentalClass = baseClass := by
  letI : Subsingleton
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton hqp x
  exact ⟨Classical.choice inferInstance, fun fundamentalClass => Subsingleton.elim _ _⟩

/--
The first homotopy group formulation of the two-point complement fundamental
group collapse.
-/
theorem onePoint_threeSpace_twoPointComplement_piOne_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton (HomotopyGroup.Pi 1
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := (({p} ∪ {q})ᶜ :
        Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := x)).subsingleton_congr).mpr
        (onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton
          hqp x)

/--
Any two first homotopy group classes in the two-point complement agree.
-/
theorem onePoint_threeSpace_twoPointComplement_piOne_eq
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (a b :
      HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :
    a = b := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_twoPointComplement_piOne_subsingleton hqp x
  exact Subsingleton.elim _ _

/--
The first homotopy group of the two-point complement has a unique class.
-/
theorem onePoint_threeSpace_twoPointComplement_piOne_exists_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ baseClass :
      HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
      ∀ homotopyClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_twoPointComplement_piOne_subsingleton hqp x
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
Any two zeroth-homotopy classes in the two-point complement agree.
-/
theorem onePoint_threeSpace_twoPointComplement_zerothHomotopy_mk_eq
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (x y : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ZerothHomotopy.mk x = ZerothHomotopy.mk y := by
  letI : Subsingleton
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    onePoint_threeSpace_twoPointComplement_zerothHomotopy_subsingleton hqp
  exact Subsingleton.elim _ _

/--
The zeroth homotopy quotient of the two-point complement has a unique class.
-/
theorem onePoint_threeSpace_twoPointComplement_zerothHomotopy_exists_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ baseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∀ homotopyClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        homotopyClass = baseClass := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  let basePoint : (({p} ∪ {q})ᶜ :
      Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (PathConnectedSpace.nonempty
        (X := (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))))
  exact ⟨ZerothHomotopy.mk basePoint, fun homotopyClass => Subsingleton.elim _ _⟩

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
Concrete model-level two-puncture collapse package for the one-point
compactification of `ℝ³`: a punctured-Euclidean chart, simple connectedness,
connectedness/nonemptiness, collapsed low homotopy groups, unique classes, and
path-component collapse.
-/
theorem onePoint_threeSpace_twoPointComplement_collapse_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    (∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty
        ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∃ baseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        ∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) :=
  ⟨ ⟨ onePoint_threeSpace_compl_singleton_homeomorph_euclidean p
          (onePoint_threeSpace_pointInComplement hqp)
      , ⟨onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean
          hqp⟩ ⟩
  , onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hqp
  , onePoint_threeSpace_twoPointComplement_connectedSpace hqp
  , onePoint_threeSpace_twoPointComplement_nonempty hqp
  , onePoint_threeSpace_twoPointComplement_piZero_subsingleton hqp basepoint
  , onePoint_threeSpace_twoPointComplement_piOne_subsingleton hqp basepoint
  , onePoint_threeSpace_twoPointComplement_zerothHomotopy_mk_eq hqp
  , onePoint_threeSpace_twoPointComplement_piZero_eq hqp basepoint
  , onePoint_threeSpace_twoPointComplement_fundamentalGroup_eq hqp basepoint
  , onePoint_threeSpace_twoPointComplement_piOne_eq hqp basepoint
  , onePoint_threeSpace_twoPointComplement_zerothHomotopy_exists_unique hqp
  , onePoint_threeSpace_twoPointComplement_piZero_exists_unique hqp basepoint
  , onePoint_threeSpace_twoPointComplement_fundamentalGroup_exists_unique
      hqp basepoint
  , onePoint_threeSpace_twoPointComplement_piOne_exists_unique hqp basepoint
  , onePoint_threeSpace_twoPointComplement_path_nonempty hqp
  , onePoint_threeSpace_twoPointComplement_pathComponent_eq_univ hqp
  ⟩

/--
The zeroth homotopy quotient of the one-point model two-puncture complement is
a `Unique` type.
-/
@[reducible] noncomputable def onePoint_threeSpace_twoPointComplement_zerothHomotopy_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    Unique
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) := by
  let witness :=
    onePoint_threeSpace_twoPointComplement_zerothHomotopy_exists_unique hqp
  exact
    { default := Classical.choose witness
      uniq := fun homotopyClass =>
        Classical.choose_spec witness homotopyClass }

/--
The zeroth homotopy group of the one-point model two-puncture complement is a
`Unique` type at every basepoint.
-/
@[reducible] noncomputable def onePoint_threeSpace_twoPointComplement_piZero_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Unique
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  let witness :=
    onePoint_threeSpace_twoPointComplement_piZero_exists_unique hqp basepoint
  exact
    { default := Classical.choose witness
      uniq := fun homotopyClass =>
        Classical.choose_spec witness homotopyClass }

/--
The fundamental group of the one-point model two-puncture complement is a
`Unique` type at every basepoint.
-/
@[reducible] noncomputable def onePoint_threeSpace_twoPointComplement_fundamentalGroup_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Unique
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  let witness :=
    onePoint_threeSpace_twoPointComplement_fundamentalGroup_exists_unique
      hqp basepoint
  exact
    { default := Classical.choose witness
      uniq := fun fundamentalClass =>
        Classical.choose_spec witness fundamentalClass }

/--
The first homotopy group of the one-point model two-puncture complement is a
`Unique` type at every basepoint.
-/
@[reducible] noncomputable def onePoint_threeSpace_twoPointComplement_piOne_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Unique
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) := by
  let witness :=
    onePoint_threeSpace_twoPointComplement_piOne_exists_unique hqp basepoint
  exact
    { default := Classical.choose witness
      uniq := fun homotopyClass =>
        Classical.choose_spec witness homotopyClass }

/--
Data-valued unique-instance form of the one-point compactification model
two-puncture low-homotopy collapse, including connectedness, nonemptiness, and
path-component collapse.
-/
structure OnePointTwoPointComplementLowHomotopyUniquePayload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) where
  connected :
    ConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  nonempty :
    Nonempty
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  zerothUnique :
    Unique
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
  piZeroUnique :
    Unique
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint)
  fundamentalGroupUnique :
    Unique
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint)
  piOneUnique :
    Unique
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint)
  pathNonempty :
    ∀ a b :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)
  pathComponentEqUniv :
    ∀ point :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent point = Set.univ

/--
Unique-instance payload for the one-point compactification model two-puncture
collapse.  This gives downstream topology extraction a field-based object for
the model complement rather than a large tuple of individual collapse facts.
-/
noncomputable def onePoint_threeSpace_twoPointComplement_lowHomotopyUnique_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    OnePointTwoPointComplementLowHomotopyUniquePayload hqp basepoint where
  connected := onePoint_threeSpace_twoPointComplement_connectedSpace hqp
  nonempty := onePoint_threeSpace_twoPointComplement_nonempty hqp
  zerothUnique :=
    onePoint_threeSpace_twoPointComplement_zerothHomotopy_unique hqp
  piZeroUnique :=
    onePoint_threeSpace_twoPointComplement_piZero_unique hqp basepoint
  fundamentalGroupUnique :=
    onePoint_threeSpace_twoPointComplement_fundamentalGroup_unique
      hqp basepoint
  piOneUnique :=
    onePoint_threeSpace_twoPointComplement_piOne_unique hqp basepoint
  pathNonempty := onePoint_threeSpace_twoPointComplement_path_nonempty hqp
  pathComponentEqUniv :=
    onePoint_threeSpace_twoPointComplement_pathComponent_eq_univ hqp

/--
Recognition-facing payload for the one-point compactification model
two-puncture complement: a concrete punctured-Euclidean chart, simple
connectedness, and the complete low-homotopy uniqueness payload.
-/
structure OnePointTwoPointComplementRecognitionPayload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) where
  puncturedEuclideanChart :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty
        ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))
  simplyConnected :
    SimplyConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  lowHomotopy :
    OnePointTwoPointComplementLowHomotopyUniquePayload hqp basepoint

/--
The one-point model two-puncture complement provides the chart, simple
connectedness, and low-homotopy uniqueness data needed by recognition
consumers in one field-based object.
-/
noncomputable def onePoint_threeSpace_twoPointComplement_recognition_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    OnePointTwoPointComplementRecognitionPayload hqp basepoint where
  puncturedEuclideanChart :=
    ⟨ onePoint_threeSpace_compl_singleton_homeomorph_euclidean p
        (onePoint_threeSpace_pointInComplement hqp)
    , ⟨onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean
        hqp⟩ ⟩
  simplyConnected :=
    onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hqp
  lowHomotopy :=
    onePoint_threeSpace_twoPointComplement_lowHomotopyUnique_payload
      hqp basepoint

/--
Tuple form of the one-point model recognition payload for theorem consumers
that do not want to destruct the structure.
-/
theorem onePoint_threeSpace_twoPointComplement_recognition_payload_tuple
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    (∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty
        ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        (OnePointTwoPointComplementLowHomotopyUniquePayload hqp basepoint) :=
  let payload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload
      hqp basepoint
  ⟨ payload.puncturedEuclideanChart
  , payload.simplyConnected
  , ⟨payload.lowHomotopy⟩ ⟩

/--
Flat recognition certificate for the one-point model two-puncture complement.
This expands the field-based recognition object into the exact topological and
low-homotopy witnesses that downstream recognition code typically consumes.
-/
structure OnePointTwoPointComplementFlatRecognitionPayload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) where
  puncturedEuclideanChart :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty
        ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))
  simplyConnected :
    SimplyConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  connected :
    ConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  nonempty :
    Nonempty
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  zerothUnique :
    Unique
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
  piZeroUnique :
    Unique
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint)
  fundamentalGroupUnique :
    Unique
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint)
  piOneUnique :
    Unique
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint)
  pathNonempty :
    ∀ a b :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)
  pathComponentEqUniv :
    ∀ point :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent point = Set.univ

/--
The field-based recognition payload discharges the flat topological certificate
without reusing the larger legacy tuple.
-/
noncomputable def onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementRecognitionPayload hqp basepoint) :
    OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint where
  puncturedEuclideanChart := payload.puncturedEuclideanChart
  simplyConnected := payload.simplyConnected
  connected := payload.lowHomotopy.connected
  nonempty := payload.lowHomotopy.nonempty
  zerothUnique := payload.lowHomotopy.zerothUnique
  piZeroUnique := payload.lowHomotopy.piZeroUnique
  fundamentalGroupUnique := payload.lowHomotopy.fundamentalGroupUnique
  piOneUnique := payload.lowHomotopy.piOneUnique
  pathNonempty := payload.lowHomotopy.pathNonempty
  pathComponentEqUniv := payload.lowHomotopy.pathComponentEqUniv

/--
Flattening a structured two-puncture recognition payload preserves every
field by definition.  Downstream consumers can therefore move from the
structured payload to the flat recognition payload while keeping the same
punctured-Euclidean chart, simple connectedness, low-homotopy uniqueness, path
witnesses, and path-component collapse data.
-/
theorem onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementRecognitionPayload hqp basepoint) :
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          payload ∧
        flatPayload.puncturedEuclideanChart =
          payload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = payload.simplyConnected ∧
        flatPayload.connected = payload.lowHomotopy.connected ∧
        flatPayload.nonempty = payload.lowHomotopy.nonempty ∧
        flatPayload.zerothUnique = payload.lowHomotopy.zerothUnique ∧
        flatPayload.piZeroUnique = payload.lowHomotopy.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          payload.lowHomotopy.fundamentalGroupUnique ∧
        flatPayload.piOneUnique = payload.lowHomotopy.piOneUnique ∧
        flatPayload.pathNonempty = payload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          payload.lowHomotopy.pathComponentEqUniv := by
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      payload
  exact
    ⟨ flatPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    ⟩

/--
The flat two-puncture recognition payload reconstructs path-connectedness from
its stored nonempty witness and explicit paths between all pairs of points.
-/
theorem onePoint_threeSpace_twoPointComplement_pathConnectedSpace_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) where
  nonempty := payload.nonempty
  joined := payload.pathNonempty

/--
The flat two-puncture recognition payload directly supplies connectedness.
-/
theorem onePoint_threeSpace_twoPointComplement_connectedSpace_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    ConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  payload.connected

/--
The flat two-puncture recognition payload directly supplies nonemptiness.
-/
theorem onePoint_threeSpace_twoPointComplement_nonempty_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    Nonempty
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  payload.nonempty

/--
The flat recognition payload reconstructs the ordinary topology facts needed
before the low-homotopy collapse package is consumed.
-/
theorem onePoint_threeSpace_twoPointComplement_ordinaryTopology_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  ⟨onePoint_threeSpace_twoPointComplement_nonempty_of_flatRecognition payload,
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace_of_flatRecognition payload,
    onePoint_threeSpace_twoPointComplement_connectedSpace_of_flatRecognition payload⟩

/--
The flat recognition payload exposes the low-homotopy collapse surface without
forcing consumers to unpack the larger legacy collapse tuple.
-/
theorem onePoint_threeSpace_twoPointComplement_lowHomotopy_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty (Unique
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) :=
  ⟨payload.simplyConnected, ⟨payload.zerothUnique⟩, ⟨payload.piZeroUnique⟩,
    ⟨payload.fundamentalGroupUnique⟩, ⟨payload.piOneUnique⟩,
    payload.pathNonempty, payload.pathComponentEqUniv⟩

/--
The flat recognition payload also exposes direct subsingleton facts for the
low-homotopy objects at the retained basepoint.  This is the compact
consumer-facing form for code that needs collapse facts rather than chosen
`Unique` instances.
-/
theorem onePoint_threeSpace_twoPointComplement_lowHomotopy_subsingleton_package_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    Subsingleton
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) := by
  letI : Unique
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    payload.zerothUnique
  letI : Unique
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.piZeroUnique
  letI : Unique
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.fundamentalGroupUnique
  letI : Unique
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.piOneUnique
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/--
The flat recognition payload exposes the ordinary topology and low-homotopy
collapse surface together, so downstream topology extraction can consume one
endpoint instead of recombining separate path-connected and homotopy packages.
-/
theorem onePoint_threeSpace_twoPointComplement_topology_and_lowHomotopy_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty (Unique
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint)) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  rcases
    onePoint_threeSpace_twoPointComplement_ordinaryTopology_of_flatRecognition
      payload with
    ⟨hNonempty, hPathConnected, hConnected⟩
  rcases
    onePoint_threeSpace_twoPointComplement_lowHomotopy_of_flatRecognition
      payload with
    ⟨hSimplyConnected, hZeroth, hPiZero, hFundamentalGroup, hPiOne,
      hPathNonempty, hPathComponent⟩
  exact
    ⟨ hNonempty
    , hPathConnected
    , hConnected
    , hSimplyConnected
    , hZeroth
    , hPiZero
    , hFundamentalGroup
    , hPiOne
    , hPathNonempty
    , hPathComponent
    ⟩

/--
The flat recognition payload exposes concrete low-homotopy equality
eliminators and chosen unique classes for the two-puncture complement.
-/
theorem onePoint_threeSpace_twoPointComplement_lowHomotopy_eq_package_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∃ baseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        ∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) := by
  letI : Unique
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    payload.zerothUnique
  letI : Unique
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.piZeroUnique
  letI : Unique
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.fundamentalGroupUnique
  letI : Unique
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.piOneUnique
  exact
    ⟨ fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , ⟨default, fun _homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun _homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun _fundamentalClass => Subsingleton.elim _ _⟩
    , ⟨default, fun _homotopyClass => Subsingleton.elim _ _⟩
    ⟩

/--
The flat recognition payload exposes ordinary topology together with both
forms of low-homotopy collapse: direct subsingleton instances and explicit
equality/unique-class eliminators.  This is the consumer-facing endpoint for
two-puncture topology extraction code that needs topology and low-homotopy
collapse facts from the same retained flat payload without destructing the
larger legacy collapse tuple.
-/
theorem onePoint_threeSpace_twoPointComplement_topology_lowHomotopy_subsingleton_and_eq_package_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∃ baseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        ∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  rcases
    onePoint_threeSpace_twoPointComplement_topology_and_lowHomotopy_of_flatRecognition
      payload with
    ⟨hNonempty, hPathConnected, hConnected, hSimplyConnected,
      _hZerothUnique, _hPiZeroUnique, _hFundamentalGroupUnique,
      _hPiOneUnique, hPathNonempty, hPathComponent⟩
  rcases
    onePoint_threeSpace_twoPointComplement_lowHomotopy_subsingleton_package_of_flatRecognition
      payload with
    ⟨hZerothSubsingleton, hPiZeroSubsingleton, hFundamentalGroupSubsingleton,
      hPiOneSubsingleton⟩
  rcases
    onePoint_threeSpace_twoPointComplement_lowHomotopy_eq_package_of_flatRecognition
      payload with
    ⟨hZerothEq, hPiZeroEq, hFundamentalGroupEq, hPiOneEq,
      hZerothUniqueClass, hPiZeroUniqueClass, hFundamentalGroupUniqueClass,
      hPiOneUniqueClass⟩
  exact
    ⟨ hNonempty
    , hPathConnected
    , hConnected
    , hSimplyConnected
    , hZerothSubsingleton
    , hPiZeroSubsingleton
    , hFundamentalGroupSubsingleton
    , hPiOneSubsingleton
    , hZerothEq
    , hPiZeroEq
    , hFundamentalGroupEq
    , hPiOneEq
    , hZerothUniqueClass
    , hPiZeroUniqueClass
    , hFundamentalGroupUniqueClass
    , hPiOneUniqueClass
    , hPathNonempty
    , hPathComponent
    ⟩

/--
The flat one-point two-puncture recognition payload discharges the legacy
collapse tuple, including the low-homotopy subsingleton and unique-class
conclusions, without reconstructing the punctured-Euclidean chart or path
connectivity route.
-/
theorem onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (payload : OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) :
    (∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty
        ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∃ baseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        ∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  letI : Unique
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    payload.zerothUnique
  letI : Unique
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.piZeroUnique
  letI : Unique
      (FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.fundamentalGroupUnique
  letI : Unique
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
    payload.piOneUnique
  exact
    ⟨ payload.puncturedEuclideanChart
    , payload.simplyConnected
    , payload.connected
    , payload.nonempty
    , inferInstance
    , inferInstance
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , ⟨default, fun _homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun _homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun _fundamentalClass => Subsingleton.elim _ _⟩
    , ⟨default, fun _homotopyClass => Subsingleton.elim _ _⟩
    , payload.pathNonempty
    , payload.pathComponentEqUniv
    ⟩

/--
Concrete flat certificate for the one-point compactification model
two-puncture complement.
-/
noncomputable def onePoint_threeSpace_twoPointComplement_flatRecognition_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint :=
  onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
    (onePoint_threeSpace_twoPointComplement_recognition_payload hqp basepoint)

/--
The flat two-puncture recognition payload is exactly the concrete
punctured-Euclidean chart, ordinary topology fields, unique low-homotopy
instances, and path-component collapse fields.  The reverse direction rebuilds
the field-based flat-recognition payload from those explicit witnesses.
-/
theorem nonempty_onePoint_threeSpace_twoPointComplement_flatRecognition_payload_iff_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} {hqp : q ≠ p}
    {basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))} :
    Nonempty (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) ↔
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty
          ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty (Unique
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent point = Set.univ) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.puncturedEuclideanChart
      , payload.simplyConnected
      , payload.connected
      , payload.nonempty
      , ⟨payload.zerothUnique⟩
      , ⟨payload.piZeroUnique⟩
      , ⟨payload.fundamentalGroupUnique⟩
      , ⟨payload.piOneUnique⟩
      , payload.pathNonempty
      , payload.pathComponentEqUniv
      ⟩
  · rintro
      ⟨ puncturedEuclideanChart
      , simplyConnected
      , connected
      , nonempty
      , ⟨zerothUnique⟩
      , ⟨piZeroUnique⟩
      , ⟨fundamentalGroupUnique⟩
      , ⟨piOneUnique⟩
      , pathNonempty
      , pathComponentEqUniv
      ⟩
    exact
      ⟨ { puncturedEuclideanChart := puncturedEuclideanChart
          simplyConnected := simplyConnected
          connected := connected
          nonempty := nonempty
          zerothUnique := zerothUnique
          piZeroUnique := piZeroUnique
          fundamentalGroupUnique := fundamentalGroupUnique
          piOneUnique := piOneUnique
          pathNonempty := pathNonempty
          pathComponentEqUniv := pathComponentEqUniv } ⟩

/--
The flat two-puncture recognition payload can be produced without an externally
chosen basepoint.  Nonemptiness of the two-point complement selects a
basepoint, and the full flat-recognition field package is exposed at that
selected point.
-/
theorem onePoint_threeSpace_twoPointComplement_flatRecognition_payload_with_basepoint
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty
        (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty (Unique
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent point = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let payload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload hqp
      basepoint
  exact
    ⟨ basepoint
    , ⟨payload⟩
    , (nonempty_onePoint_threeSpace_twoPointComplement_flatRecognition_payload_iff_fields
        (hqp := hqp) (basepoint := basepoint)).1 ⟨payload⟩
    ⟩

/--
The full legacy two-puncture collapse tuple can also be produced without an
externally chosen basepoint.  The basepoint is selected from the established
nonemptiness of the two-point complement, and all low-homotopy equality and
path-component collapse fields are returned at that selected point.
-/
theorem onePoint_threeSpace_twoPointComplement_collapse_payload_with_basepoint
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty
          ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  exact
    ⟨ basepoint
    , onePoint_threeSpace_twoPointComplement_collapse_payload hqp basepoint
    ⟩

/--
The selected two-puncture endpoint carries the flat-recognition payload and the
legacy collapse tuple at the same basepoint.  This synchronizes the concrete
punctured-Euclidean recognition data with the low-homotopy equality and
base-class collapse witnesses used by downstream topology extraction.
-/
theorem onePoint_threeSpace_twoPointComplement_flatRecognition_and_collapse_payload_with_basepoint
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty
        (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let payload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload hqp
      basepoint
  exact
    ⟨ basepoint
    , ⟨payload⟩
    , onePoint_threeSpace_twoPointComplement_collapse_payload hqp basepoint
    ⟩

/--
At an externally supplied two-puncture basepoint, the model endpoint retains
the whole recognition hierarchy: the structured recognition payload, its
flattened recognition payload, and the legacy collapse tuple all refer to the
same basepoint.  This is the supplied-basepoint companion to the selected
endpoint below.
-/
theorem onePoint_threeSpace_twoPointComplement_recognition_flatRecognition_and_collapse_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Nonempty
      (OnePointTwoPointComplementRecognitionPayload hqp basepoint) ∧
      Nonempty
        (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) ∧
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty
          ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∃ baseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        ∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ ⟨recognitionPayload⟩
    , ⟨flatPayload⟩
    , onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
        flatPayload
    ⟩

/--
The selected two-puncture endpoint retains the whole recognition hierarchy at
one basepoint: the structured recognition payload, its flattened recognition
payload, and the legacy collapse tuple all refer to the same selected point.
This lets downstream topology extraction consume whichever layer it needs
without reselecting basepoints or reconstructing the flat payload from the
structured payload.
-/
theorem onePoint_threeSpace_twoPointComplement_recognition_flatRecognition_and_collapse_payload_with_basepoint
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty
        (OnePointTwoPointComplementRecognitionPayload hqp basepoint) ∧
        Nonempty
          (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ basepoint
    , ⟨recognitionPayload⟩
    , ⟨flatPayload⟩
    , onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
        flatPayload
    ⟩

/--
At a supplied basepoint, the structured recognition hierarchy also exposes the
consumer-facing ordinary-topology and low-homotopy collapse endpoint.  This
lets recognition-level topology extraction callers use the retained structured
payload while obtaining the flat two-puncture topology, subsingleton, equality,
unique-class, path, and path-component data from one theorem.
-/
theorem onePoint_threeSpace_twoPointComplement_recognition_flatRecognition_and_topology_lowHomotopy_package
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Nonempty
      (OnePointTwoPointComplementRecognitionPayload hqp basepoint) ∧
      Nonempty
        (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) ∧
      Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Subsingleton
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
      Subsingleton
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        a = b) ∧
      (∃ baseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint,
        ∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          homotopyClass = baseClass) ∧
      (∀ a b :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty (Path a b)) ∧
      (∀ x :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        pathComponent x = Set.univ) := by
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ ⟨recognitionPayload⟩
    , ⟨flatPayload⟩
    , onePoint_threeSpace_twoPointComplement_topology_lowHomotopy_subsingleton_and_eq_package_of_flatRecognition
        flatPayload
    ⟩

/--
The selected-basepoint recognition endpoint exposes the same ordinary-topology
and low-homotopy collapse package as the supplied-basepoint endpoint, with the
basepoint chosen from the established nonemptiness of the two-puncture
complement.  This is the recognition-level one-point compactification route
for downstream consumers that should not make their own basepoint choice.
-/
theorem onePoint_threeSpace_twoPointComplement_recognition_flatRecognition_and_topology_lowHomotopy_package_with_basepoint
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty
        (OnePointTwoPointComplementRecognitionPayload hqp basepoint) ∧
        Nonempty
          (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  exact
    ⟨ basepoint
    , onePoint_threeSpace_twoPointComplement_recognition_flatRecognition_and_topology_lowHomotopy_package
        hqp basepoint
    ⟩

/--
The selected-basepoint recognition route can retain the actual structured
recognition payload and its flattened payload, not only their inhabited
wrappers.  The same selected flat payload then supplies the ordinary-topology
and low-homotopy collapse package used by recognition-level topology
extraction.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_flatRecognition_payload_and_topology_lowHomotopy_package
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , onePoint_threeSpace_twoPointComplement_topology_lowHomotopy_subsingleton_and_eq_package_of_flatRecognition
        flatPayload
    ⟩

/--
The selected-basepoint recognition route retains the actual structured
recognition payload and flattened payload while also exposing the legacy
collapse tuple produced from that same flattened payload.  This keeps the
punctured-Euclidean chart, ordinary topology, low-homotopy collapse, and
path-component collapse synchronized at the selected point.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_flatRecognition_payload_and_collapse_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
        flatPayload
    ⟩

/--
The selected two-puncture recognition route also keeps the concrete
punctured-Euclidean chart and path-collapse fields synchronized across the
structured and flattened payloads.  The same selected flat payload reconstructs
path-connectedness, so downstream consumers can use the flattened recognition
object without losing the selected chart or path-component data.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_flatRecognition_fields_and_pathConnected_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , onePoint_threeSpace_twoPointComplement_pathConnectedSpace_of_flatRecognition
        flatPayload
    , flatPayload.pathNonempty
    , flatPayload.pathComponentEqUniv
    ⟩

/--
The selected two-puncture recognition route retains actual `Unique` instances
for the low homotopy types at the same selected basepoint, together with the
path-connectedness and path-collapse fields from the selected flat payload.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_unique_lowHomotopy_and_path_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        Nonempty (Unique
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , ⟨flatPayload.zerothUnique⟩
    , ⟨flatPayload.piZeroUnique⟩
    , ⟨flatPayload.fundamentalGroupUnique⟩
    , ⟨flatPayload.piOneUnique⟩
    , onePoint_threeSpace_twoPointComplement_pathConnectedSpace_of_flatRecognition
        flatPayload
    , flatPayload.pathNonempty
    , flatPayload.pathComponentEqUniv
    ⟩

/--
The selected two-puncture recognition route retains concrete field equalities,
unique low-homotopy instances, path-connectedness, and the path-collapse
surface at the same selected basepoint and flattened payload.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_fields_unique_and_collapse_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        Nonempty (Unique
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , ⟨flatPayload.zerothUnique⟩
    , ⟨flatPayload.piZeroUnique⟩
    , ⟨flatPayload.fundamentalGroupUnique⟩
    , ⟨flatPayload.piOneUnique⟩
    , onePoint_threeSpace_twoPointComplement_pathConnectedSpace_of_flatRecognition
        flatPayload
    , flatPayload.pathNonempty
    , flatPayload.pathComponentEqUniv
    ⟩

/--
The selected two-puncture recognition route retains concrete field equalities,
direct low-homotopy subsingleton facts, unique low-homotopy instances,
path-connectedness, and the path-collapse surface at the same selected
basepoint and flattened payload.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_fields_subsingleton_unique_and_collapse_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        Subsingleton
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Nonempty (Unique
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint)) ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  rcases
    onePoint_threeSpace_twoPointComplement_lowHomotopy_subsingleton_package_of_flatRecognition
      flatPayload with
    ⟨zerothSubsingleton, piZeroSubsingleton, fundamentalGroupSubsingleton,
      piOneSubsingleton⟩
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalGroupSubsingleton
    , piOneSubsingleton
    , ⟨flatPayload.zerothUnique⟩
    , ⟨flatPayload.piZeroUnique⟩
    , ⟨flatPayload.fundamentalGroupUnique⟩
    , ⟨flatPayload.piOneUnique⟩
    , onePoint_threeSpace_twoPointComplement_pathConnectedSpace_of_flatRecognition
        flatPayload
    , flatPayload.pathNonempty
    , flatPayload.pathComponentEqUniv
    ⟩

/--
The selected two-puncture recognition route keeps the structured recognition
payload, flattened payload, concrete field equalities, path-connectedness, the
direct zeroth/fundamental low-homotopy subsingletons, and the full legacy
collapse tuple synchronized at one selected basepoint.  This is the
single-use endpoint for callers that need the selected recognition fields and
legacy collapse data without reselecting a basepoint or reconstructing the
flat payload.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_fields_topology_lowHomotopy_and_collapse_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        PathConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          a = b) ∧
        (∃ baseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  rcases
    onePoint_threeSpace_twoPointComplement_lowHomotopy_subsingleton_package_of_flatRecognition
      flatPayload with
    ⟨zerothSubsingleton, _piZeroSubsingleton,
      fundamentalGroupSubsingleton, _piOneSubsingleton⟩
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , onePoint_threeSpace_twoPointComplement_pathConnectedSpace_of_flatRecognition
        flatPayload
    , zerothSubsingleton
    , fundamentalGroupSubsingleton
    , onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
        flatPayload
    ⟩

/--
The selected two-puncture recognition route also retains a universal
low-homotopy collapse family.  The selected flat payload supplies the legacy
collapse tuple, while every supplied basepoint of the same two-point complement
carries direct `Subsingleton`, equality-eliminator, and unique-class data.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_collapse_and_all_basepoint_lowHomotopy_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      (flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ x :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent x = Set.univ) ∧
        (∀ suppliedBasepoint :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Subsingleton
              (ZerothHomotopy
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
            Subsingleton
              (HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint) ∧
            Subsingleton
              (FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
            (∀ a b :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              a = b) ∧
            (∀ a b :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              a = b) ∧
            (∀ a b :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
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
                suppliedBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 0
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                homotopyClass = baseClass) ∧
            (∃ baseClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              ∀ fundamentalClass :
                FundamentalGroup
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                fundamentalClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 1
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                homotopyClass = baseClass)) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  rcases
      onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
        flatPayload with
    ⟨ chart
    , simplyConnected
    , connected
    , nonempty
    , _piZeroSubsingleton
    , _piOneSubsingleton
    , _zerothEq
    , _piZeroEq
    , _fundamentalGroupEq
    , _piOneEq
    , _zerothExistsUnique
    , _piZeroExistsUnique
    , _fundamentalGroupExistsUnique
    , _piOneExistsUnique
    , pathNonempty
    , pathComponentEqUniv
    ⟩
  let allBasepointLowHomotopy :
      ∀ suppliedBasepoint :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Subsingleton
            (ZerothHomotopy
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
          Subsingleton
            (HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
          (∀ a b :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
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
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∃ baseClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ fundamentalClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              fundamentalClass = baseClass) ∧
          (∃ baseClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) := by
    intro suppliedBasepoint
    exact
      ⟨ onePoint_threeSpace_twoPointComplement_zerothHomotopy_subsingleton
          hqp
      , onePoint_threeSpace_twoPointComplement_piZero_subsingleton
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_piOne_subsingleton
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_zerothHomotopy_mk_eq hqp
      , onePoint_threeSpace_twoPointComplement_piZero_eq
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_fundamentalGroup_eq
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_piOne_eq
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_zerothHomotopy_exists_unique
          hqp
      , onePoint_threeSpace_twoPointComplement_piZero_exists_unique
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_fundamentalGroup_exists_unique
          hqp suppliedBasepoint
      , onePoint_threeSpace_twoPointComplement_piOne_exists_unique
          hqp suppliedBasepoint
      ⟩
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , chart
    , simplyConnected
    , connected
    , nonempty
    , pathNonempty
    , pathComponentEqUniv
    , allBasepointLowHomotopy
    ⟩

/--
The selected two-puncture recognition route retains the concrete flattening
field equalities while also providing a reusable low-homotopy payload object at
every supplied basepoint.  This is the structured all-basepoint form of the
one-point compactification collapse route for consumers that need payload
objects rather than only propositional collapse fields.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_fields_and_all_basepoint_lowHomotopy_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.zerothUnique =
          recognitionPayload.lowHomotopy.zerothUnique ∧
        flatPayload.piZeroUnique =
          recognitionPayload.lowHomotopy.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
        flatPayload.piOneUnique =
          recognitionPayload.lowHomotopy.piOneUnique ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        (∀ suppliedBasepoint :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∃ _lowHomotopyPayload :
            OnePointTwoPointComplementLowHomotopyUniquePayload
              hqp suppliedBasepoint,
            ConnectedSpace
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Nonempty
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Nonempty (Unique
              (ZerothHomotopy
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
            Nonempty (Unique
              (HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint)) ∧
            Nonempty (Unique
              (FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint)) ∧
            Nonempty (Unique
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint)) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              Nonempty (Path a b)) ∧
            (∀ point :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              pathComponent point = Set.univ)) := by
  let basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload hqp
      basepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  let allBasepointLowHomotopyPayloads :
      ∀ suppliedBasepoint :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∃ _lowHomotopyPayload :
          OnePointTwoPointComplementLowHomotopyUniquePayload
            hqp suppliedBasepoint,
          ConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Nonempty
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Nonempty (Unique
            (ZerothHomotopy
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
          Nonempty (Unique
            (HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint)) ∧
          Nonempty (Unique
            (FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint)) ∧
          Nonempty (Unique
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint)) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
          (∀ point :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent point = Set.univ) := by
    intro suppliedBasepoint
    let lowHomotopyPayload :=
      onePoint_threeSpace_twoPointComplement_lowHomotopyUnique_payload
        hqp suppliedBasepoint
    exact
      ⟨ lowHomotopyPayload
      , lowHomotopyPayload.connected
      , lowHomotopyPayload.nonempty
      , ⟨lowHomotopyPayload.zerothUnique⟩
      , ⟨lowHomotopyPayload.piZeroUnique⟩
      , ⟨lowHomotopyPayload.fundamentalGroupUnique⟩
      , ⟨lowHomotopyPayload.piOneUnique⟩
      , lowHomotopyPayload.pathNonempty
      , lowHomotopyPayload.pathComponentEqUniv
      ⟩
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , allBasepointLowHomotopyPayloads
    ⟩

/--
The selected two-puncture recognition route can keep both downstream consumer
forms at once: concrete flattening field equalities for the selected flat
payload, the full legacy collapse tuple at the selected basepoint, and
reusable low-homotopy payload objects at every supplied basepoint of the same
two-point complement.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_fields_collapse_and_all_basepoint_lowHomotopy_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.zerothUnique =
          recognitionPayload.lowHomotopy.zerothUnique ∧
        flatPayload.piZeroUnique =
          recognitionPayload.lowHomotopy.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
        flatPayload.piOneUnique =
          recognitionPayload.lowHomotopy.piOneUnique ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        (∃ _collapsePayload :
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty
              ((({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
            SimplyConnectedSpace
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            ConnectedSpace
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Nonempty
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Subsingleton
              (HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                basepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                basepoint) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
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
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              Nonempty (Path a b)) ∧
            (∀ x :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              pathComponent x = Set.univ),
          True) ∧
        (∀ suppliedBasepoint :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∃ _lowHomotopyPayload :
            OnePointTwoPointComplementLowHomotopyUniquePayload
              hqp suppliedBasepoint,
            ConnectedSpace
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Nonempty
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Nonempty (Unique
              (ZerothHomotopy
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
            Nonempty (Unique
              (HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint)) ∧
            Nonempty (Unique
              (FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint)) ∧
            Nonempty (Unique
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint)) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              Nonempty (Path a b)) ∧
            (∀ point :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              pathComponent point = Set.univ)) := by
  rcases
      onePoint_threeSpace_twoPointComplement_selected_recognition_fields_and_all_basepoint_lowHomotopy_payloads
        hqp with
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , hFlat
    , hChart
    , hSimplyConnected
    , hConnected
    , hNonempty
    , hZerothUnique
    , hPiZeroUnique
    , hFundamentalGroupUnique
    , hPiOneUnique
    , hPathNonempty
    , hPathComponentEqUniv
    , allBasepointLowHomotopyPayloads
    ⟩
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , hFlat
    , hChart
    , hSimplyConnected
    , hConnected
    , hNonempty
    , hZerothUnique
    , hPiZeroUnique
    , hFundamentalGroupUnique
    , hPiOneUnique
    , hPathNonempty
    , hPathComponentEqUniv
    , ⟨ onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
          flatPayload
      , trivial⟩
    , allBasepointLowHomotopyPayloads
    ⟩

/--
The selected two-puncture recognition route can also expose the all-basepoint
low-homotopy payloads in the strongest consumer form: every supplied basepoint
gets the reusable payload object together with direct subsingleton instances,
explicit equality eliminators, unique-class representatives, path nonemptiness,
and path-component collapse.  The selected basepoint still carries the same
flat-recognition equalities and legacy collapse tuple.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_fields_collapse_and_all_basepoint_subsingleton_eq_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp basepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.zerothUnique =
          recognitionPayload.lowHomotopy.zerothUnique ∧
        flatPayload.piZeroUnique =
          recognitionPayload.lowHomotopy.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
        flatPayload.piOneUnique =
          recognitionPayload.lowHomotopy.piOneUnique ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        (∃ _collapsePayload :
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty
              ((({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
            SimplyConnectedSpace
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            ConnectedSpace
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Nonempty
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Subsingleton
              (HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                basepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                basepoint) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
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
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              Nonempty (Path a b)) ∧
            (∀ x :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              pathComponent x = Set.univ),
          True) ∧
        (∀ suppliedBasepoint :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∃ _lowHomotopyPayload :
            OnePointTwoPointComplementLowHomotopyUniquePayload
              hqp suppliedBasepoint,
            ConnectedSpace
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
            Nonempty
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
                suppliedBasepoint) ∧
            Subsingleton
              (FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
            (∀ a b :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              a = b) ∧
            (∀ a b :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              a = b) ∧
            (∀ a b :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
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
                suppliedBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 0
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                homotopyClass = baseClass) ∧
            (∃ baseClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              ∀ fundamentalClass :
                FundamentalGroup
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                fundamentalClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 1
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                homotopyClass = baseClass) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              Nonempty (Path a b)) ∧
            (∀ point :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              pathComponent point = Set.univ)) := by
  rcases
      onePoint_threeSpace_twoPointComplement_selected_recognition_fields_collapse_and_all_basepoint_lowHomotopy_payloads
        hqp with
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , hFlat
    , hChart
    , hSimplyConnected
    , hConnected
    , hNonempty
    , hZerothUnique
    , hPiZeroUnique
    , hFundamentalGroupUnique
    , hPiOneUnique
    , hPathNonempty
    , hPathComponentEqUniv
    , collapsePayload
    , _allBasepointLowHomotopyPayloads
    ⟩
  let allBasepointSubsingletonEqPayloads :
      ∀ suppliedBasepoint :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∃ lowHomotopyPayload :
          OnePointTwoPointComplementLowHomotopyUniquePayload
            hqp suppliedBasepoint,
          ConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Nonempty
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
              suppliedBasepoint) ∧
          Subsingleton
            (FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
          (∀ a b :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
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
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∃ baseClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ fundamentalClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              fundamentalClass = baseClass) ∧
          (∃ baseClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
          (∀ point :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent point = Set.univ) := by
    intro suppliedBasepoint
    let lowHomotopyPayload :=
      onePoint_threeSpace_twoPointComplement_lowHomotopyUnique_payload
        hqp suppliedBasepoint
    letI : Unique
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
      lowHomotopyPayload.zerothUnique
    letI : Unique
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
      lowHomotopyPayload.piZeroUnique
    letI : Unique
        (FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
      lowHomotopyPayload.fundamentalGroupUnique
    letI : Unique
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
      lowHomotopyPayload.piOneUnique
    exact
      ⟨ lowHomotopyPayload
      , lowHomotopyPayload.connected
      , lowHomotopyPayload.nonempty
      , inferInstance
      , inferInstance
      , inferInstance
      , inferInstance
      , fun a b => Subsingleton.elim _ _
      , fun a b => Subsingleton.elim _ _
      , fun a b => Subsingleton.elim _ _
      , fun a b => Subsingleton.elim _ _
      , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
      , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
      , ⟨default, fun fundamentalClass => Subsingleton.elim _ _⟩
      , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
      , lowHomotopyPayload.pathNonempty
      , lowHomotopyPayload.pathComponentEqUniv
      ⟩
  exact
    ⟨ basepoint
    , recognitionPayload
    , flatPayload
    , hFlat
    , hChart
    , hSimplyConnected
    , hConnected
    , hNonempty
    , hZerothUnique
    , hPiZeroUnique
    , hFundamentalGroupUnique
    , hPiOneUnique
    , hPathNonempty
    , hPathComponentEqUniv
    , collapsePayload
    , allBasepointSubsingletonEqPayloads
    ⟩

/--
For every supplied basepoint, the one-point two-puncture route retains the
actual structured recognition payload and its flattened recognition payload.
This all-basepoint endpoint keeps the flattening equalities, chart, ordinary
topology, low-homotopy unique instances, path-collapse fields, and legacy
collapse tuple synchronized without choosing a preferred basepoint first.
-/
theorem onePoint_threeSpace_twoPointComplement_all_basepoint_recognition_flatRecognition_and_collapse_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∃ recognitionPayload :
        OnePointTwoPointComplementRecognitionPayload hqp suppliedBasepoint,
      ∃ flatPayload :
        OnePointTwoPointComplementFlatRecognitionPayload hqp suppliedBasepoint,
        flatPayload =
          onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
            recognitionPayload ∧
          flatPayload.puncturedEuclideanChart =
            recognitionPayload.puncturedEuclideanChart ∧
          flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
          flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
          flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
          flatPayload.zerothUnique =
            recognitionPayload.lowHomotopy.zerothUnique ∧
          flatPayload.piZeroUnique =
            recognitionPayload.lowHomotopy.piZeroUnique ∧
          flatPayload.fundamentalGroupUnique =
            recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
          flatPayload.piOneUnique =
            recognitionPayload.lowHomotopy.piOneUnique ∧
          flatPayload.pathNonempty =
            recognitionPayload.lowHomotopy.pathNonempty ∧
          flatPayload.pathComponentEqUniv =
            recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty
              ((({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
          SimplyConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          ConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Nonempty
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Subsingleton
            (HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
          (∀ a b :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
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
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∃ baseClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ fundamentalClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              fundamentalClass = baseClass) ∧
          (∃ baseClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
          (∀ x :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent x = Set.univ) := by
  intro suppliedBasepoint
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload
      hqp suppliedBasepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  exact
    ⟨ recognitionPayload
    , flatPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , onePoint_threeSpace_twoPointComplement_collapse_payload_of_flatRecognition
        flatPayload
    ⟩

/--
The two-puncture complement has a standalone all-basepoint low-homotopy
collapse package.  For every supplied basepoint it returns the reusable
low-homotopy uniqueness payload, direct subsingleton instances, explicit
equality eliminators, named collapsed base classes, path nonemptiness, and
path-component collapse, without forcing callers through a separately selected
basepoint endpoint.
-/
theorem onePoint_threeSpace_twoPointComplement_all_basepoint_lowHomotopy_baseclass_collapse_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∃ _lowHomotopyPayload :
        OnePointTwoPointComplementLowHomotopyUniquePayload hqp suppliedBasepoint,
        ConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
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
            suppliedBasepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
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
            suppliedBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ) := by
  intro suppliedBasepoint
  let lowHomotopyPayload :=
    onePoint_threeSpace_twoPointComplement_lowHomotopyUnique_payload
      hqp suppliedBasepoint
  letI : Unique
      (ZerothHomotopy
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    lowHomotopyPayload.zerothUnique
  letI : Unique
      (HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        suppliedBasepoint) :=
    lowHomotopyPayload.piZeroUnique
  letI : Unique
      (FundamentalGroup
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        suppliedBasepoint) :=
    lowHomotopyPayload.fundamentalGroupUnique
  letI : Unique
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        suppliedBasepoint) :=
    lowHomotopyPayload.piOneUnique
  exact
    ⟨ lowHomotopyPayload
    , lowHomotopyPayload.connected
    , lowHomotopyPayload.nonempty
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , fun a b => Subsingleton.elim _ _
    , fun a b => Subsingleton.elim _ _
    , fun a b => Subsingleton.elim _ _
    , fun a b => Subsingleton.elim _ _
    , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun fundamentalClass => Subsingleton.elim _ _⟩
    , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
    , lowHomotopyPayload.pathNonempty
    , lowHomotopyPayload.pathComponentEqUniv
    ⟩

/--
The two-puncture route exposes its two all-basepoint consumer families
together: every supplied basepoint has the structured recognition/flat-
recognition/collapse payload, and the same supplied basepoints have the
standalone low-homotopy baseclass-collapse payload.  This is a compact
downstream endpoint for consumers that need both the recognition object and
the direct low-homotopy eliminators without reselecting a preferred basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_all_basepoint_recognition_and_lowHomotopy_baseclass_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    (∀ suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∃ recognitionPayload :
        OnePointTwoPointComplementRecognitionPayload hqp suppliedBasepoint,
      ∃ flatPayload :
        OnePointTwoPointComplementFlatRecognitionPayload hqp suppliedBasepoint,
        flatPayload =
          onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
            recognitionPayload ∧
          flatPayload.puncturedEuclideanChart =
            recognitionPayload.puncturedEuclideanChart ∧
          flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
          flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
          flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
          flatPayload.zerothUnique =
            recognitionPayload.lowHomotopy.zerothUnique ∧
          flatPayload.piZeroUnique =
            recognitionPayload.lowHomotopy.piZeroUnique ∧
          flatPayload.fundamentalGroupUnique =
            recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
          flatPayload.piOneUnique =
            recognitionPayload.lowHomotopy.piOneUnique ∧
          flatPayload.pathNonempty =
            recognitionPayload.lowHomotopy.pathNonempty ∧
          flatPayload.pathComponentEqUniv =
            recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty
              ((({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
          SimplyConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          ConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Nonempty
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Subsingleton
            (HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
          (∀ a b :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
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
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∃ baseClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ fundamentalClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              fundamentalClass = baseClass) ∧
          (∃ baseClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
          (∀ x :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent x = Set.univ)) ∧
    (∀ suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∃ _lowHomotopyPayload :
        OnePointTwoPointComplementLowHomotopyUniquePayload hqp suppliedBasepoint,
        ConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
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
            suppliedBasepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
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
            suppliedBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ)) := by
  exact
    ⟨ onePoint_threeSpace_twoPointComplement_all_basepoint_recognition_flatRecognition_and_collapse_payloads
        hqp
    , onePoint_threeSpace_twoPointComplement_all_basepoint_lowHomotopy_baseclass_collapse_payloads
        hqp
    ⟩

/--
For one supplied two-puncture basepoint, the recognition payload, flat
recognition payload, and low-homotopy/baseclass payload can be selected from
the same concrete low-homotopy object.  This fixed-basepoint endpoint keeps
the punctured-Euclidean model, simple connectedness, connectedness,
nonemptiness, four unique low-homotopy/baseclass witnesses, path nonemptiness,
and path-component collapse synchronized without passing through the
all-basepoint family first.
-/
theorem onePoint_threeSpace_twoPointComplement_supplied_basepoint_recognition_flat_lowHomotopy_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp suppliedBasepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp suppliedBasepoint,
    ∃ lowHomotopyPayload :
      OnePointTwoPointComplementLowHomotopyUniquePayload
        hqp suppliedBasepoint,
      lowHomotopyPayload = recognitionPayload.lowHomotopy ∧
        flatPayload =
          onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
            recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = lowHomotopyPayload.connected ∧
        flatPayload.nonempty = lowHomotopyPayload.nonempty ∧
        flatPayload.zerothUnique = lowHomotopyPayload.zerothUnique ∧
        flatPayload.piZeroUnique = lowHomotopyPayload.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          lowHomotopyPayload.fundamentalGroupUnique ∧
        flatPayload.piOneUnique = lowHomotopyPayload.piOneUnique ∧
        flatPayload.pathNonempty = lowHomotopyPayload.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          lowHomotopyPayload.pathComponentEqUniv ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty (Unique
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint)) ∧
        Nonempty (Unique
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint)) ∧
        Nonempty (Unique
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint)) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ) := by
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload
      hqp suppliedBasepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  let lowHomotopyPayload :=
    recognitionPayload.lowHomotopy
  exact
    ⟨ recognitionPayload
    , flatPayload
    , lowHomotopyPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , recognitionPayload.puncturedEuclideanChart
    , recognitionPayload.simplyConnected
    , lowHomotopyPayload.connected
    , lowHomotopyPayload.nonempty
    , ⟨lowHomotopyPayload.zerothUnique⟩
    , ⟨lowHomotopyPayload.piZeroUnique⟩
    , ⟨lowHomotopyPayload.fundamentalGroupUnique⟩
    , ⟨lowHomotopyPayload.piOneUnique⟩
    , lowHomotopyPayload.pathNonempty
    , lowHomotopyPayload.pathComponentEqUniv
    ⟩

/--
For one supplied two-puncture basepoint, the structured recognition payload
also opens to direct low-homotopy subsingleton eliminators and named collapsed
base classes.  This is the fixed-basepoint consumer form used by topology
transport code that needs both the retained recognition/flat payloads and
explicit quotient-collapse witnesses.
-/
theorem onePoint_threeSpace_twoPointComplement_supplied_basepoint_recognition_flat_lowHomotopy_subsingleton_baseclass_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp suppliedBasepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp suppliedBasepoint,
    ∃ lowHomotopyPayload :
      OnePointTwoPointComplementLowHomotopyUniquePayload
        hqp suppliedBasepoint,
      lowHomotopyPayload = recognitionPayload.lowHomotopy ∧
        flatPayload =
          onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
            recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = lowHomotopyPayload.connected ∧
        flatPayload.nonempty = lowHomotopyPayload.nonempty ∧
        flatPayload.zerothUnique = lowHomotopyPayload.zerothUnique ∧
        flatPayload.piZeroUnique = lowHomotopyPayload.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          lowHomotopyPayload.fundamentalGroupUnique ∧
        flatPayload.piOneUnique = lowHomotopyPayload.piOneUnique ∧
        flatPayload.pathNonempty = lowHomotopyPayload.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          lowHomotopyPayload.pathComponentEqUniv ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
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
            suppliedBasepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
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
            suppliedBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          ∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = baseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ) := by
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload
      hqp suppliedBasepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  let lowHomotopyPayload :=
    recognitionPayload.lowHomotopy
  letI :
      Unique
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    lowHomotopyPayload.zerothUnique
  letI :
      Unique
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
    lowHomotopyPayload.piZeroUnique
  letI :
      Unique
        (FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
    lowHomotopyPayload.fundamentalGroupUnique
  letI :
      Unique
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
    lowHomotopyPayload.piOneUnique
  exact
    ⟨ recognitionPayload
    , flatPayload
    , lowHomotopyPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , recognitionPayload.puncturedEuclideanChart
    , recognitionPayload.simplyConnected
    , lowHomotopyPayload.connected
    , lowHomotopyPayload.nonempty
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , fun _a _b => Subsingleton.elim _ _
    , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
    , ⟨default, fun fundamentalClass => Subsingleton.elim _ _⟩
    , ⟨default, fun homotopyClass => Subsingleton.elim _ _⟩
    , lowHomotopyPayload.pathNonempty
    , lowHomotopyPayload.pathComponentEqUniv
    ⟩

/--
Uniform all-basepoint consumer form of the retained two-puncture recognition
route.  For every supplied basepoint it constructs the synchronized structured
recognition, flat recognition, and low-homotopy payloads and exposes the four
low-homotopy subsingleton instances together with path and path-component
collapse.
-/
theorem onePoint_threeSpace_twoPointComplement_all_basepoint_recognition_flat_lowHomotopy_subsingleton_path_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∃ recognitionPayload :
        OnePointTwoPointComplementRecognitionPayload hqp suppliedBasepoint,
      ∃ flatPayload :
        OnePointTwoPointComplementFlatRecognitionPayload hqp suppliedBasepoint,
      ∃ lowHomotopyPayload :
        OnePointTwoPointComplementLowHomotopyUniquePayload
          hqp suppliedBasepoint,
        lowHomotopyPayload = recognitionPayload.lowHomotopy ∧
          flatPayload =
            onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
              recognitionPayload ∧
          Subsingleton
            (ZerothHomotopy
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
          Subsingleton
            (HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
          (∀ point :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent point = Set.univ) := by
  intro suppliedBasepoint
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload
      hqp suppliedBasepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  let lowHomotopyPayload :=
    recognitionPayload.lowHomotopy
  letI :
      Unique
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    lowHomotopyPayload.zerothUnique
  letI :
      Unique
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
    lowHomotopyPayload.piZeroUnique
  letI :
      Unique
        (FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
    lowHomotopyPayload.fundamentalGroupUnique
  letI :
      Unique
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint) :=
    lowHomotopyPayload.piOneUnique
  exact
    ⟨ recognitionPayload
    , flatPayload
    , lowHomotopyPayload
    , rfl
    , rfl
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , lowHomotopyPayload.pathNonempty
    , lowHomotopyPayload.pathComponentEqUniv
    ⟩

/--
Uniform all-basepoint consumer form with named low-homotopy base classes.
This opens the supplied-basepoint recognition/flat/low-homotopy endpoint at
every two-puncture complement basepoint, so downstream topology transport can
use concrete collapsed zeroth, `π₀`, fundamental-group, and `π₁` base classes
without separately specializing the fixed-basepoint theorem.
-/
theorem onePoint_threeSpace_twoPointComplement_all_basepoint_recognition_flat_lowHomotopy_subsingleton_baseclass_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∃ recognitionPayload :
        OnePointTwoPointComplementRecognitionPayload hqp suppliedBasepoint,
      ∃ flatPayload :
        OnePointTwoPointComplementFlatRecognitionPayload hqp suppliedBasepoint,
      ∃ lowHomotopyPayload :
        OnePointTwoPointComplementLowHomotopyUniquePayload
          hqp suppliedBasepoint,
        lowHomotopyPayload = recognitionPayload.lowHomotopy ∧
          flatPayload =
            onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
              recognitionPayload ∧
          flatPayload.puncturedEuclideanChart =
            recognitionPayload.puncturedEuclideanChart ∧
          flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
          flatPayload.connected = lowHomotopyPayload.connected ∧
          flatPayload.nonempty = lowHomotopyPayload.nonempty ∧
          flatPayload.zerothUnique = lowHomotopyPayload.zerothUnique ∧
          flatPayload.piZeroUnique = lowHomotopyPayload.piZeroUnique ∧
          flatPayload.fundamentalGroupUnique =
            lowHomotopyPayload.fundamentalGroupUnique ∧
          flatPayload.piOneUnique = lowHomotopyPayload.piOneUnique ∧
          flatPayload.pathNonempty = lowHomotopyPayload.pathNonempty ∧
          flatPayload.pathComponentEqUniv =
            lowHomotopyPayload.pathComponentEqUniv ∧
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty
              ((({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
          SimplyConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          ConnectedSpace
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Nonempty
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
              suppliedBasepoint) ∧
          Subsingleton
            (FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
          (∀ a b :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            a = b) ∧
          (∀ a b :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
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
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∃ baseClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ fundamentalClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              fundamentalClass = baseClass) ∧
          (∃ baseClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            ∀ homotopyClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = baseClass) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
          (∀ point :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent point = Set.univ) := by
  intro suppliedBasepoint
  exact
    onePoint_threeSpace_twoPointComplement_supplied_basepoint_recognition_flat_lowHomotopy_subsingleton_baseclass_fields
      hqp suppliedBasepoint

/--
The selected two-puncture basepoint can be opened into the concrete
recognition/flat payloads and named collapsed low-homotopy base classes.  This
is the selected-basepoint consumer form of the two-puncture route: it retains
the punctured-Euclidean chart, simple connectedness, connectedness,
nonemptiness, four subsingleton collapse instances, concrete collapsed
representatives, path nonemptiness, and path-component collapse in one witness.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_basepoint_recognition_flat_named_baseclass_collapse_witnesses
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ selectedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp selectedBasepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp selectedBasepoint,
    ∃ zerothBaseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ piZeroBaseClass :
      HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ fundamentalBaseClass :
      FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ piOneBaseClass :
      HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.zerothUnique =
          recognitionPayload.lowHomotopy.zerothUnique ∧
        flatPayload.piZeroUnique =
          recognitionPayload.lowHomotopy.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
        flatPayload.piOneUnique =
          recognitionPayload.lowHomotopy.piOneUnique ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint) ∧
        (∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = zerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = piZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          fundamentalClass = fundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = piOneBaseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ) := by
  let selectedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (onePoint_threeSpace_twoPointComplement_nonempty hqp)
  let recognitionPayload :=
    onePoint_threeSpace_twoPointComplement_recognition_payload
      hqp selectedBasepoint
  let flatPayload :=
    onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
      recognitionPayload
  let lowHomotopyPayload :=
    recognitionPayload.lowHomotopy
  letI :
      Unique
        (ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    lowHomotopyPayload.zerothUnique
  letI :
      Unique
        (HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          selectedBasepoint) :=
    lowHomotopyPayload.piZeroUnique
  letI :
      Unique
        (FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          selectedBasepoint) :=
    lowHomotopyPayload.fundamentalGroupUnique
  letI :
      Unique
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          selectedBasepoint) :=
    lowHomotopyPayload.piOneUnique
  exact
    ⟨ selectedBasepoint
    , recognitionPayload
    , flatPayload
    , default
    , default
    , default
    , default
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , recognitionPayload.puncturedEuclideanChart
    , recognitionPayload.simplyConnected
    , lowHomotopyPayload.connected
    , lowHomotopyPayload.nonempty
    , inferInstance
    , inferInstance
    , inferInstance
    , inferInstance
    , fun homotopyClass => Subsingleton.elim _ _
    , fun homotopyClass => Subsingleton.elim _ _
    , fun fundamentalClass => Subsingleton.elim _ _
    , fun homotopyClass => Subsingleton.elim _ _
    , lowHomotopyPayload.pathNonempty
    , lowHomotopyPayload.pathComponentEqUniv
    ⟩

/--
Uniform selected-basepoint and all-supplied-basepoint collapse endpoint for
the two-puncture complement.  It fixes one selected complement basepoint and
names its collapsed zeroth, `π₀`, fundamental-group, and `π₁` classes, while
also exposing named collapsed classes, path nonemptiness, and path-component
collapse for every externally supplied basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_basepoint_and_all_basepoint_named_baseclass_collapse_witnesses
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∃ selectedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ selectedZerothBaseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ selectedPiZeroBaseClass :
      HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ selectedFundamentalBaseClass :
      FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ selectedPiOneBaseClass :
      HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
      (∀ homotopyClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        homotopyClass = selectedZerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = selectedPiZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          fundamentalClass = selectedFundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = selectedPiOneBaseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ) ∧
        (∀ suppliedBasepoint :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∃ suppliedZerothBaseClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ∃ suppliedPiZeroBaseClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
          ∃ suppliedFundamentalBaseClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
          ∃ suppliedPiOneBaseClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            (∀ homotopyClass :
              ZerothHomotopy
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              homotopyClass = suppliedZerothBaseClass) ∧
              (∀ homotopyClass :
                HomotopyGroup.Pi 0
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                homotopyClass = suppliedPiZeroBaseClass) ∧
              (∀ fundamentalClass :
                FundamentalGroup
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                fundamentalClass = suppliedFundamentalBaseClass) ∧
              (∀ homotopyClass :
                HomotopyGroup.Pi 1
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  suppliedBasepoint,
                homotopyClass = suppliedPiOneBaseClass) ∧
              (∀ a b :
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
                Nonempty (Path a b)) ∧
              (∀ point :
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
                pathComponent point = Set.univ)) := by
  rcases
    onePoint_threeSpace_twoPointComplement_selected_basepoint_recognition_flat_named_baseclass_collapse_witnesses
      hqp with
    ⟨ selectedBasepoint
    , _recognitionPayload
    , _flatPayload
    , selectedZerothBaseClass
    , selectedPiZeroBaseClass
    , selectedFundamentalBaseClass
    , selectedPiOneBaseClass
    , _hFlat
    , _hChart
    , _hSimplyConnected
    , _hConnected
    , _hNonempty
    , _hZerothUnique
    , _hPiZeroUnique
    , _hFundamentalUnique
    , _hPiOneUnique
    , _hPathNonemptyFlat
    , _hPathComponentFlat
    , _punctureChart
    , _simplyConnected
    , _connected
    , _nonempty
    , _zerothSubsingleton
    , _piZeroSubsingleton
    , _fundamentalSubsingleton
    , _piOneSubsingleton
    , selectedZerothEq
    , selectedPiZeroEq
    , selectedFundamentalEq
    , selectedPiOneEq
    , selectedPathNonempty
    , selectedPathComponentEqUniv
    ⟩
  have allSupplied :
      ∀ suppliedBasepoint :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∃ suppliedZerothBaseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∃ suppliedPiZeroBaseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
        ∃ suppliedFundamentalBaseClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
        ∃ suppliedPiOneBaseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          (∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = suppliedZerothBaseClass) ∧
            (∀ homotopyClass :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = suppliedPiZeroBaseClass) ∧
            (∀ fundamentalClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              fundamentalClass = suppliedFundamentalBaseClass) ∧
            (∀ homotopyClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = suppliedPiOneBaseClass) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              Nonempty (Path a b)) ∧
            (∀ point :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              pathComponent point = Set.univ) := by
    intro suppliedBasepoint
    rcases
      onePoint_threeSpace_twoPointComplement_all_basepoint_lowHomotopy_baseclass_collapse_payloads
        hqp suppliedBasepoint with
      ⟨ _lowHomotopyPayload
      , _connected
      , _nonempty
      , _zerothSubsingleton
      , _piZeroSubsingleton
      , _fundamentalSubsingleton
      , _piOneSubsingleton
      , _zerothMkEq
      , _piZeroEq
      , _fundamentalEq
      , _piOneEq
      , ⟨ suppliedZerothBaseClass, suppliedZerothEq ⟩
      , ⟨ suppliedPiZeroBaseClass, suppliedPiZeroEq ⟩
      , ⟨ suppliedFundamentalBaseClass, suppliedFundamentalEq ⟩
      , ⟨ suppliedPiOneBaseClass, suppliedPiOneEq ⟩
      , suppliedPathNonempty
      , suppliedPathComponentEqUniv
      ⟩
    exact
      ⟨ suppliedZerothBaseClass
      , suppliedPiZeroBaseClass
      , suppliedFundamentalBaseClass
      , suppliedPiOneBaseClass
      , suppliedZerothEq
      , suppliedPiZeroEq
      , suppliedFundamentalEq
      , suppliedPiOneEq
      , suppliedPathNonempty
      , suppliedPathComponentEqUniv
      ⟩
  exact
    ⟨ selectedBasepoint
    , selectedZerothBaseClass
    , selectedPiZeroBaseClass
    , selectedFundamentalBaseClass
    , selectedPiOneBaseClass
    , selectedZerothEq
    , selectedPiZeroEq
    , selectedFundamentalEq
    , selectedPiOneEq
    , selectedPathNonempty
    , selectedPathComponentEqUniv
    , allSupplied
    ⟩

/--
The two-puncture route can keep the selected recognition/flat payload objects
and the uniform all-basepoint named class collapse simultaneously.  This gives
downstream topology extraction one endpoint that retains the selected
punctured-Euclidean chart data while still providing the low-homotopy collapse
for every externally supplied basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_flat_and_all_basepoint_named_baseclass_collapse_witnesses
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    (∃ selectedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp selectedBasepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp selectedBasepoint,
    ∃ zerothBaseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ piZeroBaseClass :
      HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ fundamentalBaseClass :
      FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ piOneBaseClass :
      HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.zerothUnique =
          recognitionPayload.lowHomotopy.zerothUnique ∧
        flatPayload.piZeroUnique =
          recognitionPayload.lowHomotopy.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
        flatPayload.piOneUnique =
          recognitionPayload.lowHomotopy.piOneUnique ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty
            ((({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        ConnectedSpace
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Subsingleton
          (ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) ∧
        Subsingleton
          (HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint) ∧
        (∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = zerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = piZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          fundamentalClass = fundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = piOneBaseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ)) ∧
      (∀ suppliedBasepoint :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∃ suppliedZerothBaseClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        ∃ suppliedPiZeroBaseClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
        ∃ suppliedFundamentalBaseClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
        ∃ suppliedPiOneBaseClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          (∀ homotopyClass :
            ZerothHomotopy
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            homotopyClass = suppliedZerothBaseClass) ∧
            (∀ homotopyClass :
              HomotopyGroup.Pi 0
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = suppliedPiZeroBaseClass) ∧
            (∀ fundamentalClass :
              FundamentalGroup
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              fundamentalClass = suppliedFundamentalBaseClass) ∧
            (∀ homotopyClass :
              HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                suppliedBasepoint,
              homotopyClass = suppliedPiOneBaseClass) ∧
            (∀ a b :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              Nonempty (Path a b)) ∧
            (∀ point :
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
              pathComponent point = Set.univ)) := by
  refine
    ⟨ onePoint_threeSpace_twoPointComplement_selected_basepoint_recognition_flat_named_baseclass_collapse_witnesses
        hqp
    , ?_ ⟩
  intro suppliedBasepoint
  rcases
    onePoint_threeSpace_twoPointComplement_all_basepoint_lowHomotopy_baseclass_collapse_payloads
      hqp suppliedBasepoint with
    ⟨ _lowHomotopyPayload
    , _connected
    , _nonempty
    , _zerothSubsingleton
    , _piZeroSubsingleton
    , _fundamentalSubsingleton
    , _piOneSubsingleton
    , _zerothMkEq
    , _piZeroEq
    , _fundamentalEq
    , _piOneEq
    , ⟨ suppliedZerothBaseClass, suppliedZerothEq ⟩
    , ⟨ suppliedPiZeroBaseClass, suppliedPiZeroEq ⟩
    , ⟨ suppliedFundamentalBaseClass, suppliedFundamentalEq ⟩
    , ⟨ suppliedPiOneBaseClass, suppliedPiOneEq ⟩
    , suppliedPathNonempty
    , suppliedPathComponentEqUniv
    ⟩
  exact
    ⟨ suppliedZerothBaseClass
    , suppliedPiZeroBaseClass
    , suppliedFundamentalBaseClass
    , suppliedPiOneBaseClass
    , suppliedZerothEq
    , suppliedPiZeroEq
    , suppliedFundamentalEq
    , suppliedPiOneEq
    , suppliedPathNonempty
    , suppliedPathComponentEqUniv
    ⟩

/--
Fixed supplied-basepoint form of the selected two-puncture endpoint.  It keeps
the selected recognition/flat payload and named-baseclass collapse witnesses
from the canonical selected basepoint, while also retaining the named
baseclass collapse and path-connectedness witnesses for one externally
supplied basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_recognition_flat_and_supplied_basepoint_named_baseclass_collapse_witnesses
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    (∃ selectedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ recognitionPayload :
      OnePointTwoPointComplementRecognitionPayload hqp selectedBasepoint,
    ∃ flatPayload :
      OnePointTwoPointComplementFlatRecognitionPayload hqp selectedBasepoint,
    ∃ selectedZerothBaseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ selectedPiZeroBaseClass :
      HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ selectedFundamentalBaseClass :
      FundamentalGroup
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
    ∃ selectedPiOneBaseClass :
      HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        selectedBasepoint,
      flatPayload =
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload_of_recognition
          recognitionPayload ∧
        flatPayload.puncturedEuclideanChart =
          recognitionPayload.puncturedEuclideanChart ∧
        flatPayload.simplyConnected = recognitionPayload.simplyConnected ∧
        flatPayload.connected = recognitionPayload.lowHomotopy.connected ∧
        flatPayload.nonempty = recognitionPayload.lowHomotopy.nonempty ∧
        flatPayload.zerothUnique =
          recognitionPayload.lowHomotopy.zerothUnique ∧
        flatPayload.piZeroUnique =
          recognitionPayload.lowHomotopy.piZeroUnique ∧
        flatPayload.fundamentalGroupUnique =
          recognitionPayload.lowHomotopy.fundamentalGroupUnique ∧
        flatPayload.piOneUnique =
          recognitionPayload.lowHomotopy.piOneUnique ∧
        flatPayload.pathNonempty =
          recognitionPayload.lowHomotopy.pathNonempty ∧
        flatPayload.pathComponentEqUniv =
          recognitionPayload.lowHomotopy.pathComponentEqUniv ∧
        (∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = selectedZerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = selectedPiZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          fundamentalClass = selectedFundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            selectedBasepoint,
          homotopyClass = selectedPiOneBaseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ)) ∧
      (∃ suppliedZerothBaseClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∃ suppliedPiZeroBaseClass :
        HomotopyGroup.Pi 0
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint,
      ∃ suppliedFundamentalBaseClass :
        FundamentalGroup
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint,
      ∃ suppliedPiOneBaseClass :
        HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          suppliedBasepoint,
        (∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = suppliedZerothBaseClass) ∧
          (∀ homotopyClass :
            HomotopyGroup.Pi 0
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = suppliedPiZeroBaseClass) ∧
          (∀ fundamentalClass :
            FundamentalGroup
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            fundamentalClass = suppliedFundamentalBaseClass) ∧
          (∀ homotopyClass :
            HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              suppliedBasepoint,
            homotopyClass = suppliedPiOneBaseClass) ∧
          (∀ a b :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            Nonempty (Path a b)) ∧
          (∀ point :
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
            pathComponent point = Set.univ)) := by
  rcases
    onePoint_threeSpace_twoPointComplement_selected_recognition_flat_and_all_basepoint_named_baseclass_collapse_witnesses
      hqp with
    ⟨ selectedPayload, allSupplied ⟩
  rcases selectedPayload with
    ⟨ selectedBasepoint
    , recognitionPayload
    , flatPayload
    , selectedZerothBaseClass
    , selectedPiZeroBaseClass
    , selectedFundamentalBaseClass
    , selectedPiOneBaseClass
    , hFlatPayload
    , hPuncturedChart
    , hSimplyConnected
    , hConnected
    , hNonempty
    , hZerothUnique
    , hPiZeroUnique
    , hFundamentalUnique
    , hPiOneUnique
    , hPathNonemptyField
    , hPathComponentField
    , _puncturedChart
    , _simplyConnected
    , _connected
    , _nonempty
    , _zerothSubsingleton
    , _piZeroSubsingleton
    , _fundamentalSubsingleton
    , _piOneSubsingleton
    , selectedZerothEq
    , selectedPiZeroEq
    , selectedFundamentalEq
    , selectedPiOneEq
    , selectedPathNonempty
    , selectedPathComponentEqUniv
    ⟩
  rcases allSupplied suppliedBasepoint with
    ⟨ suppliedZerothBaseClass
    , suppliedPiZeroBaseClass
    , suppliedFundamentalBaseClass
    , suppliedPiOneBaseClass
    , suppliedZerothEq
    , suppliedPiZeroEq
    , suppliedFundamentalEq
    , suppliedPiOneEq
    , suppliedPathNonempty
    , suppliedPathComponentEqUniv
    ⟩
  exact
    ⟨ ⟨ selectedBasepoint
      , recognitionPayload
      , flatPayload
      , selectedZerothBaseClass
      , selectedPiZeroBaseClass
      , selectedFundamentalBaseClass
      , selectedPiOneBaseClass
      , hFlatPayload
      , hPuncturedChart
      , hSimplyConnected
      , hConnected
      , hNonempty
      , hZerothUnique
      , hPiZeroUnique
      , hFundamentalUnique
      , hPiOneUnique
      , hPathNonemptyField
      , hPathComponentField
      , selectedZerothEq
      , selectedPiZeroEq
      , selectedFundamentalEq
      , selectedPiOneEq
      , selectedPathNonempty
      , selectedPathComponentEqUniv
      ⟩
    , suppliedZerothBaseClass
    , suppliedPiZeroBaseClass
    , suppliedFundamentalBaseClass
    , suppliedPiOneBaseClass
    , suppliedZerothEq
    , suppliedPiZeroEq
    , suppliedFundamentalEq
    , suppliedPiOneEq
    , suppliedPathNonempty
    , suppliedPathComponentEqUniv
    ⟩

set_option linter.unusedVariables false

/--
Basepoint-independence of the named `π₀` collapse representative for the
one-point compactification two-puncture complement.  The selected basepoint
route and any externally supplied basepoint route choose zeroth homotopy base
classes, and the collapse eliminators identify those representatives.
-/
theorem onePoint_threeSpace_twoPointComplement_selected_and_supplied_zeroth_baseclass_agreement
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ selectedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ selectedZerothBaseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ suppliedZerothBaseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      (∀ homotopyClass :
        ZerothHomotopy
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        homotopyClass = selectedZerothBaseClass) ∧
        (∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = suppliedZerothBaseClass) ∧
        selectedZerothBaseClass = suppliedZerothBaseClass ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ) := by
  rcases
    onePoint_threeSpace_twoPointComplement_selected_basepoint_and_all_basepoint_named_baseclass_collapse_witnesses
      hqp with
    ⟨ selectedBasepoint
    , selectedZerothBaseClass
    , _selectedPiZeroBaseClass
    , _selectedFundamentalBaseClass
    , _selectedPiOneBaseClass
    , selectedZerothEq
    , _selectedPiZeroEq
    , _selectedFundamentalEq
    , _selectedPiOneEq
    , _selectedPathNonempty
    , _selectedPathComponentEqUniv
    , allSupplied
    ⟩
  rcases allSupplied suppliedBasepoint with
    ⟨ suppliedZerothBaseClass
    , _suppliedPiZeroBaseClass
    , _suppliedFundamentalBaseClass
    , _suppliedPiOneBaseClass
    , suppliedZerothEq
    , _suppliedPiZeroEq
    , _suppliedFundamentalEq
    , _suppliedPiOneEq
    , suppliedPathNonempty
    , suppliedPathComponentEqUniv
    ⟩
  exact
    ⟨ selectedBasepoint
    , selectedZerothBaseClass
    , suppliedZerothBaseClass
    , selectedZerothEq
    , suppliedZerothEq
    , suppliedZerothEq selectedZerothBaseClass
    , suppliedPathNonempty
    , suppliedPathComponentEqUniv
    ⟩

set_option linter.unusedVariables true

/--
Fixed supplied-basepoint low-homotopy collapse package.  This specializes the
all-basepoint two-puncture theorem to one external basepoint while retaining
the reusable payload, direct subsingleton instances, equality eliminators,
named collapsed base classes, path nonemptiness, and path-component collapse.
-/
theorem onePoint_threeSpace_twoPointComplement_supplied_basepoint_lowHomotopy_subsingletons_named_baseclasses_and_paths
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (suppliedBasepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ _lowHomotopyPayload :
      OnePointTwoPointComplementLowHomotopyUniquePayload hqp suppliedBasepoint,
    ∃ zerothBaseClass :
      ZerothHomotopy
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
    ∃ piZeroBaseClass :
      HomotopyGroup.Pi 0
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        suppliedBasepoint,
    ∃ fundamentalBaseClass :
      FundamentalGroup
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        suppliedBasepoint,
    ∃ piOneBaseClass :
      HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        suppliedBasepoint,
      ConnectedSpace
        (({p} ∪ {q})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        Nonempty
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
            suppliedBasepoint) ∧
        Subsingleton
          (FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          a = b) ∧
        (∀ homotopyClass :
          ZerothHomotopy
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          homotopyClass = zerothBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 0
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          homotopyClass = piZeroBaseClass) ∧
        (∀ fundamentalClass :
          FundamentalGroup
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          fundamentalClass = fundamentalBaseClass) ∧
        (∀ homotopyClass :
          HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ :
              Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            suppliedBasepoint,
          homotopyClass = piOneBaseClass) ∧
        (∀ a b :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          Nonempty (Path a b)) ∧
        (∀ point :
          (({p} ∪ {q})ᶜ :
            Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
          pathComponent point = Set.univ) := by
  rcases
    onePoint_threeSpace_twoPointComplement_all_basepoint_lowHomotopy_baseclass_collapse_payloads
      hqp suppliedBasepoint with
    ⟨ lowHomotopyPayload
    , connected
    , nonempty
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalSubsingleton
    , piOneSubsingleton
    , zerothMkEq
    , piZeroEq
    , fundamentalEq
    , piOneEq
    , ⟨ zerothBaseClass, zerothBaseClassEq ⟩
    , ⟨ piZeroBaseClass, piZeroBaseClassEq ⟩
    , ⟨ fundamentalBaseClass, fundamentalBaseClassEq ⟩
    , ⟨ piOneBaseClass, piOneBaseClassEq ⟩
    , pathNonempty
    , pathComponentEqUniv
    ⟩
  exact
    ⟨ lowHomotopyPayload
    , zerothBaseClass
    , piZeroBaseClass
    , fundamentalBaseClass
    , piOneBaseClass
    , connected
    , nonempty
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalSubsingleton
    , piOneSubsingleton
    , zerothMkEq
    , piZeroEq
    , fundamentalEq
    , piOneEq
    , zerothBaseClassEq
    , piZeroBaseClassEq
    , fundamentalBaseClassEq
    , piOneBaseClassEq
    , pathNonempty
    , pathComponentEqUniv
    ⟩

end Poincare
