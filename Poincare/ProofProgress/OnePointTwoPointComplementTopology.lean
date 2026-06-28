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

end Poincare
