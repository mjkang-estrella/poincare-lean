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

end Poincare
