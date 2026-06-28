import Poincare.Statement

namespace Poincare

/--
The two-puncture complement in the standard three-sphere has trivial
fundamental group at every basepoint.
-/
theorem threeSphere_twoPointComplement_fundamentalGroup_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  letI : SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hab
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/--
The equivalent first homotopy group formulation of the two-puncture complement
triviality.
-/
theorem threeSphere_twoPointComplement_piOne_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  exact ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := (({a} ∪ {b})ᶜ : Set ThreeSphere)) (x := x)).subsingleton_congr).mpr
      (threeSphere_twoPointComplement_fundamentalGroup_subsingleton hab x)

/--
Any two first homotopy group classes in the standard three-sphere
two-puncture complement agree.
-/
theorem threeSphere_twoPointComplement_piOne_eq
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (g h : HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :
    g = h := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_piOne_subsingleton hab x
  exact Subsingleton.elim _ _

/--
The first homotopy group of the standard three-sphere two-puncture complement
has a unique class at every basepoint.
-/
theorem threeSphere_twoPointComplement_piOne_exists_unique
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ∃ baseClass : HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x,
      ∀ homotopyClass :
        HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_piOne_subsingleton hab x
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The zeroth homotopy quotient of the standard three-sphere two-puncture
complement is subsingleton.
-/
theorem threeSphere_twoPointComplement_zerothHomotopy_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a) :
    Subsingleton (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere)) := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  infer_instance

/--
Any two zeroth homotopy classes in the standard three-sphere two-puncture
complement agree.
-/
theorem threeSphere_twoPointComplement_zerothHomotopy_mk_eq
    {a b : ThreeSphere} (hab : b ≠ a)
    (x y : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ZerothHomotopy.mk x = ZerothHomotopy.mk y := by
  letI : Subsingleton (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere)) :=
    threeSphere_twoPointComplement_zerothHomotopy_subsingleton hab
  exact Subsingleton.elim _ _

/--
The zeroth homotopy quotient of the standard three-sphere two-puncture
complement has a unique class.
-/
theorem threeSphere_twoPointComplement_zerothHomotopy_exists_unique
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∃ baseClass : ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere),
      ∀ homotopyClass : ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere),
        homotopyClass = baseClass := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  let basePoint : (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    Classical.choice
      (PathConnectedSpace.nonempty
        (X := (({a} ∪ {b})ᶜ : Set ThreeSphere)))
  exact ⟨ZerothHomotopy.mk basePoint, fun homotopyClass => Subsingleton.elim _ _⟩

/--
Any two points in the standard three-sphere two-puncture complement are joined
by a path.
-/
theorem threeSphere_twoPointComplement_path_nonempty
    {a b : ThreeSphere} (hab : b ≠ a)
    (x y : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Nonempty (Path x y) := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  exact PathConnectedSpace.joined x y

/--
The path component of every point in the standard three-sphere two-puncture
complement is the whole complement.
-/
theorem threeSphere_twoPointComplement_pathComponent_eq_univ
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    pathComponent x = Set.univ := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  ext y
  constructor
  · intro _hy
    exact Set.mem_univ y
  · intro _hy
    exact PathConnectedSpace.joined x y

/--
Compact standard-sphere two-puncture low-homotopy collapse package: every
zeroth and first homotopy class is unique, and every pair of complement points
is joined by a path.
-/
theorem threeSphere_twoPointComplement_lowHomotopyCollapse_payload
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton
        (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) ∧
      (∀ g h :
        HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
        g = h) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
          homotopyClass = baseClass) ∧
      Subsingleton (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere)) ∧
      (∀ x y : (({a} ∪ {b})ᶜ : Set ThreeSphere),
        ZerothHomotopy.mk x = ZerothHomotopy.mk y) ∧
      (∃ baseClass : ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere),
        ∀ homotopyClass : ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere),
          homotopyClass = baseClass) ∧
      (∀ x y : (({a} ∪ {b})ᶜ : Set ThreeSphere), Nonempty (Path x y)) ∧
      (∀ x : (({a} ∪ {b})ᶜ : Set ThreeSphere),
        pathComponent x = Set.univ) :=
  ⟨ threeSphere_twoPointComplement_piOne_subsingleton hab basepoint
  , threeSphere_twoPointComplement_piOne_eq hab basepoint
  , threeSphere_twoPointComplement_piOne_exists_unique hab basepoint
  , threeSphere_twoPointComplement_zerothHomotopy_subsingleton hab
  , threeSphere_twoPointComplement_zerothHomotopy_mk_eq hab
  , threeSphere_twoPointComplement_zerothHomotopy_exists_unique hab
  , threeSphere_twoPointComplement_path_nonempty hab
  , threeSphere_twoPointComplement_pathComponent_eq_univ hab
  ⟩

end Poincare
