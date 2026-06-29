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
The standard three-sphere two-puncture complement is connected.
-/
theorem threeSphere_twoPointComplement_connectedSpace
    {a b : ThreeSphere} (hab : b ≠ a) :
    ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  infer_instance

/--
The standard three-sphere two-puncture complement is nonempty.
-/
theorem threeSphere_twoPointComplement_nonempty
    {a b : ThreeSphere} (hab : b ≠ a) :
    Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) := by
  exact (threeSphere_twoPointComplement_pathConnectedSpace hab).nonempty

/--
The fundamental group of the standard three-sphere two-puncture complement has
a unique class at every basepoint.
-/
theorem threeSphere_twoPointComplement_fundamentalGroup_exists_unique
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ∃ baseClass : FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x,
      ∀ fundamentalClass :
        FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x,
        fundamentalClass = baseClass := by
  letI : Subsingleton
      (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_fundamentalGroup_subsingleton hab x
  exact ⟨Classical.choice inferInstance, fun fundamentalClass =>
    Subsingleton.elim _ _⟩

/--
The fundamental group of the standard three-sphere two-puncture complement is a
`Unique` type at every basepoint.
-/
@[reducible] noncomputable def threeSphere_twoPointComplement_fundamentalGroup_unique
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Unique (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  letI : Subsingleton
      (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_fundamentalGroup_subsingleton hab x
  exact
    { default := Classical.choice inferInstance
      uniq := fun fundamentalClass => Subsingleton.elim _ _ }

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
The first homotopy group of the standard three-sphere two-puncture complement
is a `Unique` type at every basepoint.
-/
@[reducible] noncomputable def threeSphere_twoPointComplement_piOne_unique
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Unique (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_piOne_subsingleton hab x
  exact
    { default := Classical.choice inferInstance
      uniq := fun homotopyClass => Subsingleton.elim _ _ }

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
The zeroth homotopy quotient of the standard three-sphere two-puncture
complement is a `Unique` type.
-/
@[reducible] noncomputable def threeSphere_twoPointComplement_zerothHomotopy_unique
    {a b : ThreeSphere} (hab : b ≠ a) :
    Unique (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere)) := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  let basePoint : (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    Classical.choice
      (PathConnectedSpace.nonempty
        (X := (({a} ∪ {b})ᶜ : Set ThreeSphere)))
  exact
    { default := ZerothHomotopy.mk basePoint
      uniq := fun homotopyClass => Subsingleton.elim _ _ }

/--
The zeroth homotopy group formulation of the standard three-sphere
two-puncture complement collapse.
-/
theorem threeSphere_twoPointComplement_piZero_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton
      (HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := (({a} ∪ {b})ᶜ : Set ThreeSphere))
      (x := x)).subsingleton_congr).mpr
        (threeSphere_twoPointComplement_zerothHomotopy_subsingleton hab)

/--
Any two zeroth homotopy group classes in the standard three-sphere
two-puncture complement agree.
-/
theorem threeSphere_twoPointComplement_piZero_eq
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (g h : HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :
    g = h := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_piZero_subsingleton hab x
  exact Subsingleton.elim _ _

/--
The zeroth homotopy group of the standard three-sphere two-puncture complement
has a unique class at every basepoint.
-/
theorem threeSphere_twoPointComplement_piZero_exists_unique
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ∃ baseClass :
      HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x,
      ∀ homotopyClass :
        HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_piZero_subsingleton hab x
  exact ⟨Classical.choice inferInstance, fun homotopyClass =>
    Subsingleton.elim _ _⟩

/--
The zeroth homotopy group of the standard three-sphere two-puncture complement
is a `Unique` type at every basepoint.
-/
@[reducible] noncomputable def threeSphere_twoPointComplement_piZero_unique
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Unique (HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) :=
    threeSphere_twoPointComplement_piZero_subsingleton hab x
  exact
    { default := Classical.choice inferInstance
      uniq := fun homotopyClass => Subsingleton.elim _ _ }

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

/--
Data-valued unique-instance form of the standard-sphere two-puncture
low-homotopy collapse.
-/
structure ThreeSphereTwoPointComplementLowHomotopyUniquePayload
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere)) where
  piOneUnique :
    Unique
      (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint)
  zerothUnique :
    Unique (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere))
  pathNonempty :
    ∀ x y : (({a} ∪ {b})ᶜ : Set ThreeSphere), Nonempty (Path x y)
  pathComponentEqUniv :
    ∀ x : (({a} ∪ {b})ᶜ : Set ThreeSphere), pathComponent x = Set.univ

/--
Unique-instance form of the standard-sphere two-puncture low-homotopy
collapse.  This packages the same pi0 and pi1 collapse as canonical uniqueness
objects for consumers that prefer typeclass-shaped contractibility data.
-/
noncomputable def threeSphere_twoPointComplement_lowHomotopyUnique_payload
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ThreeSphereTwoPointComplementLowHomotopyUniquePayload hab basepoint where
  piOneUnique := threeSphere_twoPointComplement_piOne_unique hab basepoint
  zerothUnique := threeSphere_twoPointComplement_zerothHomotopy_unique hab
  pathNonempty := threeSphere_twoPointComplement_path_nonempty hab
  pathComponentEqUniv := threeSphere_twoPointComplement_pathComponent_eq_univ hab

/--
Broader data-valued form of the standard-sphere two-puncture low-homotopy
collapse, including connectedness, nonemptiness, and fundamental-group
uniqueness alongside the pi1 and pi0 uniqueness payload.
-/
structure ThreeSphereTwoPointComplementCompleteLowHomotopyUniquePayload
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere)) where
  connected : ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere)
  nonempty : Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere)
  fundamentalGroupUnique :
    Unique (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint)
  piOneUnique :
    Unique
      (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint)
  piZeroUnique :
    Unique
      (HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint)
  zerothUnique :
    Unique (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere))
  pathNonempty :
    ∀ x y : (({a} ∪ {b})ᶜ : Set ThreeSphere), Nonempty (Path x y)
  pathComponentEqUniv :
    ∀ x : (({a} ∪ {b})ᶜ : Set ThreeSphere), pathComponent x = Set.univ

/--
Complete unique-instance payload for the standard three-sphere two-puncture
complement.
-/
noncomputable def threeSphere_twoPointComplement_completeLowHomotopyUnique_payload
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ThreeSphereTwoPointComplementCompleteLowHomotopyUniquePayload
      hab basepoint where
  connected := threeSphere_twoPointComplement_connectedSpace hab
  nonempty := threeSphere_twoPointComplement_nonempty hab
  fundamentalGroupUnique :=
    threeSphere_twoPointComplement_fundamentalGroup_unique hab basepoint
  piOneUnique := threeSphere_twoPointComplement_piOne_unique hab basepoint
  piZeroUnique := threeSphere_twoPointComplement_piZero_unique hab basepoint
  zerothUnique := threeSphere_twoPointComplement_zerothHomotopy_unique hab
  pathNonempty := threeSphere_twoPointComplement_path_nonempty hab
  pathComponentEqUniv := threeSphere_twoPointComplement_pathComponent_eq_univ hab

/--
The standard-sphere two-puncture endpoint can be consumed without an externally
chosen basepoint.  Nonemptiness selects one complement point, and the complete
unique-instance payload is returned together with the legacy low-homotopy
collapse tuple at that same basepoint.
-/
theorem threeSphere_twoPointComplement_completeLowHomotopyUnique_and_collapse_payload_with_basepoint
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∃ basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere),
      Nonempty
        (ThreeSphereTwoPointComplementCompleteLowHomotopyUniquePayload
          hab basepoint) ∧
      ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      Nonempty (Unique
        (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint)) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere)
          basepoint)) ∧
      Nonempty (Unique
        (HomotopyGroup.Pi 0 (({a} ∪ {b})ᶜ : Set ThreeSphere)
          basepoint)) ∧
      Nonempty (Unique
        (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere))) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere)
          basepoint) ∧
      (∀ g h :
        HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere)
          basepoint,
        g = h) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere)
          basepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere)
            basepoint,
          homotopyClass = baseClass) ∧
      Subsingleton
        (ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere)) ∧
      (∀ x y : (({a} ∪ {b})ᶜ : Set ThreeSphere),
        ZerothHomotopy.mk x = ZerothHomotopy.mk y) ∧
      (∃ baseClass : ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere),
        ∀ homotopyClass : ZerothHomotopy (({a} ∪ {b})ᶜ : Set ThreeSphere),
          homotopyClass = baseClass) ∧
      (∀ x y : (({a} ∪ {b})ᶜ : Set ThreeSphere), Nonempty (Path x y)) ∧
      (∀ x : (({a} ∪ {b})ᶜ : Set ThreeSphere),
        pathComponent x = Set.univ) := by
  let basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    Classical.choice (threeSphere_twoPointComplement_nonempty hab)
  let payload :=
    threeSphere_twoPointComplement_completeLowHomotopyUnique_payload
      hab basepoint
  rcases threeSphere_twoPointComplement_lowHomotopyCollapse_payload
      hab basepoint with
    ⟨piOneSubsingleton, piOneEq, piOneExistsUnique,
      zerothSubsingleton, zerothEq, zerothExistsUnique,
      pathNonempty, pathComponentEqUniv⟩
  exact
    ⟨ basepoint
    , ⟨payload⟩
    , payload.connected
    , payload.nonempty
    , ⟨payload.fundamentalGroupUnique⟩
    , ⟨payload.piOneUnique⟩
    , ⟨payload.piZeroUnique⟩
    , ⟨payload.zerothUnique⟩
    , piOneSubsingleton
    , piOneEq
    , piOneExistsUnique
    , zerothSubsingleton
    , zerothEq
    , zerothExistsUnique
    , pathNonempty
    , pathComponentEqUniv
    ⟩

end Poincare
