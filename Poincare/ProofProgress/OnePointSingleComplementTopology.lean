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
Deleting one point from the one-point compactification model leaves a
path-connected space.
-/
theorem onePoint_threeSpace_compl_singleton_pathConnectedSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : ContractibleSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_contractibleSpace p
  infer_instance

/--
Any two points in the singleton complement are joined by a path.
-/
theorem onePoint_threeSpace_compl_singleton_path_nonempty
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∀ (x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))),
      Nonempty (Path x y) := by
  intro x y
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  exact PathConnectedSpace.joined x y

/--
The path component of any point in the singleton complement is the whole
singleton complement.
-/
theorem onePoint_threeSpace_compl_singleton_pathComponent_eq_univ
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    pathComponent x = Set.univ := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  ext y
  constructor
  · intro _hy
    exact Set.mem_univ y
  · intro _hy
    exact PathConnectedSpace.joined x y

/--
The zeroth homotopy quotient of the singleton complement has only one class.
-/
theorem onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Subsingleton
      (ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

/--
Any two zeroth-homotopy classes in the singleton complement agree.
-/
theorem onePoint_threeSpace_compl_singleton_zerothHomotopy_mk_eq
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ZerothHomotopy.mk x = ZerothHomotopy.mk y := by
  letI : Subsingleton
      (ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :=
    onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p
  exact Subsingleton.elim _ _

/--
The zeroth homotopy quotient of the singleton complement has a unique class.
-/
theorem onePoint_threeSpace_compl_singleton_zerothHomotopy_exists_unique
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∃ baseClass :
      ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∀ homotopyClass :
        ZerothHomotopy
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        homotopyClass = baseClass := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  let basePoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    Classical.choice
      (PathConnectedSpace.nonempty
        (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))))
  exact ⟨ZerothHomotopy.mk basePoint, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The zeroth homotopy group formulation of the singleton-complement collapse.
-/
theorem onePoint_threeSpace_compl_singleton_piZero_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := x)).subsingleton_congr).mpr
        (onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p)

/--
Any two zeroth homotopy group classes in the singleton complement agree.
-/
theorem onePoint_threeSpace_compl_singleton_piZero_eq
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (a b :
      HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :
    a = b := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_piZero_subsingleton p x
  exact Subsingleton.elim _ _

/--
The zeroth homotopy group of the singleton complement has a unique class.
-/
theorem onePoint_threeSpace_compl_singleton_piZero_exists_unique
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ baseClass :
      HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
      ∀ homotopyClass :
        HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_piZero_subsingleton p x
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
Simple-connectedness of the singleton complement collapses its based
fundamental group.
-/
theorem onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton (FundamentalGroup
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  letI : SimplyConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/--
Any two based fundamental-group classes in the singleton complement agree.
-/
theorem onePoint_threeSpace_compl_singleton_fundamentalGroup_eq
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (a b : FundamentalGroup
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :
    a = b := by
  letI : Subsingleton
      (FundamentalGroup
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton p x
  exact Subsingleton.elim _ _

/--
The based fundamental group of the singleton complement has a unique class.
-/
theorem onePoint_threeSpace_compl_singleton_fundamentalGroup_exists_unique
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ baseClass :
      FundamentalGroup
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
      ∀ fundamentalClass :
        FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
        fundamentalClass = baseClass := by
  letI : Subsingleton
      (FundamentalGroup
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton p x
  exact ⟨Classical.choice inferInstance, fun fundamentalClass => Subsingleton.elim _ _⟩

/--
The equivalent first homotopy group formulation of singleton-complement
triviality.
-/
theorem onePoint_threeSpace_compl_singleton_piOne_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton (HomotopyGroup.Pi 1
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (x := x)).subsingleton_congr).mpr
        (onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton p x)

/--
Any two first homotopy group classes in the singleton complement agree.
-/
theorem onePoint_threeSpace_compl_singleton_piOne_eq
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (a b :
      HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :
    a = b := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_piOne_subsingleton p x
  exact Subsingleton.elim _ _

/--
The first homotopy group of the singleton complement has a unique class.
-/
theorem onePoint_threeSpace_compl_singleton_piOne_exists_unique
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ baseClass :
      HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
      ∀ homotopyClass :
        HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) x) :=
    onePoint_threeSpace_compl_singleton_piOne_subsingleton p x
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The singleton complement is connected as a direct consequence of the named
path-connectedness theorem above.
-/
theorem onePoint_threeSpace_compl_singleton_connectedSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

/--
The singleton complement is nonempty, witnessed by its path-connected topology.
-/
theorem onePoint_threeSpace_compl_singleton_nonempty
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Nonempty
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

/--
Recognition-facing payload for the one-point compactification singleton
complement.  It packages the Euclidean chart, contractibility, simple
connectedness, connectedness/nonemptiness, low-homotopy collapse, and
path-component collapse for downstream topology extraction.
-/
structure OnePointSingletonComplementRecognitionPayload
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) where
  euclideanChart :
    Nonempty
      (({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
        EuclideanSpace ℝ (Fin 3))
  contractible :
    ContractibleSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  pathConnected :
    PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  simplyConnected :
    SimplyConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  connected :
    ConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  nonempty :
    Nonempty
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
  zerothHomotopySubsingleton :
    Subsingleton
      (ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
  piZeroSubsingleton :
    Subsingleton
      (HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint)
  fundamentalGroupSubsingleton :
    Subsingleton
      (FundamentalGroup
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint)
  piOneSubsingleton :
    Subsingleton
      (HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint)
  zerothHomotopyUnique :
    ∃ baseClass :
      ZerothHomotopy
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      ∀ homotopyClass :
        ZerothHomotopy
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        homotopyClass = baseClass
  piZeroUnique :
    ∃ baseClass :
      HomotopyGroup.Pi 0
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
      ∀ homotopyClass :
        HomotopyGroup.Pi 0
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
        homotopyClass = baseClass
  fundamentalGroupUnique :
    ∃ baseClass :
      FundamentalGroup
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
      ∀ fundamentalClass :
        FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
        fundamentalClass = baseClass
  piOneUnique :
    ∃ baseClass :
      HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
      ∀ homotopyClass :
        HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
        homotopyClass = baseClass
  pathNonempty :
    ∀ x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      Nonempty (Path x y)
  pathComponentEqUniv :
    ∀ x : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))),
      pathComponent x = Set.univ

/--
The singleton complement in the one-point compactification model supplies all
recognition-facing topology and low-homotopy witnesses in one field-based
object.
-/
noncomputable def onePoint_threeSpace_compl_singleton_recognition_payload
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    OnePointSingletonComplementRecognitionPayload p basepoint where
  euclideanChart :=
    ⟨onePoint_threeSpace_compl_singleton_homeomorph_euclidean p⟩
  contractible := onePoint_threeSpace_compl_singleton_contractibleSpace p
  pathConnected := onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  simplyConnected := onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
  connected := onePoint_threeSpace_compl_singleton_connectedSpace p
  nonempty := onePoint_threeSpace_compl_singleton_nonempty p
  zerothHomotopySubsingleton :=
    onePoint_threeSpace_compl_singleton_zerothHomotopy_subsingleton p
  piZeroSubsingleton :=
    onePoint_threeSpace_compl_singleton_piZero_subsingleton p basepoint
  fundamentalGroupSubsingleton :=
    onePoint_threeSpace_compl_singleton_fundamentalGroup_subsingleton
      p basepoint
  piOneSubsingleton :=
    onePoint_threeSpace_compl_singleton_piOne_subsingleton p basepoint
  zerothHomotopyUnique :=
    onePoint_threeSpace_compl_singleton_zerothHomotopy_exists_unique p
  piZeroUnique :=
    onePoint_threeSpace_compl_singleton_piZero_exists_unique p basepoint
  fundamentalGroupUnique :=
    onePoint_threeSpace_compl_singleton_fundamentalGroup_exists_unique
      p basepoint
  piOneUnique :=
    onePoint_threeSpace_compl_singleton_piOne_exists_unique p basepoint
  pathNonempty := onePoint_threeSpace_compl_singleton_path_nonempty p
  pathComponentEqUniv :=
    onePoint_threeSpace_compl_singleton_pathComponent_eq_univ p

/--
Tuple projection of the singleton-complement recognition payload for consumers
that only need the chart, contractibility, simple connectedness, and the
field-based payload inhabitant.
-/
theorem onePoint_threeSpace_compl_singleton_recognition_payload_tuple
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Nonempty
      (({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
        EuclideanSpace ℝ (Fin 3)) ∧
      ContractibleSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty (OnePointSingletonComplementRecognitionPayload p basepoint) :=
  let payload :=
    onePoint_threeSpace_compl_singleton_recognition_payload p basepoint
  ⟨ payload.euclideanChart
  , payload.contractible
  , payload.simplyConnected
  , ⟨payload⟩ ⟩

end Poincare
