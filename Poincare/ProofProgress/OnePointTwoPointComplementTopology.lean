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

end Poincare
