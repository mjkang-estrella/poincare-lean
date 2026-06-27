import Poincare.TopologyExtraction

namespace Poincare

/--
Path-component equality data with a chosen path from the basepoint to every
target. This packages the usable path-level content of
`pathComponent basepoint = Set.univ`.
-/
structure PointedPathComponentPathData
    (X : Type u) [TopologicalSpace X] (basepoint : X) : Type u where
  component_univ : pathComponent basepoint = Set.univ
  joined_to : ∀ z : X, Joined basepoint z
  path_to : ∀ z : X, Path basepoint z

/--
Endpoint-level data for a chosen path from a fixed basepoint. This is the
usable proof object downstream constructions need when they must evaluate the
path at `0` and `1`, not only know that some path exists.
-/
structure PointedChosenPathEndpointData
    (X : Type u) [TopologicalSpace X] (basepoint z : X) : Type u where
  path : Path basepoint z
  source_eq : path 0 = basepoint
  target_eq : path 1 = z
  joined : Joined basepoint z

/--
If a basepoint's path component is all of a space, then every target is joined
to that basepoint. This is the direct path-component elimination used by the
puncture-complement bundles below.
-/
theorem joined_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) :
    ∀ z : X, Joined basepoint z := by
  intro z
  rw [← mem_pathComponent_iff]
  rw [hcomponent]
  exact Set.mem_univ z

/--
The path-component equality gives an actual path witness between the basepoint
and each target.
-/
theorem path_nonempty_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) :
    ∀ z : X, Nonempty (Path basepoint z) :=
  joined_of_pathComponent_eq_univ basepoint hcomponent

/--
Choose a concrete path from the path-component equality. Downstream code that
needs a `Path`, rather than merely a `Joined` proposition, can consume this
field through `PointedPathComponentPathData.path_to`.
-/
noncomputable def chosenPath_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) (z : X) :
    Path basepoint z :=
  (joined_of_pathComponent_eq_univ basepoint hcomponent z).somePath

/-- The chosen path starts at the selected basepoint. -/
theorem chosenPath_source_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) (z : X) :
    chosenPath_of_pathComponent_eq_univ basepoint hcomponent z 0 = basepoint := by
  simp [chosenPath_of_pathComponent_eq_univ]

/-- The chosen path ends at the requested target point. -/
theorem chosenPath_target_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) (z : X) :
    chosenPath_of_pathComponent_eq_univ basepoint hcomponent z 1 = z := by
  simp [chosenPath_of_pathComponent_eq_univ]

/--
The selected path itself is a concrete witness of the corresponding `Joined`
fact.
-/
theorem chosenPath_joined_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) (z : X) :
    Joined basepoint z :=
  ⟨chosenPath_of_pathComponent_eq_univ basepoint hcomponent z⟩

/--
Bundle the path-component equality together with the joined and concrete-path
consequences extracted from it.
-/
noncomputable def pointedPathComponentPathData_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) :
    PointedPathComponentPathData X basepoint where
  component_univ := hcomponent
  joined_to := joined_of_pathComponent_eq_univ basepoint hcomponent
  path_to := chosenPath_of_pathComponent_eq_univ basepoint hcomponent

/--
Package the concrete chosen path, its endpoints, and its `Joined` witness from
a full path-component equality.
-/
noncomputable def chosenPathEndpointData_of_pathComponent_eq_univ
    {X : Type u} [TopologicalSpace X] (basepoint : X)
    (hcomponent : pathComponent basepoint = Set.univ) (z : X) :
    PointedChosenPathEndpointData X basepoint z where
  path := chosenPath_of_pathComponent_eq_univ basepoint hcomponent z
  source_eq := chosenPath_source_of_pathComponent_eq_univ basepoint hcomponent z
  target_eq := chosenPath_target_of_pathComponent_eq_univ basepoint hcomponent z
  joined := chosenPath_joined_of_pathComponent_eq_univ basepoint hcomponent z

/--
Transport a recognized one-point compactification target's single-puncture
complement to the Euclidean chart of the model compactification.
-/
noncomputable def homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3) := by
  let eM : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)) := Classical.choice h
  let hCompl :
      ({x}ᶜ : Set M) ≃ₜ
        ({eM x}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    eM.subtype (fun y => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · intro hy hyeq
        exact hy (eM.injective hyeq)
      · intro hy hyx
        exact hy (by rw [hyx]))
  exact hCompl.trans
    (onePoint_threeSpace_compl_singleton_homeomorph_euclidean (eM x))

/--
Every single-puncture complement of a space recognized as the one-point
compactification of `R^3` is contractible.
-/
theorem compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) :=
  (homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    h x).contractibleSpace

/--
Every based loop in a single-puncture complement of a recognized one-point
compactification target is null-homotopic.
-/
theorem compl_singleton_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ∀ (basepoint : ({x}ᶜ : Set M)) (γ : Path basepoint basepoint),
      Path.Homotopic γ (Path.refl basepoint) := by
  intro basepoint γ
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace h x
  exact SimplyConnectedSpace.paths_homotopic γ (Path.refl basepoint)

/--
Any two paths with the same endpoints in a single-puncture complement of a
recognized one-point compactification target are homotopic.
-/
theorem compl_singleton_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ∀ {a b : ({x}ᶜ : Set M)} (γ₀ γ₁ : Path a b),
      Path.Homotopic γ₀ γ₁ := by
  intro a b γ₀ γ₁
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace h x
  exact SimplyConnectedSpace.paths_homotopic γ₀ γ₁

/--
Any two points in a single-puncture complement of a recognized one-point
compactification target are joined by an actual path.
-/
theorem compl_singleton_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Nonempty (Path a b) := by
  intro a b
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace h x
  exact PathConnectedSpace.joined a b

/--
The same single-puncture path extraction, stated in mathlib's `Joined`
relation so path-component consumers can use it directly.
-/
theorem compl_singleton_joined_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Joined a b := by
  intro a b
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace h x
  exact PathConnectedSpace.joined a b

/--
Every point of a single-puncture complement lies in the path component of any
chosen basepoint after transport from the one-point compactification model.
-/
theorem compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    pathComponent basepoint = Set.univ := by
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace h x
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact PathConnectedSpace.joined basepoint y

/--
The transported single-puncture path-component equality carries a complete
basepointed path-data bundle: every target point comes with a selected path
from the chosen basepoint.
-/
noncomputable def compl_singleton_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    PointedPathComponentPathData ({x}ᶜ : Set M) basepoint :=
  pointedPathComponentPathData_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h x basepoint)

/--
Extract a concrete path from the chosen basepoint to any point of the
transported single-puncture complement.
-/
noncomputable def compl_singleton_chosenPath_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    Path basepoint z :=
  (compl_singleton_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace
    h x basepoint).path_to z

/--
The transported single-puncture chosen path carries its endpoint equalities and
is itself the chosen `Joined` witness from the basepoint to the target.
-/
noncomputable def compl_singleton_chosenPathEndpointData_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    PointedChosenPathEndpointData ({x}ᶜ : Set M) basepoint z :=
  chosenPathEndpointData_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h x basepoint) z

/-- The transported single-puncture chosen path starts at its basepoint. -/
theorem compl_singleton_chosenPath_source_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    compl_singleton_chosenPath_of_homeomorph_to_onePoint_threeSpace
      h x basepoint z 0 = basepoint := by
  exact chosenPath_source_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h x basepoint) z

/-- The transported single-puncture chosen path ends at its target point. -/
theorem compl_singleton_chosenPath_target_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    compl_singleton_chosenPath_of_homeomorph_to_onePoint_threeSpace
      h x basepoint z 1 = z := by
  exact chosenPath_target_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h x basepoint) z

/--
The transported single-puncture chosen path is a concrete witness that the
basepoint is joined to the target.
-/
theorem compl_singleton_chosenPath_joined_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    Joined basepoint z :=
  ⟨compl_singleton_chosenPath_of_homeomorph_to_onePoint_threeSpace
    h x basepoint z⟩

/--
A recognized one-point compactification target gives an explicit path between a
basepoint and target in any single-puncture complement, together with both
endpoint equations.
-/
theorem compl_singleton_exists_path_with_endpoints_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z := by
  refine ⟨compl_singleton_chosenPath_of_homeomorph_to_onePoint_threeSpace
    h x basepoint z, ?_, ?_, ?_⟩
  · exact compl_singleton_chosenPath_source_of_homeomorph_to_onePoint_threeSpace
      h x basepoint z
  · exact compl_singleton_chosenPath_target_of_homeomorph_to_onePoint_threeSpace
      h x basepoint z
  · exact compl_singleton_chosenPath_joined_of_homeomorph_to_onePoint_threeSpace
      h x basepoint z

/--
Every path-homotopy quotient in a single-puncture complement of a recognized
one-point compactification target is a subsingleton.
-/
theorem compl_singleton_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)),
      Subsingleton (Path.Homotopic.Quotient a b) := by
  intro a b
  rw [subsingleton_iff]
  intro γ η
  induction γ using Quotient.inductionOn with
  | h γ =>
    induction η using Quotient.inductionOn with
    | h η =>
      exact Quotient.sound
        (compl_singleton_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
          h x γ η)

/--
The based fundamental group of every single-puncture complement of a recognized
one-point compactification target is trivial.
-/
theorem compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) := by
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  exact
    compl_singleton_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
      h x basepoint basepoint

/--
The same single-puncture triviality, stated for mathlib's first homotopy group.
-/
theorem compl_singleton_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := ({x}ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
    (compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
      h x basepoint)

/--
Transport a recognized one-point compactification target's two-puncture
complement to the punctured Euclidean chart of the model compactification.
-/
theorem exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  rcases h with ⟨eM⟩
  have hImage : eM y ≠ eM x := by
    intro hxy
    exact hyx (eM.injective hxy)
  let puncture : EuclideanSpace ℝ (Fin 3) :=
    onePoint_threeSpace_compl_singleton_homeomorph_euclidean (eM x)
      (onePoint_threeSpace_pointInComplement hImage)
  let hCompl :
      (({x} ∪ {y})ᶜ : Set M) ≃ₜ
        (({eM x} ∪ {eM y})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    eM.subtype (fun z => by
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hz hzImage
        rcases hzImage with hzx | hzy
        · exact hz (Or.inl (eM.injective hzx))
        · exact hz (Or.inr (eM.injective hzy))
      · intro hz hzSource
        rcases hzSource with hzx | hzy
        · exact hz (Or.inl (by rw [hzx]))
        · exact hz (Or.inr (by rw [hzy])))
  exact ⟨puncture,
    ⟨hCompl.trans
      (onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean
        hImage)⟩⟩

/--
Expose the transported two-puncture Euclidean chart as a concrete payload,
including both the image puncture and the homeomorphism to its complement.
-/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∀ z, (chart z : EuclideanSpace ℝ (Fin 3)) ≠ puncture := by
  rcases h with ⟨eM⟩
  have hImage : eM y ≠ eM x := by
    intro hxy
    exact hyx (eM.injective hxy)
  let puncture : EuclideanSpace ℝ (Fin 3) :=
    onePoint_threeSpace_compl_singleton_homeomorph_euclidean (eM x)
      (onePoint_threeSpace_pointInComplement hImage)
  let hCompl :
      (({x} ∪ {y})ᶜ : Set M) ≃ₜ
        (({eM x} ∪ {eM y})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    eM.subtype (fun z => by
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hz hzImage
        rcases hzImage with hzx | hzy
        · exact hz (Or.inl (eM.injective hzx))
        · exact hz (Or.inr (eM.injective hzy))
      · intro hz hzSource
        rcases hzSource with hzx | hzy
        · exact hz (Or.inl (by rw [hzx]))
        · exact hz (Or.inr (by rw [hzy])))
  let chart :=
    hCompl.trans
      (onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean
        hImage)
  refine ⟨puncture, chart, ?_⟩
  intro z
  exact (chart z).2

/--
Every two-puncture complement of a space recognized as the one-point
compactification of `R^3` is simply connected.
-/
theorem twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  rcases h with ⟨eM⟩
  have hImage : eM y ≠ eM x := by
    intro hxy
    exact hyx (eM.injective hxy)
  let hCompl :
      (({x} ∪ {y})ᶜ : Set M) ≃ₜ
        (({eM x} ∪ {eM y})ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    eM.subtype (fun z => by
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hz hzImage
        rcases hzImage with hzx | hzy
        · exact hz (Or.inl (eM.injective hzx))
        · exact hz (Or.inr (eM.injective hzy))
      · intro hz hzSource
        rcases hzSource with hzx | hzy
        · exact hz (Or.inl (by rw [hzx]))
        · exact hz (Or.inr (by rw [hzy])))
  letI : SimplyConnectedSpace
      (({eM x} ∪ {eM y})ᶜ :
        Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hImage
  exact hCompl.toHomotopyEquiv.simplyConnectedSpace

/--
Every two-puncture complement of a recognized one-point compactification
target is path-connected.
-/
theorem twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  infer_instance

/--
Every two-puncture complement of a recognized one-point compactification
target is connected.
-/
theorem twoPointComplement_connectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  infer_instance

/--
Every two-puncture complement of a recognized one-point compactification
target is nonempty.
-/
theorem twoPointComplement_nonempty_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    Nonempty (({x} ∪ {y})ᶜ : Set M) := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  infer_instance

/--
The topology package for every two-puncture complement of a space recognized as
the one-point compactification of `R^3`: nonemptiness, path-connectedness,
connectedness, and simple connectedness.
-/
theorem twoPointComplement_topology_package_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
      PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  ⟨twoPointComplement_nonempty_of_homeomorph_to_onePoint_threeSpace h hyx,
    twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace h hyx,
    twoPointComplement_connectedSpace_of_homeomorph_to_onePoint_threeSpace h hyx,
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx⟩

/-- Theorem contract for `twoPointComplement_topology_package_of_homeomorph_to_onePoint_threeSpace`. -/
theorem twoPointComplement_topology_package_of_homeomorph_to_onePoint_threeSpace_eq :
    @Poincare.twoPointComplement_topology_package_of_homeomorph_to_onePoint_threeSpace =
      @Poincare.twoPointComplement_topology_package_of_homeomorph_to_onePoint_threeSpace :=
  rfl

/--
The transported two-puncture Euclidean chart also carries the concrete topology
payload needed downstream: the image avoids the transported puncture, and the
source complement is nonempty, path-connected, and simply connected.
-/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ z, (chart z : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
          Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
          PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  rcases
    exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
      h hyx with ⟨puncture, chart, hAvoidsPuncture⟩
  have hSimply :
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  have hPath :
      PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  have hNonempty : Nonempty (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_nonempty_of_homeomorph_to_onePoint_threeSpace h hyx
  exact ⟨puncture, chart, hAvoidsPuncture, hNonempty, hPath, hSimply⟩

/--
The transported two-puncture Euclidean chart with the full concrete topology
payload, including connectedness in addition to nonemptiness,
path-connectedness, and simple connectedness.
-/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ z, (chart z : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
          Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
          PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  rcases
      exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
        h hyx with
    ⟨puncture, chart, hAvoidsPuncture⟩
  rcases twoPointComplement_topology_package_of_homeomorph_to_onePoint_threeSpace h hyx with
    ⟨hNonempty, hPath, hConnected, hSimply⟩
  exact
    ⟨puncture, chart, hAvoidsPuncture, hNonempty, hPath, hConnected, hSimply⟩

/-- Theorem contract for `exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload`. -/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload_eq :
    @Poincare.exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload =
      @Poincare.exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload :=
  rfl

/--
The based fundamental group of every two-puncture complement of a recognized
one-point compactification target is trivial.
-/
theorem twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  infer_instance

/--
Every based loop in a two-puncture complement of a recognized one-point
compactification target is null-homotopic.
-/
theorem twoPointComplement_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∀ (basepoint : (({x} ∪ {y})ᶜ : Set M))
      (γ : Path basepoint basepoint), Path.Homotopic γ (Path.refl basepoint) := by
  intro basepoint γ
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  exact SimplyConnectedSpace.paths_homotopic γ (Path.refl basepoint)

/--
Any two paths with the same endpoints in a two-puncture complement of a
recognized one-point compactification target are homotopic.
-/
theorem twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∀ {a b : (({x} ∪ {y})ᶜ : Set M)} (γ η : Path a b),
      Path.Homotopic γ η := by
  intro a b γ η
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  exact SimplyConnectedSpace.paths_homotopic γ η

/--
Any two points in a two-puncture complement of a recognized one-point
compactification target are joined by an actual path.
-/
theorem twoPointComplement_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Nonempty (Path a b) := by
  intro a b
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  exact PathConnectedSpace.joined a b

/--
The same two-puncture path extraction, stated in mathlib's `Joined` relation.
-/
theorem twoPointComplement_joined_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Joined a b := by
  intro a b
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  exact PathConnectedSpace.joined a b

/--
Every point of a two-puncture complement lies in the path component of any
chosen basepoint after transport from the one-point compactification model.
-/
theorem twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    pathComponent basepoint = Set.univ := by
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
      h hyx
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    exact PathConnectedSpace.joined basepoint z

/--
The transported two-puncture path-component equality carries a complete
basepointed path-data bundle: every target point comes with a selected path
from the chosen basepoint.
-/
noncomputable def twoPointComplement_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) basepoint :=
  pointedPathComponentPathData_of_pathComponent_eq_univ basepoint
    (twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint)

/--
Extract a concrete path from the chosen basepoint to any point of the
transported two-puncture complement.
-/
noncomputable def twoPointComplement_chosenPath_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    Path basepoint z :=
  (twoPointComplement_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace
    h hyx basepoint).path_to z

/--
The transported two-puncture chosen path carries its endpoint equalities and is
itself the chosen `Joined` witness from the basepoint to the target.
-/
noncomputable def twoPointComplement_chosenPathEndpointData_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    PointedChosenPathEndpointData (({x} ∪ {y})ᶜ : Set M) basepoint z :=
  chosenPathEndpointData_of_pathComponent_eq_univ basepoint
    (twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint) z

/-- The transported two-puncture chosen path starts at its basepoint. -/
theorem twoPointComplement_chosenPath_source_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    twoPointComplement_chosenPath_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint z 0 = basepoint := by
  simpa [twoPointComplement_chosenPath_of_homeomorph_to_onePoint_threeSpace,
    twoPointComplement_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace,
    pointedPathComponentPathData_of_pathComponent_eq_univ] using
    chosenPath_source_of_pathComponent_eq_univ basepoint
      (twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint) z

/-- The transported two-puncture chosen path ends at its target point. -/
theorem twoPointComplement_chosenPath_target_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    twoPointComplement_chosenPath_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint z 1 = z := by
  simpa [twoPointComplement_chosenPath_of_homeomorph_to_onePoint_threeSpace,
    twoPointComplement_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace,
    pointedPathComponentPathData_of_pathComponent_eq_univ] using
    chosenPath_target_of_pathComponent_eq_univ basepoint
      (twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint) z

/--
The transported two-puncture chosen path is a concrete witness that the
basepoint is joined to the target.
-/
theorem twoPointComplement_chosenPath_joined_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    Joined basepoint z :=
  ⟨twoPointComplement_chosenPath_of_homeomorph_to_onePoint_threeSpace
    h hyx basepoint z⟩

/--
A recognized one-point compactification target gives an explicit path between a
basepoint and target in any two-puncture complement, together with both
endpoint equations.
-/
theorem twoPointComplement_exists_path_with_endpoints_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z := by
  refine ⟨twoPointComplement_chosenPath_of_homeomorph_to_onePoint_threeSpace
    h hyx basepoint z, ?_, ?_, ?_⟩
  · exact twoPointComplement_chosenPath_source_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint z
  · exact twoPointComplement_chosenPath_target_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint z
  · exact twoPointComplement_chosenPath_joined_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint z

/--
The transported two-puncture topology payload also supplies the selected path
data needed by downstream fundamental-group and quotient arguments: a concrete
path from a chosen basepoint to a target, both endpoint equalities, and the
corresponding `Joined` witness.
-/
theorem exists_puncture_homeomorph_twoPointComplement_chosenPathTopologyPayload
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({x} ∪ {y})ᶜ : Set M) basepoint z,
            ∃ γ : Path basepoint z,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                pathData.path_to z = γ ∧
                endpointData.path = γ ∧
                γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z := by
  rcases
    exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload
      h hyx with
    ⟨puncture, chart, hAvoidsPuncture, hNonempty, hPath, hSimply⟩
  let pathData :
      PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) basepoint :=
    twoPointComplement_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint
  let endpointData :
      PointedChosenPathEndpointData
        (({x} ∪ {y})ᶜ : Set M) basepoint z :=
    twoPointComplement_chosenPathEndpointData_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint z
  let γ : Path basepoint z := endpointData.path
  have hPathData : pathData.path_to z = γ := by
    rfl
  have hEndpointPath : endpointData.path = γ := by
    rfl
  have hSource : γ 0 = basepoint := by
    change endpointData.path 0 = basepoint
    exact endpointData.source_eq
  have hTarget : γ 1 = z := by
    change endpointData.path 1 = z
    exact endpointData.target_eq
  have hJoined : Joined basepoint z := endpointData.joined
  exact
    ⟨puncture, chart, pathData, endpointData, γ, hAvoidsPuncture, hNonempty,
      hPath, hSimply, hPathData, hEndpointPath, hSource, hTarget, hJoined⟩

/--
Every path-homotopy quotient in a two-puncture complement of a recognized
one-point compactification target is a subsingleton.
-/
theorem twoPointComplement_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)),
      Subsingleton (Path.Homotopic.Quotient a b) := by
  intro a b
  rw [subsingleton_iff]
  intro γ η
  induction γ using Quotient.inductionOn with
  | h γ =>
    induction η using Quotient.inductionOn with
    | h η =>
      exact Quotient.sound
        (twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
          h hyx γ η)

/--
The same two-puncture triviality, stated for mathlib's first homotopy group.
-/
theorem twoPointComplement_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := (({x} ∪ {y})ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
    (twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint)

/--
A recognized one-point compactification target supplies a full two-puncture
path/loop projection payload: a canonical chosen path with endpoint equations,
homotopy uniqueness against any supplied path, quotient collapse, loop
nullhomotopy, and trivial first homotopy group.
-/
theorem twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint target : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ canonicalPath : Path basepoint target,
      Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        pathComponent basepoint = Set.univ ∧
        canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
        Joined basepoint target ∧
        Path.Homotopic chosenPath canonicalPath ∧
        (⟦chosenPath⟧ :
          Path.Homotopic.Quotient basepoint target) =
          ⟦canonicalPath⟧ ∧
        (∀ η : Path basepoint target,
          Path.Homotopic canonicalPath η) ∧
        Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
        loop 0 = basepoint ∧ loop 1 = basepoint ∧
        Path.Homotopic loop (Path.refl basepoint) ∧
        FundamentalGroup.fromPath
            (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
          FundamentalGroup.fromPath
            (⟦Path.refl basepoint⟧ :
              Path.Homotopic.Quotient basepoint basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  rcases
      twoPointComplement_exists_path_with_endpoints_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint target with
    ⟨canonicalPath, canonicalSource, canonicalTarget, canonicalJoined⟩
  have chosenHomotopic :
      Path.Homotopic chosenPath canonicalPath :=
    twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
      h hyx chosenPath canonicalPath
  have chosenQuotientEq :
      (⟦chosenPath⟧ : Path.Homotopic.Quotient basepoint target) =
        ⟦canonicalPath⟧ :=
    Quotient.sound chosenHomotopic
  have loopHomotopic :
      Path.Homotopic loop (Path.refl basepoint) :=
    twoPointComplement_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint loop
  exact
    ⟨canonicalPath,
      twoPointComplement_nonempty_of_homeomorph_to_onePoint_threeSpace h hyx,
      twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint,
      canonicalSource, canonicalTarget, canonicalJoined,
      chosenHomotopic, chosenQuotientEq,
      fun η =>
        twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
          h hyx canonicalPath η,
      twoPointComplement_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint target,
      Path.source loop, Path.target loop, loopHomotopic,
      congrArg FundamentalGroup.fromPath (Quotient.sound loopHomotopic),
      twoPointComplement_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint⟩

/--
Theorem contract for
`twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace`.
-/
theorem twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace_eq :
    @Poincare.twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace =
      @Poincare.twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace :=
  rfl

/--
The one-point compactification recognition route supplies the transported
two-puncture Euclidean chart and the path/loop projection payload with one
shared canonical chosen path. This keeps the chart, endpoint-data, homotopy,
quotient, loop, and `π₁` collapse evidence synchronized for downstream
topology extraction consumers.
-/
theorem twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (basepoint target : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({x} ∪ {y})ᶜ : Set M) basepoint target,
            ∃ canonicalPath : Path basepoint target,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                pathData.path_to target = canonicalPath ∧
                endpointData.path = canonicalPath ∧
                canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
                Joined basepoint target ∧
                pathComponent basepoint = Set.univ ∧
                Path.Homotopic chosenPath canonicalPath ∧
                (⟦chosenPath⟧ :
                  Path.Homotopic.Quotient basepoint target) =
                  ⟦canonicalPath⟧ ∧
                (∀ η : Path basepoint target,
                  Path.Homotopic canonicalPath η) ∧
                Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
                loop 0 = basepoint ∧ loop 1 = basepoint ∧
                Path.Homotopic loop (Path.refl basepoint) ∧
                FundamentalGroup.fromPath
                    (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
                  FundamentalGroup.fromPath
                    (⟦Path.refl basepoint⟧ :
                      Path.Homotopic.Quotient basepoint basepoint) ∧
                Subsingleton
                  (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  rcases
      exists_puncture_homeomorph_twoPointComplement_chosenPathTopologyPayload
        h hyx basepoint target with
    ⟨puncture, chart, pathData, endpointData, canonicalPath,
      hAvoidsPuncture, hNonempty, hPathConnected, hSimplyConnected,
      hPathData, hEndpointPath, hSource, hTarget, hJoined⟩
  have hComponent :
      pathComponent basepoint = Set.univ :=
    twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint
  have chosenHomotopic :
      Path.Homotopic chosenPath canonicalPath :=
    twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
      h hyx chosenPath canonicalPath
  have chosenQuotientEq :
      (⟦chosenPath⟧ : Path.Homotopic.Quotient basepoint target) =
        ⟦canonicalPath⟧ :=
    Quotient.sound chosenHomotopic
  have loopHomotopic :
      Path.Homotopic loop (Path.refl basepoint) :=
    twoPointComplement_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
      h hyx basepoint loop
  exact
    ⟨puncture, chart, pathData, endpointData, canonicalPath,
      hAvoidsPuncture, hNonempty, hPathConnected, hSimplyConnected,
      hPathData, hEndpointPath, hSource, hTarget, hJoined, hComponent,
      chosenHomotopic, chosenQuotientEq,
      fun η =>
        twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
          h hyx canonicalPath η,
      twoPointComplement_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint target,
      Path.source loop, Path.target loop, loopHomotopic,
      congrArg FundamentalGroup.fromPath (Quotient.sound loopHomotopic),
      twoPointComplement_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
        h hyx basepoint⟩

/--
Theorem contract for
`twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace`.
-/
theorem twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace_eq :
    @Poincare.twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace =
      @Poincare.twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace :=
  rfl

/--
Recognition as a one-point compactification exposes the singleton-complement
path/loop collapse and the synchronized two-puncture chart/path-loop projection
payload together. This is the transport-layer form of the puncture data that
final topology packages consume one level higher.
-/
theorem singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    {a b : ({x}ᶜ : Set M)} (γ η : Path a b)
    (singleBase : ({x}ᶜ : Set M))
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path twoBase twoTarget)
    (loop : Path twoBase twoBase) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ ∧
      singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
      Path.Homotopic singleLoop (Path.refl singleBase) ∧
      FundamentalGroup.fromPath
          (⟦singleLoop⟧ : Path.Homotopic.Quotient singleBase singleBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl singleBase⟧ :
            Path.Homotopic.Quotient singleBase singleBase) ∧
      Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBase) ∧
      ∃ puncture : EuclideanSpace ℝ (Fin 3),
        ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
          ∃ pathData :
              PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) twoBase,
            ∃ endpointData :
                PointedChosenPathEndpointData
                  (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
              ∃ canonicalPath : Path twoBase twoTarget,
                (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                  Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                  PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  pathData.path_to twoTarget = canonicalPath ∧
                  endpointData.path = canonicalPath ∧
                  canonicalPath 0 = twoBase ∧ canonicalPath 1 = twoTarget ∧
                  Joined twoBase twoTarget ∧
                  pathComponent twoBase = Set.univ ∧
                  Path.Homotopic chosenPath canonicalPath ∧
                  (⟦chosenPath⟧ :
                    Path.Homotopic.Quotient twoBase twoTarget) =
                    ⟦canonicalPath⟧ ∧
                  (∀ ζ : Path twoBase twoTarget,
                    Path.Homotopic canonicalPath ζ) ∧
                  Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
                  loop 0 = twoBase ∧ loop 1 = twoBase ∧
                  Path.Homotopic loop (Path.refl twoBase) ∧
                  FundamentalGroup.fromPath
                      (⟦loop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
                    FundamentalGroup.fromPath
                      (⟦Path.refl twoBase⟧ :
                        Path.Homotopic.Quotient twoBase twoBase) ∧
                  Subsingleton
                    (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBase) := by
  have singleHomotopy :
      Path.Homotopic γ η :=
    compl_singleton_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
      h x γ η
  have singleQuotient :
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ :=
    Quotient.sound singleHomotopy
  have singleLoopHomotopy :
      Path.Homotopic singleLoop (Path.refl singleBase) :=
    compl_singleton_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
      h x singleBase singleLoop
  have singleFromPath :
      FundamentalGroup.fromPath
          (⟦singleLoop⟧ : Path.Homotopic.Quotient singleBase singleBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl singleBase⟧ :
            Path.Homotopic.Quotient singleBase singleBase) :=
    congrArg FundamentalGroup.fromPath (Quotient.sound singleLoopHomotopy)
  exact
    ⟨singleHomotopy, singleQuotient, Path.source singleLoop,
      Path.target singleLoop, singleLoopHomotopy, singleFromPath,
      compl_singleton_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
        h x singleBase,
      twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace
        h hyx twoBase twoTarget chosenPath loop⟩

/--
Theorem contract for
`singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace`.
-/
theorem singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace_eq :
    @Poincare.singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace =
      @Poincare.singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace :=
  rfl

/--
Recognition as a one-point compactification also exposes explicit singleton
chosen-path endpoint data together with singleton path/loop collapse and the
synchronized two-puncture chart/path-loop projection payload.
-/
theorem singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (singleBase singleTarget : ({x}ᶜ : Set M))
    (chosenSinglePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path twoBase twoTarget)
    (loop : Path twoBase twoBase) :
    ∃ singlePathData :
        PointedPathComponentPathData ({x}ᶜ : Set M) singleBase,
      ∃ singleEndpointData :
          PointedChosenPathEndpointData ({x}ᶜ : Set M)
            singleBase singleTarget,
        ∃ canonicalSinglePath : Path singleBase singleTarget,
          singlePathData.path_to singleTarget = canonicalSinglePath ∧
            singleEndpointData.path = canonicalSinglePath ∧
            canonicalSinglePath 0 = singleBase ∧
            canonicalSinglePath 1 = singleTarget ∧
            Joined singleBase singleTarget ∧
            pathComponent singleBase = Set.univ ∧
            Path.Homotopic chosenSinglePath canonicalSinglePath ∧
            (⟦chosenSinglePath⟧ :
              Path.Homotopic.Quotient singleBase singleTarget) =
              ⟦canonicalSinglePath⟧ ∧
            (∀ ζ : Path singleBase singleTarget,
              Path.Homotopic canonicalSinglePath ζ) ∧
            Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
            singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
            Path.Homotopic singleLoop (Path.refl singleBase) ∧
            FundamentalGroup.fromPath
                (⟦singleLoop⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) =
              FundamentalGroup.fromPath
                (⟦Path.refl singleBase⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBase) ∧
            ∃ puncture : EuclideanSpace ℝ (Fin 3),
              ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
                ∃ twoPathData :
                    PointedPathComponentPathData
                      (({x} ∪ {y})ᶜ : Set M) twoBase,
                  ∃ twoEndpointData :
                      PointedChosenPathEndpointData
                        (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
                    ∃ canonicalPath : Path twoBase twoTarget,
                      (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                        twoPathData.path_to twoTarget = canonicalPath ∧
                        twoEndpointData.path = canonicalPath ∧
                        canonicalPath 0 = twoBase ∧
                        canonicalPath 1 = twoTarget ∧
                        Joined twoBase twoTarget ∧
                        pathComponent twoBase = Set.univ ∧
                        Path.Homotopic chosenPath canonicalPath ∧
                        (⟦chosenPath⟧ :
                          Path.Homotopic.Quotient twoBase twoTarget) =
                          ⟦canonicalPath⟧ ∧
                        (∀ ζ : Path twoBase twoTarget,
                          Path.Homotopic canonicalPath ζ) ∧
                        Subsingleton
                          (Path.Homotopic.Quotient twoBase twoTarget) ∧
                        loop 0 = twoBase ∧ loop 1 = twoBase ∧
                        Path.Homotopic loop (Path.refl twoBase) ∧
                        FundamentalGroup.fromPath
                            (⟦loop⟧ :
                              Path.Homotopic.Quotient twoBase twoBase) =
                          FundamentalGroup.fromPath
                            (⟦Path.refl twoBase⟧ :
                              Path.Homotopic.Quotient twoBase twoBase) ∧
                        Subsingleton
                          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M)
                            twoBase) := by
  let singlePathData :
      PointedPathComponentPathData ({x}ᶜ : Set M) singleBase :=
    compl_singleton_pointedPathComponentPathData_of_homeomorph_to_onePoint_threeSpace
      h x singleBase
  let singleEndpointData :
      PointedChosenPathEndpointData ({x}ᶜ : Set M) singleBase singleTarget :=
    compl_singleton_chosenPathEndpointData_of_homeomorph_to_onePoint_threeSpace
      h x singleBase singleTarget
  let canonicalSinglePath : Path singleBase singleTarget :=
    singleEndpointData.path
  have hSinglePathData :
      singlePathData.path_to singleTarget = canonicalSinglePath := by
    rfl
  have hSingleEndpoint :
      singleEndpointData.path = canonicalSinglePath := by
    rfl
  have hSingleSource : canonicalSinglePath 0 = singleBase := by
    change singleEndpointData.path 0 = singleBase
    exact singleEndpointData.source_eq
  have hSingleTarget : canonicalSinglePath 1 = singleTarget := by
    change singleEndpointData.path 1 = singleTarget
    exact singleEndpointData.target_eq
  have hSingleComponent : pathComponent singleBase = Set.univ :=
    compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
      h x singleBase
  have hChosenSingle :
      Path.Homotopic chosenSinglePath canonicalSinglePath :=
    compl_singleton_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
      h x chosenSinglePath canonicalSinglePath
  have hChosenSingleQuotient :
      (⟦chosenSinglePath⟧ :
        Path.Homotopic.Quotient singleBase singleTarget) =
        ⟦canonicalSinglePath⟧ :=
    Quotient.sound hChosenSingle
  have hSingleLoop :
      Path.Homotopic singleLoop (Path.refl singleBase) :=
    compl_singleton_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
      h x singleBase singleLoop
  have hSingleLoopFromPath :
      FundamentalGroup.fromPath
          (⟦singleLoop⟧ :
            Path.Homotopic.Quotient singleBase singleBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl singleBase⟧ :
            Path.Homotopic.Quotient singleBase singleBase) :=
    congrArg FundamentalGroup.fromPath (Quotient.sound hSingleLoop)
  exact
    ⟨singlePathData, singleEndpointData, canonicalSinglePath,
      hSinglePathData, hSingleEndpoint, hSingleSource, hSingleTarget,
      singleEndpointData.joined, hSingleComponent, hChosenSingle,
      hChosenSingleQuotient,
      fun ζ =>
        compl_singleton_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
          h x canonicalSinglePath ζ,
      compl_singleton_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
        h x singleBase singleTarget,
      Path.source singleLoop, Path.target singleLoop, hSingleLoop,
      hSingleLoopFromPath,
      compl_singleton_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
        h x singleBase,
      twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace
        h hyx twoBase twoTarget chosenPath loop⟩

/--
Theorem contract for
`singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace`.
-/
theorem singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace_eq :
    @Poincare.singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace =
      @Poincare.singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace :=
  rfl

/--
Recognition as a one-point compactification gives the actual Euclidean chart
on a singleton complement together with explicit singleton chosen-path data,
singleton path/loop collapse, and the synchronized two-puncture chart/path-loop
projection payload.
-/
theorem singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    {x y : M} (hyx : y ≠ x)
    (singleBase singleTarget : ({x}ᶜ : Set M))
    (chosenSinglePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path twoBase twoTarget)
    (loop : Path twoBase twoBase) :
    Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
      ∃ singlePathData :
          PointedPathComponentPathData ({x}ᶜ : Set M) singleBase,
        ∃ singleEndpointData :
            PointedChosenPathEndpointData ({x}ᶜ : Set M)
              singleBase singleTarget,
          ∃ canonicalSinglePath : Path singleBase singleTarget,
            singlePathData.path_to singleTarget = canonicalSinglePath ∧
              singleEndpointData.path = canonicalSinglePath ∧
              canonicalSinglePath 0 = singleBase ∧
              canonicalSinglePath 1 = singleTarget ∧
              Joined singleBase singleTarget ∧
              pathComponent singleBase = Set.univ ∧
              Path.Homotopic chosenSinglePath canonicalSinglePath ∧
              (⟦chosenSinglePath⟧ :
                Path.Homotopic.Quotient singleBase singleTarget) =
                ⟦canonicalSinglePath⟧ ∧
              (∀ ζ : Path singleBase singleTarget,
                Path.Homotopic canonicalSinglePath ζ) ∧
              Subsingleton
                (Path.Homotopic.Quotient singleBase singleTarget) ∧
              singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
              Path.Homotopic singleLoop (Path.refl singleBase) ∧
              FundamentalGroup.fromPath
                  (⟦singleLoop⟧ :
                    Path.Homotopic.Quotient singleBase singleBase) =
                FundamentalGroup.fromPath
                  (⟦Path.refl singleBase⟧ :
                    Path.Homotopic.Quotient singleBase singleBase) ∧
              Subsingleton
                (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBase) ∧
              ∃ puncture : EuclideanSpace ℝ (Fin 3),
                ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
                    ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
                  ∃ twoPathData :
                      PointedPathComponentPathData
                        (({x} ∪ {y})ᶜ : Set M) twoBase,
                    ∃ twoEndpointData :
                        PointedChosenPathEndpointData
                          (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
                      ∃ canonicalPath : Path twoBase twoTarget,
                        (∀ w,
                          (chart w : EuclideanSpace ℝ (Fin 3)) ≠
                            puncture) ∧
                          Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                          PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                          twoPathData.path_to twoTarget = canonicalPath ∧
                          twoEndpointData.path = canonicalPath ∧
                          canonicalPath 0 = twoBase ∧
                          canonicalPath 1 = twoTarget ∧
                          Joined twoBase twoTarget ∧
                          pathComponent twoBase = Set.univ ∧
                          Path.Homotopic chosenPath canonicalPath ∧
                          (⟦chosenPath⟧ :
                            Path.Homotopic.Quotient twoBase twoTarget) =
                            ⟦canonicalPath⟧ ∧
                          (∀ ζ : Path twoBase twoTarget,
                            Path.Homotopic canonicalPath ζ) ∧
                          Subsingleton
                            (Path.Homotopic.Quotient twoBase twoTarget) ∧
                          loop 0 = twoBase ∧ loop 1 = twoBase ∧
                          Path.Homotopic loop (Path.refl twoBase) ∧
                          FundamentalGroup.fromPath
                              (⟦loop⟧ :
                                Path.Homotopic.Quotient twoBase twoBase) =
                            FundamentalGroup.fromPath
                              (⟦Path.refl twoBase⟧ :
                                Path.Homotopic.Quotient twoBase twoBase) ∧
                          Subsingleton
                            (HomotopyGroup.Pi 1
                              (({x} ∪ {y})ᶜ : Set M) twoBase) := by
  exact
    ⟨⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
        h x⟩,
      singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace
        h hyx singleBase singleTarget chosenSinglePath singleLoop
        twoBase twoTarget chosenPath loop⟩

/--
Theorem contract for
`singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace`.
-/
theorem singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace_eq :
    @Poincare.singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace =
      @Poincare.singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace :=
  rfl

/--
The same single-puncture Euclidean chart transport, stated from recognition as
the project `ThreeSphere`.
-/
noncomputable def homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
Every single-puncture complement of a space recognized as `ThreeSphere` is
contractible.
-/
theorem compl_singleton_contractibleSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) :=
  (homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
    h x).contractibleSpace

/--
Every based loop in a single-puncture complement of a recognized `ThreeSphere`
is null-homotopic.
-/
theorem compl_singleton_loop_nullhomotopic_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ∀ (basepoint : ({x}ᶜ : Set M)) (γ : Path basepoint basepoint),
      Path.Homotopic γ (Path.refl basepoint) :=
  compl_singleton_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
Any two paths with the same endpoints in a single-puncture complement of a
recognized `ThreeSphere` are homotopic.
-/
theorem compl_singleton_paths_homotopic_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ∀ {a b : ({x}ᶜ : Set M)} (γ₀ γ₁ : Path a b),
      Path.Homotopic γ₀ γ₁ :=
  compl_singleton_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
Any two points in a single-puncture complement of a recognized `ThreeSphere`
are joined by an actual path.
-/
theorem compl_singleton_path_nonempty_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Nonempty (Path a b) :=
  compl_singleton_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
Recognizing a space as `ThreeSphere` joins any two points in a single-puncture
complement in mathlib's `Joined` relation.
-/
theorem compl_singleton_joined_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Joined a b :=
  compl_singleton_joined_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
Recognizing a space as `ThreeSphere` collapses each single-puncture
complement to one path component.
-/
theorem compl_singleton_pathComponent_eq_univ_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    pathComponent basepoint = Set.univ :=
  compl_singleton_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x
    basepoint

/--
Recognizing a space as `ThreeSphere` gives an explicit path between a basepoint
and target in any single-puncture complement, together with both endpoint
equations.
-/
theorem compl_singleton_exists_path_with_endpoints_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z :=
  compl_singleton_exists_path_with_endpoints_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x
    basepoint z

/--
Every path-homotopy quotient in a single-puncture complement of a recognized
`ThreeSphere` is a subsingleton.
-/
theorem compl_singleton_pathQuotient_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)),
      Subsingleton (Path.Homotopic.Quotient a b) :=
  compl_singleton_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x

/--
The based fundamental group of every single-puncture complement of a recognized
`ThreeSphere` is trivial.
-/
theorem compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) :=
  compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) x
    basepoint

/--
The same single-puncture triviality for a recognized `ThreeSphere`, stated for
mathlib's first homotopy group.
-/
theorem compl_singleton_piOne_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := ({x}ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
    (compl_singleton_fundamentalGroup_subsingleton_of_homeomorph_to_threeSphere
      h x basepoint)

/--
Every two-puncture complement of a space recognized as `ThreeSphere` is simply
connected.
-/
theorem twoPointComplement_simplyConnectedSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Every two-puncture complement of a space recognized as `ThreeSphere` is
path-connected.
-/
theorem twoPointComplement_pathConnectedSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Every two-puncture complement of a space recognized as `ThreeSphere` is
connected.
-/
theorem twoPointComplement_connectedSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_connectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Every two-puncture complement of a space recognized as `ThreeSphere` is
nonempty.
-/
theorem twoPointComplement_nonempty_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    Nonempty (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_nonempty_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
The topology package for every two-puncture complement of a space recognized as
`ThreeSphere`: nonemptiness, path-connectedness, connectedness, and simple
connectedness.
-/
theorem twoPointComplement_topology_package_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
      PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  ⟨twoPointComplement_nonempty_of_homeomorph_to_threeSphere h hyx,
    twoPointComplement_pathConnectedSpace_of_homeomorph_to_threeSphere h hyx,
    twoPointComplement_connectedSpace_of_homeomorph_to_threeSphere h hyx,
    twoPointComplement_simplyConnectedSpace_of_homeomorph_to_threeSphere h hyx⟩

/-- Theorem contract for `twoPointComplement_topology_package_of_homeomorph_to_threeSphere`. -/
theorem twoPointComplement_topology_package_of_homeomorph_to_threeSphere_eq :
    @Poincare.twoPointComplement_topology_package_of_homeomorph_to_threeSphere =
      @Poincare.twoPointComplement_topology_package_of_homeomorph_to_threeSphere :=
  rfl

/--
The transported two-puncture Euclidean chart topology payload, stated directly
from recognition as `ThreeSphere`.
-/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ z, (chart z : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
          Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
          PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Theorem contract for
`exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload_of_homeomorph_to_threeSphere`.
-/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload_of_homeomorph_to_threeSphere_eq :
    @Poincare.exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload_of_homeomorph_to_threeSphere =
      @Poincare.exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload_of_homeomorph_to_threeSphere :=
  rfl

/--
The transported two-puncture Euclidean chart with full topology payload, stated
directly from recognition as `ThreeSphere`.
-/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ z, (chart z : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
          Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
          PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Theorem contract for
`exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload_of_homeomorph_to_threeSphere`.
-/
theorem exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload_of_homeomorph_to_threeSphere_eq :
    @Poincare.exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload_of_homeomorph_to_threeSphere =
      @Poincare.exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_fullTopologyPayload_of_homeomorph_to_threeSphere :=
  rfl

/--
The based fundamental group of every two-puncture complement of a space
recognized as `ThreeSphere` is trivial.
-/
theorem twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint

/--
Every based loop in a two-puncture complement of a recognized `ThreeSphere` is
null-homotopic.
-/
theorem twoPointComplement_loop_nullhomotopic_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∀ (basepoint : (({x} ∪ {y})ᶜ : Set M))
      (γ : Path basepoint basepoint), Path.Homotopic γ (Path.refl basepoint) :=
  twoPointComplement_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Any two paths with the same endpoints in a two-puncture complement of a
recognized `ThreeSphere` are homotopic.
-/
theorem twoPointComplement_paths_homotopic_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∀ {a b : (({x} ∪ {y})ᶜ : Set M)} (γ η : Path a b),
      Path.Homotopic γ η :=
  twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Any two points in a two-puncture complement of a recognized `ThreeSphere` are
joined by an actual path.
-/
theorem twoPointComplement_path_nonempty_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Nonempty (Path a b) :=
  twoPointComplement_path_nonempty_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Recognizing a space as `ThreeSphere` joins any two points in a two-puncture
complement in mathlib's `Joined` relation.
-/
theorem twoPointComplement_joined_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Joined a b :=
  twoPointComplement_joined_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
Recognizing a space as `ThreeSphere` collapses each two-puncture complement
to one path component.
-/
theorem twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    pathComponent basepoint = Set.univ :=
  twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint

/--
Recognizing a space as `ThreeSphere` gives an explicit path between a basepoint
and target in any two-puncture complement, together with both endpoint
equations.
-/
theorem twoPointComplement_exists_path_with_endpoints_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z :=
  twoPointComplement_exists_path_with_endpoints_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint z

/--
Every path-homotopy quotient in a two-puncture complement of a recognized
`ThreeSphere` is a subsingleton.
-/
theorem twoPointComplement_pathQuotient_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)),
      Subsingleton (Path.Homotopic.Quotient a b) :=
  twoPointComplement_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx

/--
The same two-puncture triviality for a recognized `ThreeSphere`, stated for
mathlib's first homotopy group.
-/
theorem twoPointComplement_piOne_subsingleton_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := (({x} ∪ {y})ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
    (twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_threeSphere
      h hyx basepoint)

/--
For a space already recognized as `ThreeSphere`, every two-puncture complement
has the concrete path/loop payload used downstream: nonemptiness, component
collapse, a chosen path with endpoint equations, homotopy uniqueness against
any supplied path, quotient collapse, loop nullhomotopy, and trivial first
homotopy group.
-/
theorem twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint target : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ canonicalPath : Path basepoint target,
      Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        pathComponent basepoint = Set.univ ∧
        canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
        Joined basepoint target ∧
        Path.Homotopic chosenPath canonicalPath ∧
        (⟦chosenPath⟧ :
          Path.Homotopic.Quotient basepoint target) =
          ⟦canonicalPath⟧ ∧
        (∀ η : Path basepoint target,
          Path.Homotopic canonicalPath η) ∧
        Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
        loop 0 = basepoint ∧ loop 1 = basepoint ∧
        Path.Homotopic loop (Path.refl basepoint) ∧
        FundamentalGroup.fromPath
            (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
          FundamentalGroup.fromPath
            (⟦Path.refl basepoint⟧ :
              Path.Homotopic.Quotient basepoint basepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  rcases
      twoPointComplement_exists_path_with_endpoints_of_homeomorph_to_threeSphere
        h hyx basepoint target with
    ⟨canonicalPath, canonicalSource, canonicalTarget, canonicalJoined⟩
  have chosenHomotopic :
      Path.Homotopic chosenPath canonicalPath :=
    twoPointComplement_paths_homotopic_of_homeomorph_to_threeSphere
      h hyx chosenPath canonicalPath
  have chosenQuotientEq :
      (⟦chosenPath⟧ : Path.Homotopic.Quotient basepoint target) =
        ⟦canonicalPath⟧ :=
    Quotient.sound chosenHomotopic
  have loopHomotopic :
      Path.Homotopic loop (Path.refl basepoint) :=
    twoPointComplement_loop_nullhomotopic_of_homeomorph_to_threeSphere
      h hyx basepoint loop
  exact
    ⟨canonicalPath,
      twoPointComplement_nonempty_of_homeomorph_to_threeSphere h hyx,
      twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_threeSphere
        h hyx basepoint,
      canonicalSource, canonicalTarget, canonicalJoined,
      chosenHomotopic, chosenQuotientEq,
      fun η =>
        twoPointComplement_paths_homotopic_of_homeomorph_to_threeSphere
          h hyx canonicalPath η,
      twoPointComplement_pathQuotient_subsingleton_of_homeomorph_to_threeSphere
        h hyx basepoint target,
      Path.source loop, Path.target loop, loopHomotopic,
      congrArg FundamentalGroup.fromPath (Quotient.sound loopHomotopic),
      twoPointComplement_piOne_subsingleton_of_homeomorph_to_threeSphere
        h hyx basepoint⟩

/--
Theorem contract for
`twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_threeSphere`.
-/
theorem twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_threeSphere_eq :
    @Poincare.twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_threeSphere =
      @Poincare.twoPointComplement_chosen_path_loop_projection_bundle_of_homeomorph_to_threeSphere :=
  rfl

/--
For a space recognized as `ThreeSphere`, the transported two-puncture Euclidean
chart and the path/loop projection payload are available with one shared
canonical chosen path. This is the `ThreeSphere` recognition form of the
synchronized chart, endpoint-data, homotopy, quotient, loop, and `π₁` collapse
certificate.
-/
theorem twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (basepoint target : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({x} ∪ {y})ᶜ : Set M) basepoint target,
            ∃ canonicalPath : Path basepoint target,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                pathData.path_to target = canonicalPath ∧
                endpointData.path = canonicalPath ∧
                canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
                Joined basepoint target ∧
                pathComponent basepoint = Set.univ ∧
                Path.Homotopic chosenPath canonicalPath ∧
                (⟦chosenPath⟧ :
                  Path.Homotopic.Quotient basepoint target) =
                  ⟦canonicalPath⟧ ∧
                (∀ η : Path basepoint target,
                  Path.Homotopic canonicalPath η) ∧
                Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
                loop 0 = basepoint ∧ loop 1 = basepoint ∧
                Path.Homotopic loop (Path.refl basepoint) ∧
                FundamentalGroup.fromPath
                    (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
                  FundamentalGroup.fromPath
                    (⟦Path.refl basepoint⟧ :
                      Path.Homotopic.Quotient basepoint basepoint) ∧
                Subsingleton
                  (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    basepoint target chosenPath loop

/--
Theorem contract for
`twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_threeSphere`.
-/
theorem twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_threeSphere_eq :
    @Poincare.twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_threeSphere =
      @Poincare.twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_threeSphere :=
  rfl

/--
Recognition as `ThreeSphere` exposes singleton-complement path/loop collapse
and the synchronized two-puncture chart/path-loop projection payload together.
This is the direct `ThreeSphere` form of the combined puncture transport
certificate.
-/
theorem singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    {a b : ({x}ᶜ : Set M)} (γ η : Path a b)
    (singleBase : ({x}ᶜ : Set M))
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path twoBase twoTarget)
    (loop : Path twoBase twoBase) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ ∧
      singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
      Path.Homotopic singleLoop (Path.refl singleBase) ∧
      FundamentalGroup.fromPath
          (⟦singleLoop⟧ : Path.Homotopic.Quotient singleBase singleBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl singleBase⟧ :
            Path.Homotopic.Quotient singleBase singleBase) ∧
      Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBase) ∧
      ∃ puncture : EuclideanSpace ℝ (Fin 3),
        ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
          ∃ pathData :
              PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) twoBase,
            ∃ endpointData :
                PointedChosenPathEndpointData
                  (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
              ∃ canonicalPath : Path twoBase twoTarget,
                (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                  Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                  PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  pathData.path_to twoTarget = canonicalPath ∧
                  endpointData.path = canonicalPath ∧
                  canonicalPath 0 = twoBase ∧ canonicalPath 1 = twoTarget ∧
                  Joined twoBase twoTarget ∧
                  pathComponent twoBase = Set.univ ∧
                  Path.Homotopic chosenPath canonicalPath ∧
                  (⟦chosenPath⟧ :
                    Path.Homotopic.Quotient twoBase twoTarget) =
                    ⟦canonicalPath⟧ ∧
                  (∀ ζ : Path twoBase twoTarget,
                    Path.Homotopic canonicalPath ζ) ∧
                  Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
                  loop 0 = twoBase ∧ loop 1 = twoBase ∧
                  Path.Homotopic loop (Path.refl twoBase) ∧
                  FundamentalGroup.fromPath
                      (⟦loop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
                    FundamentalGroup.fromPath
                      (⟦Path.refl twoBase⟧ :
                        Path.Homotopic.Quotient twoBase twoBase) ∧
                  Subsingleton
                    (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBase) :=
  singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    γ η singleBase singleLoop twoBase twoTarget chosenPath loop

/--
Theorem contract for
`singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere`.
-/
theorem singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere_eq :
    @Poincare.singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere =
      @Poincare.singletonPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere :=
  rfl

/--
Recognition as `ThreeSphere` also exposes explicit singleton chosen-path
endpoint data together with singleton path/loop collapse and the synchronized
two-puncture chart/path-loop projection payload.
-/
theorem singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (singleBase singleTarget : ({x}ᶜ : Set M))
    (chosenSinglePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path twoBase twoTarget)
    (loop : Path twoBase twoBase) :
    ∃ singlePathData :
        PointedPathComponentPathData ({x}ᶜ : Set M) singleBase,
      ∃ singleEndpointData :
          PointedChosenPathEndpointData ({x}ᶜ : Set M)
            singleBase singleTarget,
        ∃ canonicalSinglePath : Path singleBase singleTarget,
          singlePathData.path_to singleTarget = canonicalSinglePath ∧
            singleEndpointData.path = canonicalSinglePath ∧
            canonicalSinglePath 0 = singleBase ∧
            canonicalSinglePath 1 = singleTarget ∧
            Joined singleBase singleTarget ∧
            pathComponent singleBase = Set.univ ∧
            Path.Homotopic chosenSinglePath canonicalSinglePath ∧
            (⟦chosenSinglePath⟧ :
              Path.Homotopic.Quotient singleBase singleTarget) =
              ⟦canonicalSinglePath⟧ ∧
            (∀ ζ : Path singleBase singleTarget,
              Path.Homotopic canonicalSinglePath ζ) ∧
            Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
            singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
            Path.Homotopic singleLoop (Path.refl singleBase) ∧
            FundamentalGroup.fromPath
                (⟦singleLoop⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) =
              FundamentalGroup.fromPath
                (⟦Path.refl singleBase⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBase) ∧
            ∃ puncture : EuclideanSpace ℝ (Fin 3),
              ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
                ∃ twoPathData :
                    PointedPathComponentPathData
                      (({x} ∪ {y})ᶜ : Set M) twoBase,
                  ∃ twoEndpointData :
                      PointedChosenPathEndpointData
                        (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
                    ∃ canonicalPath : Path twoBase twoTarget,
                      (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                        PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                        twoPathData.path_to twoTarget = canonicalPath ∧
                        twoEndpointData.path = canonicalPath ∧
                        canonicalPath 0 = twoBase ∧
                        canonicalPath 1 = twoTarget ∧
                        Joined twoBase twoTarget ∧
                        pathComponent twoBase = Set.univ ∧
                        Path.Homotopic chosenPath canonicalPath ∧
                        (⟦chosenPath⟧ :
                          Path.Homotopic.Quotient twoBase twoTarget) =
                          ⟦canonicalPath⟧ ∧
                        (∀ ζ : Path twoBase twoTarget,
                          Path.Homotopic canonicalPath ζ) ∧
                        Subsingleton
                          (Path.Homotopic.Quotient twoBase twoTarget) ∧
                        loop 0 = twoBase ∧ loop 1 = twoBase ∧
                        Path.Homotopic loop (Path.refl twoBase) ∧
                        FundamentalGroup.fromPath
                            (⟦loop⟧ :
                              Path.Homotopic.Quotient twoBase twoBase) =
                          FundamentalGroup.fromPath
                            (⟦Path.refl twoBase⟧ :
                              Path.Homotopic.Quotient twoBase twoBase) ∧
                        Subsingleton
                          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M)
                            twoBase) :=
  singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    singleBase singleTarget chosenSinglePath singleLoop twoBase twoTarget
    chosenPath loop

/--
Recognition as `ThreeSphere` gives the actual Euclidean chart on a singleton
complement together with explicit singleton chosen-path data, singleton
path/loop collapse, and the synchronized two-puncture chart/path-loop
projection payload.
-/
theorem singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) {x y : M} (hyx : y ≠ x)
    (singleBase singleTarget : ({x}ᶜ : Set M))
    (chosenSinglePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path twoBase twoTarget)
    (loop : Path twoBase twoBase) :
    Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
      ∃ singlePathData :
          PointedPathComponentPathData ({x}ᶜ : Set M) singleBase,
        ∃ singleEndpointData :
            PointedChosenPathEndpointData ({x}ᶜ : Set M)
              singleBase singleTarget,
          ∃ canonicalSinglePath : Path singleBase singleTarget,
            singlePathData.path_to singleTarget = canonicalSinglePath ∧
              singleEndpointData.path = canonicalSinglePath ∧
              canonicalSinglePath 0 = singleBase ∧
              canonicalSinglePath 1 = singleTarget ∧
              Joined singleBase singleTarget ∧
              pathComponent singleBase = Set.univ ∧
              Path.Homotopic chosenSinglePath canonicalSinglePath ∧
              (⟦chosenSinglePath⟧ :
                Path.Homotopic.Quotient singleBase singleTarget) =
                ⟦canonicalSinglePath⟧ ∧
              (∀ ζ : Path singleBase singleTarget,
                Path.Homotopic canonicalSinglePath ζ) ∧
              Subsingleton
                (Path.Homotopic.Quotient singleBase singleTarget) ∧
              singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
              Path.Homotopic singleLoop (Path.refl singleBase) ∧
              FundamentalGroup.fromPath
                  (⟦singleLoop⟧ :
                    Path.Homotopic.Quotient singleBase singleBase) =
                FundamentalGroup.fromPath
                  (⟦Path.refl singleBase⟧ :
                    Path.Homotopic.Quotient singleBase singleBase) ∧
              Subsingleton
                (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBase) ∧
              ∃ puncture : EuclideanSpace ℝ (Fin 3),
                ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
                    ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
                  ∃ twoPathData :
                      PointedPathComponentPathData
                        (({x} ∪ {y})ᶜ : Set M) twoBase,
                    ∃ twoEndpointData :
                        PointedChosenPathEndpointData
                          (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
                      ∃ canonicalPath : Path twoBase twoTarget,
                        (∀ w,
                          (chart w : EuclideanSpace ℝ (Fin 3)) ≠
                            puncture) ∧
                          Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                          PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                          twoPathData.path_to twoTarget = canonicalPath ∧
                          twoEndpointData.path = canonicalPath ∧
                          canonicalPath 0 = twoBase ∧
                          canonicalPath 1 = twoTarget ∧
                          Joined twoBase twoTarget ∧
                          pathComponent twoBase = Set.univ ∧
                          Path.Homotopic chosenPath canonicalPath ∧
                          (⟦chosenPath⟧ :
                            Path.Homotopic.Quotient twoBase twoTarget) =
                            ⟦canonicalPath⟧ ∧
                          (∀ ζ : Path twoBase twoTarget,
                            Path.Homotopic canonicalPath ζ) ∧
                          Subsingleton
                            (Path.Homotopic.Quotient twoBase twoTarget) ∧
                          loop 0 = twoBase ∧ loop 1 = twoBase ∧
                          Path.Homotopic loop (Path.refl twoBase) ∧
                          FundamentalGroup.fromPath
                              (⟦loop⟧ :
                                Path.Homotopic.Quotient twoBase twoBase) =
                            FundamentalGroup.fromPath
                              (⟦Path.refl twoBase⟧ :
                                Path.Homotopic.Quotient twoBase twoBase) ∧
                          Subsingleton
                            (HomotopyGroup.Pi 1
                              (({x} ∪ {y})ᶜ : Set M) twoBase) :=
  singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h) hyx
    singleBase singleTarget chosenSinglePath singleLoop twoBase twoTarget
    chosenPath loop

/--
Theorem contract for
`singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere`.
-/
theorem singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere_eq :
    @Poincare.singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere =
      @Poincare.singletonEuclideanChart_chosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere :=
  rfl

/--
Theorem contract for
`singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere`.
-/
theorem singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere_eq :
    @Poincare.singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere =
      @Poincare.singletonChosenPathLoop_and_twoPointChartPathLoopProjection_of_homeomorph_to_threeSphere :=
  rfl

end Poincare
