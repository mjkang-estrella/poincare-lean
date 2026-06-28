import Poincare.ProofProgress.TopologyExtractionPunctureTransport
import Poincare.ProofProgress.TopologyDecompositionInterface

namespace Poincare

universe u

/--
A fixed finite-extinction witness and a completed topology extraction package
give the one-point compactification recognition used by the puncture transport
theorems.
-/
theorem homeomorph_to_onePoint_threeSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
    (homeomorphism_of_topology_package package M extinction)

/--
The package-level one-point compactification recognition transports each
single-puncture complement to the Euclidean chart.
-/
theorem homeomorph_compl_singleton_euclidean_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) :=
  ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) x⟩

/--
The package-level one-point compactification recognition transports each
two-puncture complement to a punctured Euclidean chart.
-/
theorem exists_homeomorph_twoPointComplement_puncturedEuclidean_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) :=
  exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) hyx

/--
The package-level homeomorphism projection transports each single-puncture
complement to Euclidean space, hence makes it contractible.
-/
theorem compl_singleton_contractibleSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) := by
  rcases
    homeomorph_compl_singleton_euclidean_of_topology_package
      package M extinction x with ⟨chart⟩
  exact chart.contractibleSpace

/--
The package-level single-puncture contractibility projection gives
path-connectedness of every single-puncture complement.
-/
theorem compl_singleton_pathConnectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    PathConnectedSpace ({x}ᶜ : Set M) := by
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  infer_instance

/--
Any two points in a package-selected single-puncture complement are joined by a
path.
-/
theorem compl_singleton_path_nonempty_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Nonempty (Path a b) := by
  intro a b
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      package M extinction x
  exact PathConnectedSpace.joined a b

/--
The path component of any point in a package-selected single-puncture
complement is the whole complement.
-/
theorem compl_singleton_pathComponent_eq_univ_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    pathComponent basepoint = Set.univ := by
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      package M extinction x
  ext y
  constructor
  · intro _hy
    exact Set.mem_univ y
  · intro _hy
    exact PathConnectedSpace.joined basepoint y

/--
A package-selected single-puncture complement is connected.
-/
theorem compl_singleton_connectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ConnectedSpace ({x}ᶜ : Set M) := by
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      package M extinction x
  infer_instance

/--
A package-selected single-puncture complement is nonempty.
-/
theorem compl_singleton_nonempty_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    Nonempty ({x}ᶜ : Set M) := by
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      package M extinction x
  infer_instance

/--
The zeroth homotopy quotient of a package-selected single-puncture complement
has only one class.
-/
theorem compl_singleton_zerothHomotopy_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) := by
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      package M extinction x
  infer_instance

/--
Any two zeroth-homotopy classes in a package-selected single-puncture
complement agree.
-/
theorem compl_singleton_zerothHomotopy_mk_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (a b : ({x}ᶜ : Set M)) :
    ZerothHomotopy.mk a = ZerothHomotopy.mk b := by
  letI : Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) :=
    compl_singleton_zerothHomotopy_subsingleton_of_topology_package
      package M extinction x
  exact Subsingleton.elim _ _

/--
The zeroth homotopy quotient of a package-selected single-puncture complement
has a unique class.
-/
theorem compl_singleton_zerothHomotopy_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ∃ baseClass : ZerothHomotopy ({x}ᶜ : Set M),
      ∀ homotopyClass : ZerothHomotopy ({x}ᶜ : Set M),
        homotopyClass = baseClass := by
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      package M extinction x
  let basePoint : ({x}ᶜ : Set M) :=
    Classical.choice (PathConnectedSpace.nonempty (X := ({x}ᶜ : Set M)))
  exact ⟨ZerothHomotopy.mk basePoint, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The zeroth homotopy group of a package-selected single-puncture complement has
only one class.
-/
theorem compl_singleton_piZero_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := ({x}ᶜ : Set M))
      (x := basepoint)).subsingleton_congr).mpr
        (compl_singleton_zerothHomotopy_subsingleton_of_topology_package
          package M extinction x)

/--
Any two zeroth homotopy group classes in a package-selected single-puncture
complement agree.
-/
theorem compl_singleton_piZero_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M))
    (a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) :
    a = b := by
  letI : Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_piZero_subsingleton_of_topology_package
      package M extinction x basepoint
  exact Subsingleton.elim _ _

/--
The zeroth homotopy group of a package-selected single-puncture complement has
a unique class.
-/
theorem compl_singleton_piZero_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    ∃ baseClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint,
      ∀ homotopyClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint,
        homotopyClass = baseClass := by
  letI : Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_piZero_subsingleton_of_topology_package
      package M extinction x basepoint
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The package-level single-puncture contractibility projection gives simple
connectedness of every single-puncture complement.
-/
theorem compl_singleton_simplyConnectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    SimplyConnectedSpace ({x}ᶜ : Set M) := by
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  infer_instance

/--
Consequently, every based fundamental group of a single-puncture complement
selected by the topology package is trivial.
-/
theorem compl_singleton_fundamentalGroup_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) := by
  letI : SimplyConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_simplyConnectedSpace_of_topology_package
      package M extinction x
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  infer_instance

/--
Any two based fundamental-group classes in a package-selected
single-puncture complement agree.
-/
theorem compl_singleton_fundamentalGroup_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M))
    (a b : FundamentalGroup ({x}ᶜ : Set M) basepoint) :
    a = b := by
  letI : Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_fundamentalGroup_subsingleton_of_topology_package
      package M extinction x basepoint
  exact Subsingleton.elim _ _

/--
The based fundamental group of a package-selected single-puncture complement
has a unique class.
-/
theorem compl_singleton_fundamentalGroup_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    ∃ baseClass : FundamentalGroup ({x}ᶜ : Set M) basepoint,
      ∀ fundamentalClass : FundamentalGroup ({x}ᶜ : Set M) basepoint,
        fundamentalClass = baseClass := by
  letI : Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_fundamentalGroup_subsingleton_of_topology_package
      package M extinction x basepoint
  exact ⟨Classical.choice inferInstance, fun fundamentalClass => Subsingleton.elim _ _⟩

/--
The same package-level single-puncture collapse, stated for the first homotopy
group.
-/
theorem compl_singleton_piOne_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ({x}ᶜ : Set M))
      (x := basepoint)).subsingleton_congr).mpr
        (compl_singleton_fundamentalGroup_subsingleton_of_topology_package
          package M extinction x basepoint)

/--
Any two first homotopy group classes in a package-selected single-puncture
complement agree.
-/
theorem compl_singleton_piOne_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M))
    (a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :
    a = b := by
  letI : Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_piOne_subsingleton_of_topology_package
      package M extinction x basepoint
  exact Subsingleton.elim _ _

/--
The first homotopy group of a package-selected single-puncture complement has
a unique class.
-/
theorem compl_singleton_piOne_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    ∃ baseClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint,
      ∀ homotopyClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint,
        homotopyClass = baseClass := by
  letI : Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_piOne_subsingleton_of_topology_package
      package M extinction x basepoint
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The package-level homeomorphism projection transports any two-puncture
complement to a punctured Euclidean chart, hence makes it simply connected.
-/
theorem twoPointComplement_simplyConnectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  rcases
    exists_homeomorph_twoPointComplement_puncturedEuclidean_of_topology_package
      package M extinction hyx with ⟨puncture, chartNonempty⟩
  rcases chartNonempty with ⟨chart⟩
  letI : SimplyConnectedSpace ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    euclideanThree_compl_singleton_simplyConnectedSpace puncture
  exact chart.toHomotopyEquiv.simplyConnectedSpace

/--
The package-level two-puncture chart projection gives path-connectedness of
every selected two-puncture complement by transporting it from a punctured
Euclidean chart.
-/
theorem twoPointComplement_pathConnectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  rcases
    exists_homeomorph_twoPointComplement_puncturedEuclidean_of_topology_package
      package M extinction hyx with ⟨puncture, chartNonempty⟩
  rcases chartNonempty with ⟨chart⟩
  letI : PathConnectedSpace ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    euclideanThree_compl_singleton_pathConnectedSpace puncture
  exact chart.symm.surjective.pathConnectedSpace chart.symm.continuous

/--
Any two points in a package-selected two-puncture complement are joined by a
path.
-/
theorem twoPointComplement_path_nonempty_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Nonempty (Path a b) := by
  intro a b
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      package M extinction hyx
  exact PathConnectedSpace.joined a b

/--
The path component of any point in a package-selected two-puncture complement
is the whole complement.
-/
theorem twoPointComplement_pathComponent_eq_univ_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    pathComponent basepoint = Set.univ := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      package M extinction hyx
  ext z
  constructor
  · intro _hz
    exact Set.mem_univ z
  · intro _hz
    exact PathConnectedSpace.joined basepoint z

/--
A package-selected two-puncture complement is connected.
-/
theorem twoPointComplement_connectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      package M extinction hyx
  infer_instance

/--
A package-selected two-puncture complement is nonempty.
-/
theorem twoPointComplement_nonempty_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    Nonempty (({x} ∪ {y})ᶜ : Set M) := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      package M extinction hyx
  infer_instance

/--
The zeroth homotopy quotient of a package-selected two-puncture complement has
only one class.
-/
theorem twoPointComplement_zerothHomotopy_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      package M extinction hyx
  infer_instance

/--
Any two zeroth-homotopy classes in a package-selected two-puncture complement
agree.
-/
theorem twoPointComplement_zerothHomotopy_mk_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (a b : (({x} ∪ {y})ᶜ : Set M)) :
    ZerothHomotopy.mk a = ZerothHomotopy.mk b := by
  letI : Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)) :=
    twoPointComplement_zerothHomotopy_subsingleton_of_topology_package
      package M extinction hyx
  exact Subsingleton.elim _ _

/--
The zeroth homotopy quotient of a package-selected two-puncture complement has
a unique class.
-/
theorem twoPointComplement_zerothHomotopy_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
      ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
        homotopyClass = baseClass := by
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      package M extinction hyx
  let basePoint : (({x} ∪ {y})ᶜ : Set M) :=
    Classical.choice
      (PathConnectedSpace.nonempty (X := (({x} ∪ {y})ᶜ : Set M)))
  exact ⟨ZerothHomotopy.mk basePoint, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The zeroth homotopy group of a package-selected two-puncture complement has
only one class.
-/
theorem twoPointComplement_piZero_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton
      (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  exact
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := (({x} ∪ {y})ᶜ : Set M))
      (x := basepoint)).subsingleton_congr).mpr
        (twoPointComplement_zerothHomotopy_subsingleton_of_topology_package
          package M extinction hyx)

/--
Any two zeroth homotopy group classes in a package-selected two-puncture
complement agree.
-/
theorem twoPointComplement_piZero_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M))
    (a b :
      HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) :
    a = b := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
    twoPointComplement_piZero_subsingleton_of_topology_package
      package M extinction hyx basepoint
  exact Subsingleton.elim _ _

/--
The zeroth homotopy group of a package-selected two-puncture complement has a
unique class.
-/
theorem twoPointComplement_piZero_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ baseClass :
      HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
      ∀ homotopyClass :
        HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
    twoPointComplement_piZero_subsingleton_of_topology_package
      package M extinction hyx basepoint
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
Consequently, every based fundamental group of a two-puncture complement
selected by the topology package is trivial.
-/
theorem twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  infer_instance

/--
Any two based fundamental-group classes in a package-selected two-puncture
complement agree.
-/
theorem twoPointComplement_fundamentalGroup_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M))
    (a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :
    a = b := by
  letI : Subsingleton
      (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
    twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint
  exact Subsingleton.elim _ _

/--
The based fundamental group of a package-selected two-puncture complement has
a unique class.
-/
theorem twoPointComplement_fundamentalGroup_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ baseClass : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
      ∀ fundamentalClass :
        FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint,
        fundamentalClass = baseClass := by
  letI : Subsingleton
      (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
    twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint
  exact ⟨Classical.choice inferInstance, fun fundamentalClass => Subsingleton.elim _ _⟩

/--
The same package-level two-puncture collapse, stated for the first homotopy
group.
-/
theorem twoPointComplement_piOne_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton
      (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  exact
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := (({x} ∪ {y})ᶜ : Set M))
      (x := basepoint)).subsingleton_congr).mpr
        (twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
          package M extinction hyx basepoint)

/--
Any two first homotopy group classes in a package-selected two-puncture
complement agree.
-/
theorem twoPointComplement_piOne_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M))
    (a b :
      HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :
    a = b := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
    twoPointComplement_piOne_subsingleton_of_topology_package
      package M extinction hyx basepoint
  exact Subsingleton.elim _ _

/--
The first homotopy group of a package-selected two-puncture complement has a
unique class.
-/
theorem twoPointComplement_piOne_exists_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ baseClass :
      HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
      ∀ homotopyClass :
        HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint,
        homotopyClass = baseClass := by
  letI : Subsingleton
      (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
    twoPointComplement_piOne_subsingleton_of_topology_package
      package M extinction hyx basepoint
  exact ⟨Classical.choice inferInstance, fun homotopyClass => Subsingleton.elim _ _⟩

/--
The completed topology package exposes the contractible single-puncture
complement together with simple connectedness for both the single-puncture and
two-puncture complements selected by a finite-extinction witness.
-/
theorem complement_contractible_and_simplyConnected_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x) :
    ContractibleSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  ⟨ compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  , compl_singleton_simplyConnectedSpace_of_topology_package
      package M extinction x
  , twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  ⟩

/--
The completed topology package supplies the core complement chart,
connectedness, and low-dimensional homotopy-collapse payloads for both one and
two punctures, after choosing a finite-extinction witness.
-/
theorem complement_chart_and_homotopy_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      ConnectedSpace ({x}ᶜ : Set M) ∧
      Nonempty ({x}ᶜ : Set M) ∧
      Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
      Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
      ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
      Subsingleton
        (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) :=
  ⟨ homeomorph_compl_singleton_euclidean_of_topology_package
      package M extinction x
  , exists_homeomorph_twoPointComplement_puncturedEuclidean_of_topology_package
      package M extinction hyx
  , compl_singleton_connectedSpace_of_topology_package
      package M extinction x
  , compl_singleton_nonempty_of_topology_package
      package M extinction x
  , compl_singleton_piZero_subsingleton_of_topology_package
      package M extinction x singleBasepoint
  , compl_singleton_piOne_subsingleton_of_topology_package
      package M extinction x singleBasepoint
  , twoPointComplement_connectedSpace_of_topology_package
      package M extinction hyx
  , twoPointComplement_nonempty_of_topology_package
      package M extinction hyx
  , twoPointComplement_piZero_subsingleton_of_topology_package
      package M extinction hyx twoBasepoint
  , twoPointComplement_piOne_subsingleton_of_topology_package
      package M extinction hyx twoBasepoint
  ⟩

/--
The completed topology package also supplies concrete unique-class witnesses
for the collapsed low-dimensional homotopy objects of both one and two
punctures.
-/
theorem complement_unique_class_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    (∃ baseClass : ZerothHomotopy ({x}ᶜ : Set M),
      ∀ homotopyClass : ZerothHomotopy ({x}ᶜ : Set M),
        homotopyClass = baseClass) ∧
      (∃ baseClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
        ∀ homotopyClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
        ∀ fundamentalClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
        ∀ homotopyClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
        ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        ∀ fundamentalClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          homotopyClass = baseClass) :=
  ⟨ compl_singleton_zerothHomotopy_exists_unique_of_topology_package
      package M extinction x
  , compl_singleton_piZero_exists_unique_of_topology_package
      package M extinction x singleBasepoint
  , compl_singleton_fundamentalGroup_exists_unique_of_topology_package
      package M extinction x singleBasepoint
  , compl_singleton_piOne_exists_unique_of_topology_package
      package M extinction x singleBasepoint
  , twoPointComplement_zerothHomotopy_exists_unique_of_topology_package
      package M extinction hyx
  , twoPointComplement_piZero_exists_unique_of_topology_package
      package M extinction hyx twoBasepoint
  , twoPointComplement_fundamentalGroup_exists_unique_of_topology_package
      package M extinction hyx twoBasepoint
  , twoPointComplement_piOne_exists_unique_of_topology_package
      package M extinction hyx twoBasepoint
  ⟩

/--
The completed topology package supplies equality of arbitrary low-dimensional
homotopy classes for both one and two punctures.
-/
theorem complement_class_equality_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    (∀ a b : ({x}ᶜ : Set M),
      ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
        a = b) ∧
      (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
        a = b) ∧
      (∀ a b : (({x} ∪ {y})ᶜ : Set M),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        a = b) :=
  ⟨ compl_singleton_zerothHomotopy_mk_eq_of_topology_package
      package M extinction x
  , compl_singleton_piZero_eq_of_topology_package
      package M extinction x singleBasepoint
  , compl_singleton_fundamentalGroup_eq_of_topology_package
      package M extinction x singleBasepoint
  , compl_singleton_piOne_eq_of_topology_package
      package M extinction x singleBasepoint
  , twoPointComplement_zerothHomotopy_mk_eq_of_topology_package
      package M extinction hyx
  , twoPointComplement_piZero_eq_of_topology_package
      package M extinction hyx twoBasepoint
  , twoPointComplement_fundamentalGroup_eq_of_topology_package
      package M extinction hyx twoBasepoint
  , twoPointComplement_piOne_eq_of_topology_package
      package M extinction hyx twoBasepoint
  ⟩

/--
The completed topology package supplies joined-path and path-component-collapse
payloads for both one and two punctures.
-/
theorem complement_path_component_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x) :
    (∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
      (∀ basepoint : ({x}ᶜ : Set M),
        pathComponent basepoint = Set.univ) ∧
      (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
      (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
        pathComponent basepoint = Set.univ) :=
  ⟨ compl_singleton_path_nonempty_of_topology_package
      package M extinction x
  , compl_singleton_pathComponent_eq_univ_of_topology_package
      package M extinction x
  , twoPointComplement_path_nonempty_of_topology_package
      package M extinction hyx
  , twoPointComplement_pathComponent_eq_univ_of_topology_package
      package M extinction hyx
  ⟩

/--
The completed topology package gives a single full complement-collapse payload:
chart data, contractibility/simple-connectedness, class equality, unique-class
witnesses, and path-component collapse for the singleton and two-point
complements selected by a finite-extinction witness.
-/
theorem complete_complement_collapse_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    (ContractibleSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M)) ∧
      (Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint)) ∧
      ((∀ a b : ({x}ᶜ : Set M),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b)) ∧
      ((∃ baseClass : ZerothHomotopy ({x}ᶜ : Set M),
        ∀ homotopyClass : ZerothHomotopy ({x}ᶜ : Set M),
          homotopyClass = baseClass) ∧
        (∃ baseClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
          ∀ homotopyClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
          ∀ fundamentalClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
          ∀ homotopyClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ fundamentalClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            homotopyClass = baseClass)) ∧
      ((∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
        (∀ basepoint : ({x}ᶜ : Set M),
          pathComponent basepoint = Set.univ) ∧
        (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
        (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
          pathComponent basepoint = Set.univ)) :=
  ⟨ complement_contractible_and_simplyConnected_payload_of_topology_package
      package M extinction x hyx
  , complement_chart_and_homotopy_payload_of_topology_package
      package M extinction x hyx singleBasepoint twoBasepoint
  , complement_class_equality_payload_of_topology_package
      package M extinction x hyx singleBasepoint twoBasepoint
  , complement_unique_class_payload_of_topology_package
      package M extinction x hyx singleBasepoint twoBasepoint
  , complement_path_component_payload_of_topology_package
      package M extinction x hyx
  ⟩

/--
The completed topology package exposes the global post-extinction extractor and
the complete point-selected recognition/collapse payload at every
finite-extinction target: sphere recognition, one-point compactification
recognition, and the full singleton/two-point complement collapse.
-/
def TopologyPackageExtractorAndCompleteComplementPayloadStatement
    (_package : ExtinctionTopologyExtractionPackage.{u}) : Prop :=
    ExtinctionImpliesSphereStatement.{u} ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (_extinction : FiniteExtinctionByRicciFlowWithSurgery M)
        (x : M) {y : M} (_hyx : y ≠ x)
        (singleBasepoint : ({x}ᶜ : Set M))
        (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)),
          Nonempty (M ≃ₜ ThreeSphere) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (ContractibleSpace ({x}ᶜ : Set M) ∧
            SimplyConnectedSpace ({x}ᶜ : Set M) ∧
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M)) ∧
          (Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
            (∃ puncture : EuclideanSpace ℝ (Fin 3),
              Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
            ConnectedSpace ({x}ᶜ : Set M) ∧
            Nonempty ({x}ᶜ : Set M) ∧
            Subsingleton
              (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
            ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
            Subsingleton
              (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint)) ∧
          ((∀ a b : ({x}ᶜ : Set M),
            ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
            (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
              a = b) ∧
            (∀ a b : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
              a = b) ∧
            (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
              a = b) ∧
            (∀ a b : (({x} ∪ {y})ᶜ : Set M),
              ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
            (∀ a b :
              HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
              a = b) ∧
            (∀ a b :
              FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
              a = b) ∧
            (∀ a b :
              HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
              a = b)) ∧
          ((∃ baseClass : ZerothHomotopy ({x}ᶜ : Set M),
            ∀ homotopyClass : ZerothHomotopy ({x}ᶜ : Set M),
              homotopyClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
                homotopyClass = baseClass) ∧
            (∃ baseClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
              ∀ fundamentalClass :
                FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
                fundamentalClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
                homotopyClass = baseClass) ∧
            (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
              ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
                homotopyClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                homotopyClass = baseClass) ∧
            (∃ baseClass :
              FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
              ∀ fundamentalClass :
                FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                fundamentalClass = baseClass) ∧
            (∃ baseClass :
              HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
              ∀ homotopyClass :
                HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                homotopyClass = baseClass)) ∧
          ((∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
            (∀ basepoint : ({x}ᶜ : Set M),
              pathComponent basepoint = Set.univ) ∧
            (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
            (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
              pathComponent basepoint = Set.univ))

/--
The completed package payload statement is definitionally the extractor plus
point-selected recognition/collapse family.
-/
theorem topologyPackageExtractorAndCompleteComplementPayloadStatement_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    TopologyPackageExtractorAndCompleteComplementPayloadStatement package =
      (ExtinctionImpliesSphereStatement.{u} ∧
        ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [SimplyConnectedSpace M] [CompactSpace M]
          (_extinction : FiniteExtinctionByRicciFlowWithSurgery M)
          (x : M) {y : M} (_hyx : y ≠ x)
          (singleBasepoint : ({x}ᶜ : Set M))
          (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)),
            Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            (ContractibleSpace ({x}ᶜ : Set M) ∧
              SimplyConnectedSpace ({x}ᶜ : Set M) ∧
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M)) ∧
            (Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
              (∃ puncture : EuclideanSpace ℝ (Fin 3),
                Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
              ConnectedSpace ({x}ᶜ : Set M) ∧
              Nonempty ({x}ᶜ : Set M) ∧
              Subsingleton
                (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
              Subsingleton
                (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
              ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
              Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
              Subsingleton
                (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
              Subsingleton
                (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint)) ∧
            ((∀ a b : ({x}ᶜ : Set M),
              ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
              (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
                a = b) ∧
              (∀ a b : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
                a = b) ∧
              (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
                a = b) ∧
              (∀ a b : (({x} ∪ {y})ᶜ : Set M),
                ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
              (∀ a b :
                HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                a = b) ∧
              (∀ a b :
                FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                a = b) ∧
              (∀ a b :
                HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                a = b)) ∧
            ((∃ baseClass : ZerothHomotopy ({x}ᶜ : Set M),
              ∀ homotopyClass : ZerothHomotopy ({x}ᶜ : Set M),
                homotopyClass = baseClass) ∧
              (∃ baseClass :
                HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
                ∀ homotopyClass :
                  HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
                  homotopyClass = baseClass) ∧
              (∃ baseClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
                ∀ fundamentalClass :
                  FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
                  fundamentalClass = baseClass) ∧
              (∃ baseClass :
                HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
                ∀ homotopyClass :
                  HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
                  homotopyClass = baseClass) ∧
              (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
                ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
                  homotopyClass = baseClass) ∧
              (∃ baseClass :
                HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                ∀ homotopyClass :
                  HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                  homotopyClass = baseClass) ∧
              (∃ baseClass :
                FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                ∀ fundamentalClass :
                  FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                  fundamentalClass = baseClass) ∧
              (∃ baseClass :
                HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                ∀ homotopyClass :
                  HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
                  homotopyClass = baseClass)) ∧
            ((∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
              (∀ basepoint : ({x}ᶜ : Set M),
                pathComponent basepoint = Set.univ) ∧
              (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
              (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                pathComponent basepoint = Set.univ))) :=
  rfl

/--
The completed topology package proves the named extractor plus complete
complement-collapse payload statement.
-/
theorem topology_package_extractor_and_complete_complement_payload
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    TopologyPackageExtractorAndCompleteComplementPayloadStatement package := by
  refine ⟨?_, ?_⟩
  · exact extinction_implies_sphere_of_topology_package package
  · intro M _top _t2 _charted _simple _compact extinction x y hyx
      singleBasepoint twoBasepoint
    exact
      ⟨ homeomorphism_of_topology_package package M extinction
      , homeomorph_to_onePoint_threeSpace_of_topology_package
          package M extinction
      , complete_complement_collapse_payload_of_topology_package
          package M extinction x hyx singleBasepoint twoBasepoint
      ⟩

/--
The named topology payload exposes the global finite-extinction-to-sphere
extractor without requiring downstream files to unpack its product shape.
-/
theorem extinction_implies_sphere_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    (package : ExtinctionTopologyExtractionPackage.{u})
    (payload : TopologyPackageExtractorAndCompleteComplementPayloadStatement package) :
    ExtinctionImpliesSphereStatement.{u} :=
  payload.1

/--
The named topology payload projects to the point-selected recognition and full
complement-collapse package for a fixed finite-extinction target.
-/
theorem recognition_and_complete_complement_payload_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    (package : ExtinctionTopologyExtractionPackage.{u})
    (payload : TopologyPackageExtractorAndCompleteComplementPayloadStatement package)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      (ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M)) ∧
      (Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint)) ∧
      ((∀ a b : ({x}ᶜ : Set M),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b)) ∧
      ((∃ baseClass : ZerothHomotopy ({x}ᶜ : Set M),
        ∀ homotopyClass : ZerothHomotopy ({x}ᶜ : Set M),
          homotopyClass = baseClass) ∧
        (∃ baseClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
          ∀ homotopyClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
          ∀ fundamentalClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
          ∀ homotopyClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ fundamentalClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            homotopyClass = baseClass)) ∧
      ((∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
        (∀ basepoint : ({x}ᶜ : Set M),
          pathComponent basepoint = Set.univ) ∧
        (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
        (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
          pathComponent basepoint = Set.univ)) :=
  payload.2 M extinction x hyx singleBasepoint twoBasepoint

/--
The named topology payload gives the final sphere-recognition certificate for a
fixed finite-extinction target.
-/
theorem homeomorphism_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    (package : ExtinctionTopologyExtractionPackage.{u})
    (payload : TopologyPackageExtractorAndCompleteComplementPayloadStatement package)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  (recognition_and_complete_complement_payload_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    package payload M extinction x hyx singleBasepoint twoBasepoint).1

/--
The named topology payload gives the one-point compactification recognition
used by puncture-transport consumers.
-/
theorem onePoint_recognition_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    (package : ExtinctionTopologyExtractionPackage.{u})
    (payload : TopologyPackageExtractorAndCompleteComplementPayloadStatement package)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  (recognition_and_complete_complement_payload_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    package payload M extinction x hyx singleBasepoint twoBasepoint).2.1

/--
The named topology payload projects to the full complement-collapse certificate
without exposing the sphere-recognition fields.
-/
theorem complete_complement_collapse_payload_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    (package : ExtinctionTopologyExtractionPackage.{u})
    (payload : TopologyPackageExtractorAndCompleteComplementPayloadStatement package)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    (ContractibleSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M)) ∧
      (Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        ConnectedSpace ({x}ᶜ : Set M) ∧
        Nonempty ({x}ᶜ : Set M) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
        ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
        Subsingleton
          (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint)) ∧
      ((∀ a b : ({x}ᶜ : Set M),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
          a = b) ∧
        (∀ a b : (({x} ∪ {y})ᶜ : Set M),
          ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
        (∀ a b :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b) ∧
        (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b) ∧
        (∀ a b :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          a = b)) ∧
      ((∃ baseClass : ZerothHomotopy ({x}ᶜ : Set M),
        ∀ homotopyClass : ZerothHomotopy ({x}ᶜ : Set M),
          homotopyClass = baseClass) ∧
        (∃ baseClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
          ∀ homotopyClass : HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
          ∀ fundamentalClass : FundamentalGroup ({x}ᶜ : Set M) singleBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
          ∀ homotopyClass : HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
            homotopyClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            homotopyClass = baseClass) ∧
        (∃ baseClass : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ fundamentalClass :
            FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            fundamentalClass = baseClass) ∧
        (∃ baseClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          ∀ homotopyClass :
            HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
            homotopyClass = baseClass)) ∧
      ((∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
        (∀ basepoint : ({x}ᶜ : Set M),
          pathComponent basepoint = Set.univ) ∧
        (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
        (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
          pathComponent basepoint = Set.univ)) :=
  (recognition_and_complete_complement_payload_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    package payload M extinction x hyx singleBasepoint twoBasepoint).2.2

/--
The named topology payload gives a compact two-puncture low-homotopy collapse
certificate: connectedness, nonemptiness, collapsed π₀/π₁ objects, unique
classes, and path-component collapse.
-/
theorem twoPointComplement_lowHomotopyCollapse_payload_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
    (package : ExtinctionTopologyExtractionPackage.{u})
    (payload : TopologyPackageExtractorAndCompleteComplementPayloadStatement package)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
      Subsingleton
        (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
      (∀ a b : (({x} ∪ {y})ᶜ : Set M),
        ZerothHomotopy.mk a = ZerothHomotopy.mk b) ∧
      (∀ a b :
        HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        a = b) ∧
      (∀ a b : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        a = b) ∧
      (∀ a b :
        HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        a = b) ∧
      (∃ baseClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
        ∀ homotopyClass : ZerothHomotopy (({x} ∪ {y})ᶜ : Set M),
          homotopyClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          homotopyClass = baseClass) ∧
      (∃ baseClass : FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        ∀ fundamentalClass :
          FundamentalGroup (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          fundamentalClass = baseClass) ∧
      (∃ baseClass :
        HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
        ∀ homotopyClass :
          HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint,
          homotopyClass = baseClass) ∧
      (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
      (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
        pathComponent basepoint = Set.univ) := by
  rcases
    complete_complement_collapse_payload_of_topologyPackageExtractorAndCompleteComplementPayloadStatement
      package payload M extinction x hyx singleBasepoint twoBasepoint with
    ⟨_, chartAndHomotopy, classEquality, uniqueClass, pathComponentPayload⟩
  rcases chartAndHomotopy with
    ⟨_, _, _, _, _, _, connected, nonempty, piZeroSubsingleton,
      piOneSubsingleton⟩
  rcases classEquality with
    ⟨_, _, _, _, zerothMkEq, piZeroEq, fundamentalGroupEq, piOneEq⟩
  rcases uniqueClass with
    ⟨_, _, _, _, zerothUnique, piZeroUnique, fundamentalGroupUnique,
      piOneUnique⟩
  rcases pathComponentPayload with
    ⟨_, _, pathNonempty, pathComponentEqUniv⟩
  exact
    ⟨ connected, nonempty, piZeroSubsingleton, piOneSubsingleton
    , zerothMkEq, piZeroEq, fundamentalGroupEq, piOneEq
    , zerothUnique, piZeroUnique, fundamentalGroupUnique, piOneUnique
    , pathNonempty, pathComponentEqUniv
    ⟩

/--
Named production input for the first topology-package field: each finite
extinction witness supplies explicit certified decomposition data.
-/
def ExtinctionTopologyDecompositionDataStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      Nonempty (ExtinctionTopologyDecompositionData M extinction)

/-- The decomposition-data statement is exactly its theorem-shaped family. -/
theorem extinctionTopologyDecompositionDataStatement_eq :
    ExtinctionTopologyDecompositionDataStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          Nonempty (ExtinctionTopologyDecompositionData M extinction)) :=
  rfl

/--
Certified finite-extinction decomposition data now constructs the first
topology-package field for that fixed extinction witness.
-/
theorem extinction_topology_decomposition_of_decomposition_data_current_interface
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decompositionData : ExtinctionTopologyDecompositionData M extinction) :
    HasExtinctionTopologyDecomposition M extinction :=
  HasExtinctionTopologyDecomposition.ofData decompositionData

/--
The data statement supplies exactly the package-level decomposition witness
family. The next topology-production field is reconstruction of the surgery
trace for the decomposition selected here.
-/
theorem extinction_topology_decomposition_statement_of_decomposition_data_current_interface
    (decompositionData : ExtinctionTopologyDecompositionDataStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionTopologyDecomposition M extinction := by
  intro M _top _t2 _charted _simple _compact extinction
  rcases decompositionData M extinction with ⟨data⟩
  exact extinction_topology_decomposition_of_decomposition_data_current_interface
    M extinction data

/--
The concrete decomposition-data production input discharges the standalone
first-field witness statement used by the topology package interface.
-/
theorem extinctionTopologyDecompositionWitnessStatement_of_decomposition_data_current_interface
    (decompositionData : ExtinctionTopologyDecompositionDataStatement.{u}) :
    ExtinctionTopologyDecompositionWitnessStatement.{u} :=
  extinction_topology_decomposition_statement_of_decomposition_data_current_interface
    decompositionData

/-- This bridge is definitionally the data-to-first-field projection above. -/
theorem extinctionTopologyDecompositionWitnessStatement_of_decomposition_data_current_interface_eq
    (decompositionData : ExtinctionTopologyDecompositionDataStatement.{u}) :
    extinctionTopologyDecompositionWitnessStatement_of_decomposition_data_current_interface
        decompositionData =
      extinction_topology_decomposition_statement_of_decomposition_data_current_interface
        decompositionData :=
  rfl

end Poincare
