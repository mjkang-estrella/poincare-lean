import Poincare.ProofProgress.TopologyExtractionPunctureTransport

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
The package-level homeomorphism projection transports each single-puncture
complement to Euclidean space, hence makes it contractible.
-/
theorem compl_singleton_contractibleSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) :=
  compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) x

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
    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) hyx

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
    Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) hyx basepoint

/--
Consumer-facing recognition and puncture payload from one completed topology
package: the same finite-extinction witness supplies sphere recognition,
one-point compactification recognition, singleton-complement contractibility,
two-puncture simple connectedness, and trivial based fundamental groups for
two-puncture complements.
-/
theorem topology_package_recognition_and_puncture_payload
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      ContractibleSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  ⟨ homeomorphism_of_topology_package package M extinction
  , homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction
  , compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  , twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  , twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint
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

end Poincare
