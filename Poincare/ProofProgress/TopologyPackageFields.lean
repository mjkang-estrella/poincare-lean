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
A completed topology extraction package supplies the final-homeomorphism
payload for its stored decomposition witness.
-/
theorem finalHomeomorphismPayloadData_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    FinalHomeomorphismPayloadData M extinction
      (extinction_decomposition_of_topology_package package M extinction) where
  homeomorphism := homeomorphism_of_topology_package package M extinction

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
The package-level single-puncture complement is simply connected as a
class-level consequence of the transported contractible Euclidean chart.
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
The package-level single-puncture complement is path-connected as a direct
consequence of its contractibility.
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
The package-level single-puncture complement is connected as a direct
consequence of its path-connectedness.
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
The package-level single-puncture complement is nonempty, since it is
path-connected after contractibility is transported from the one-point model.
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
Every based loop in a package-selected single-puncture complement is
null-homotopic, because the topology package identifies that complement with a
contractible Euclidean chart.
-/
theorem compl_singleton_loop_nullhomotopic_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ∀ (basepoint : ({x}ᶜ : Set M)) (γ : Path basepoint basepoint),
      Path.Homotopic γ (Path.refl basepoint) := by
  intro basepoint γ
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  exact SimplyConnectedSpace.paths_homotopic γ (Path.refl basepoint)

/--
Any two paths with the same endpoints in a package-selected single-puncture
complement are homotopic.
-/
theorem compl_singleton_paths_homotopic_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ∀ {a b : ({x}ᶜ : Set M)} (γ η : Path a b),
      Path.Homotopic γ η := by
  intro a b γ η
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  exact SimplyConnectedSpace.paths_homotopic γ η

/--
Any two same-endpoint paths in a package-selected single-puncture complement
carry both their path homotopy and the induced equality of path-homotopy
quotient classes.
-/
theorem compl_singleton_paths_homotopic_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    {a b : ({x}ᶜ : Set M)} (γ η : Path a b) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ := by
  let h : Path.Homotopic γ η :=
    compl_singleton_paths_homotopic_of_topology_package
      package M extinction x γ η
  exact ⟨h, Quotient.sound h⟩

/--
Any two points in a package-selected single-puncture complement are joined by
an actual path.
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
The package-level single-puncture complement joins any two points in mathlib's
`Joined` relation, after extracting the transported path-connectedness field.
-/
theorem compl_singleton_joined_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ∀ (a b : ({x}ᶜ : Set M)), Joined a b := by
  intro a b
  letI : PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      package M extinction x
  exact PathConnectedSpace.joined a b

/--
The package-level single-puncture complement has exactly one path component:
every point is in the path component of any chosen basepoint.
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
  · intro _
    exact Set.mem_univ y
  · intro _
    exact PathConnectedSpace.joined basepoint y

/--
Package-level single-puncture path-component collapse, bundled with a chosen
path from the basepoint to every target point of the complement.
-/
noncomputable def compl_singleton_pointedPathComponentPathData_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    PointedPathComponentPathData ({x}ᶜ : Set M) basepoint :=
  pointedPathComponentPathData_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_topology_package
      package M extinction x basepoint)

/--
Extract a concrete package-level path from the chosen basepoint to any point
of a single-puncture complement.
-/
noncomputable def compl_singleton_chosenPath_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    Path basepoint z :=
  (compl_singleton_pointedPathComponentPathData_of_topology_package
    package M extinction x basepoint).path_to z

/--
A topology package supplies endpoint-level data for the concrete chosen path
from a single-puncture basepoint to any target point.
-/
noncomputable def compl_singleton_chosenPathEndpointData_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    PointedChosenPathEndpointData ({x}ᶜ : Set M) basepoint z :=
  chosenPathEndpointData_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_topology_package
      package M extinction x basepoint) z

/-- The package-level single-puncture chosen path starts at its basepoint. -/
theorem compl_singleton_chosenPath_source_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    compl_singleton_chosenPath_of_topology_package
      package M extinction x basepoint z 0 = basepoint := by
  exact chosenPath_source_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_topology_package
      package M extinction x basepoint) z

/-- The package-level single-puncture chosen path ends at its target point. -/
theorem compl_singleton_chosenPath_target_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    compl_singleton_chosenPath_of_topology_package
      package M extinction x basepoint z 1 = z := by
  exact chosenPath_target_of_pathComponent_eq_univ basepoint
    (compl_singleton_pathComponent_eq_univ_of_topology_package
      package M extinction x basepoint) z

/--
The package-level single-puncture chosen path is a concrete `Joined` witness
from the basepoint to the target.
-/
theorem compl_singleton_chosenPath_joined_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    Joined basepoint z :=
  ⟨compl_singleton_chosenPath_of_topology_package
    package M extinction x basepoint z⟩

/--
A topology package gives an explicit path between a basepoint and target in any
package-selected single-puncture complement, together with both endpoint
equations.
-/
theorem compl_singleton_exists_path_with_endpoints_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z := by
  refine ⟨compl_singleton_chosenPath_of_topology_package
    package M extinction x basepoint z, ?_, ?_, ?_⟩
  · exact compl_singleton_chosenPath_source_of_topology_package
      package M extinction x basepoint z
  · exact compl_singleton_chosenPath_target_of_topology_package
      package M extinction x basepoint z
  · exact compl_singleton_chosenPath_joined_of_topology_package
      package M extinction x basepoint z

/--
The package-selected single-puncture chosen path is homotopic to every other
path with the same endpoints.
-/
theorem compl_singleton_chosenPath_homotopic_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) (η : Path basepoint z) :
    Path.Homotopic
      (compl_singleton_chosenPath_of_topology_package
        package M extinction x basepoint z) η :=
  compl_singleton_paths_homotopic_of_topology_package
    package M extinction x
    (compl_singleton_chosenPath_of_topology_package
      package M extinction x basepoint z) η

/--
The package-selected single-puncture chosen path represents the unique
path-homotopy quotient class between its endpoints.
-/
theorem compl_singleton_chosenPath_quotient_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) (η : Path basepoint z) :
    (⟦compl_singleton_chosenPath_of_topology_package
      package M extinction x basepoint z⟧ :
        Path.Homotopic.Quotient basepoint z) = ⟦η⟧ :=
  Quotient.sound
    (compl_singleton_chosenPath_homotopic_of_topology_package
      package M extinction x basepoint z η)

/--
A package-selected single-puncture complement supplies one concrete path
witness from a chosen basepoint to a target, together with endpoint equations,
the `Joined` witness, and uniqueness up to path homotopy.
-/
theorem compl_singleton_exists_path_with_endpoints_and_homotopy_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z ∧
        ∀ η : Path basepoint z, Path.Homotopic γ η := by
  refine ⟨compl_singleton_chosenPath_of_topology_package
    package M extinction x basepoint z, ?_, ?_, ?_, ?_⟩
  · exact compl_singleton_chosenPath_source_of_topology_package
      package M extinction x basepoint z
  · exact compl_singleton_chosenPath_target_of_topology_package
      package M extinction x basepoint z
  · exact compl_singleton_chosenPath_joined_of_topology_package
      package M extinction x basepoint z
  · intro η
    exact compl_singleton_chosenPath_homotopic_of_topology_package
      package M extinction x basepoint z η

/--
A package-selected single-puncture complement supplies endpoint-certified path
data whose path is unique up to homotopy among paths with the same endpoints.
-/
theorem compl_singleton_exists_chosenPathEndpointData_homotopy_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint z : ({x}ᶜ : Set M)) :
    ∃ data : PointedChosenPathEndpointData ({x}ᶜ : Set M) basepoint z,
      ∀ η : Path basepoint z, Path.Homotopic data.path η := by
  refine ⟨compl_singleton_chosenPathEndpointData_of_topology_package
    package M extinction x basepoint z, ?_⟩
  intro η
  exact compl_singleton_chosenPath_homotopic_of_topology_package
    package M extinction x basepoint z η

/--
Every path-homotopy quotient in a package-selected single-puncture complement
is a subsingleton.
-/
theorem compl_singleton_pathQuotient_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
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
        (compl_singleton_paths_homotopic_of_topology_package
          package M extinction x γ η)

/--
Every based fundamental group in a package-selected single-puncture complement
is trivial.
-/
theorem compl_singleton_fundamentalGroup_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) := by
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  exact
    compl_singleton_pathQuotient_subsingleton_of_topology_package
      package M extinction x basepoint basepoint

/--
Every based loop in a package-selected single-puncture complement represents
the stationary loop in the fundamental group.
-/
theorem compl_singleton_loop_fromPath_eq_refl_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) (γ : Path basepoint basepoint) :
    FundamentalGroup.fromPath
        (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint) =
      FundamentalGroup.fromPath
        (⟦Path.refl basepoint⟧ :
          Path.Homotopic.Quotient basepoint basepoint) := by
  letI : Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_fundamentalGroup_subsingleton_of_topology_package
      package M extinction x basepoint
  exact Subsingleton.elim
    (FundamentalGroup.fromPath
      (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint))
    (FundamentalGroup.fromPath
      (⟦Path.refl basepoint⟧ :
        Path.Homotopic.Quotient basepoint basepoint))

/--
Every based first homotopy group in a package-selected single-puncture
complement is trivial.
-/
theorem compl_singleton_piOne_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := ({x}ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
      (compl_singleton_fundamentalGroup_subsingleton_of_topology_package
        package M extinction x basepoint)

/--
A completed topology extraction package exposes the actual single-puncture
Euclidean chart transported from the one-point compactification recognition.
-/
theorem exists_homeomorph_compl_singleton_euclidean_of_topology_package
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
A completed topology extraction package exposes the transported
single-puncture Euclidean chart together with contractibility, endpoint
certified chosen paths, homotopy uniqueness, and fundamental-group triviality.
-/
theorem exists_homeomorph_compl_singleton_euclidean_with_endpoint_data_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ∃ _chart : ({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3),
      ContractibleSpace ({x}ᶜ : Set M) ∧
        (∀ basepoint z : ({x}ᶜ : Set M),
          ∃ data : PointedChosenPathEndpointData ({x}ᶜ : Set M) basepoint z,
            ∀ η : Path basepoint z, Path.Homotopic data.path η) ∧
        (∀ basepoint : ({x}ᶜ : Set M),
          Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint)) := by
  refine ⟨
    homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
      (homeomorph_to_onePoint_threeSpace_of_topology_package
        package M extinction) x,
    ?_, ?_, ?_⟩
  · exact compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  · intro basepoint z
    exact compl_singleton_exists_chosenPathEndpointData_homotopy_unique_of_topology_package
      package M extinction x basepoint z
  · intro basepoint
    exact compl_singleton_fundamentalGroup_subsingleton_of_topology_package
      package M extinction x basepoint

/--
A package-selected single-puncture complement supplies a concrete based loop
payload: the selected loop has certified endpoints, is null-homotopic, and
represents the stationary element in the fundamental group.
-/
theorem compl_singleton_chosenLoop_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    ∃ γ : Path basepoint basepoint,
      γ 0 = basepoint ∧ γ 1 = basepoint ∧
        Path.Homotopic γ (Path.refl basepoint) ∧
        FundamentalGroup.fromPath
            (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint) =
          FundamentalGroup.fromPath
            (⟦Path.refl basepoint⟧ :
              Path.Homotopic.Quotient basepoint basepoint) := by
  let γ : Path basepoint basepoint :=
    compl_singleton_chosenPath_of_topology_package
      package M extinction x basepoint basepoint
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · exact compl_singleton_chosenPath_source_of_topology_package
      package M extinction x basepoint basepoint
  · exact compl_singleton_chosenPath_target_of_topology_package
      package M extinction x basepoint basepoint
  · exact compl_singleton_chosenPath_homotopic_of_topology_package
      package M extinction x basepoint basepoint (Path.refl basepoint)
  · exact compl_singleton_loop_fromPath_eq_refl_of_topology_package
      package M extinction x basepoint γ

/--
A completed topology extraction package exposes the actual two-puncture
Euclidean transport chart, not only its connectivity and fundamental-group
consequences.
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
The package-level two-puncture complement is path-connected as a direct
consequence of its transported simple-connectedness.
-/
theorem twoPointComplement_pathConnectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  infer_instance

/--
The package-level two-puncture complement is connected as a direct consequence
of its transported path-connectedness.
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
The package-level two-puncture complement is nonempty after transported
path-connectedness is installed.
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
Every based loop in a package-selected two-puncture complement represents the
stationary loop in the fundamental group.
-/
theorem twoPointComplement_loop_fromPath_eq_refl_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M))
    (γ : Path basepoint basepoint) :
    FundamentalGroup.fromPath
        (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint) =
      FundamentalGroup.fromPath
        (⟦Path.refl basepoint⟧ :
          Path.Homotopic.Quotient basepoint basepoint) := by
  letI : Subsingleton
      (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
    twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint
  exact Subsingleton.elim
    (FundamentalGroup.fromPath
      (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint))
    (FundamentalGroup.fromPath
      (⟦Path.refl basepoint⟧ :
        Path.Homotopic.Quotient basepoint basepoint))

/--
Consequently, every based first homotopy group of a two-puncture complement
selected by the topology package is trivial.
-/
theorem twoPointComplement_piOne_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := (({x} ∪ {y})ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
    (twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint)

/--
Every based loop in a package-selected two-puncture complement is
null-homotopic, extracting the path-level content of the package-level
fundamental-group computation.
-/
theorem twoPointComplement_loop_nullhomotopic_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ∀ (basepoint : (({x} ∪ {y})ᶜ : Set M))
      (γ : Path basepoint basepoint), Path.Homotopic γ (Path.refl basepoint) := by
  intro basepoint γ
  exact Quotient.exact (s := Path.Homotopic.setoid basepoint basepoint)
    (a := γ) (b := Path.refl basepoint) <| by
    letI : Subsingleton
        (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
      twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
        package M extinction hyx basepoint
    exact Subsingleton.elim
      (FundamentalGroup.fromPath
        (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint))
      (FundamentalGroup.fromPath
        (⟦Path.refl basepoint⟧ : Path.Homotopic.Quotient basepoint basepoint))

/--
Any two paths with the same endpoints in a package-selected two-puncture
complement are homotopic.
-/
theorem twoPointComplement_paths_homotopic_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ∀ {a b : (({x} ∪ {y})ᶜ : Set M)} (γ η : Path a b),
      Path.Homotopic γ η := by
  intro a b γ η
  letI : SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  exact SimplyConnectedSpace.paths_homotopic γ η

/--
Any two same-endpoint paths in a package-selected two-puncture complement carry
both their path homotopy and the induced equality of path-homotopy quotient
classes.
-/
theorem twoPointComplement_paths_homotopic_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    {a b : (({x} ∪ {y})ᶜ : Set M)} (γ η : Path a b) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ := by
  let h : Path.Homotopic γ η :=
    twoPointComplement_paths_homotopic_of_topology_package
      package M extinction hyx γ η
  exact ⟨h, Quotient.sound h⟩

/--
Any two points in a package-selected two-puncture complement are joined by an
actual path.
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
The package-level two-puncture complement joins any two points in mathlib's
`Joined` relation, after extracting transported path-connectedness.
-/
theorem twoPointComplement_joined_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ∀ (a b : (({x} ∪ {y})ᶜ : Set M)), Joined a b := by
  intro a b
  letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      package M extinction hyx
  exact PathConnectedSpace.joined a b

/--
The package-level two-puncture complement has exactly one path component:
every point is in the path component of any chosen basepoint.
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
  · intro _
    exact Set.mem_univ z
  · intro _
    exact PathConnectedSpace.joined basepoint z

/--
Package-level two-puncture path-component collapse, bundled with a chosen path
from the basepoint to every target point of the complement.
-/
noncomputable def twoPointComplement_pointedPathComponentPathData_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) basepoint :=
  pointedPathComponentPathData_of_pathComponent_eq_univ basepoint
    (twoPointComplement_pathComponent_eq_univ_of_topology_package
      package M extinction hyx basepoint)

/--
Extract a concrete package-level path from the chosen basepoint to any point
of a two-puncture complement.
-/
noncomputable def twoPointComplement_chosenPath_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    Path basepoint z :=
  (twoPointComplement_pointedPathComponentPathData_of_topology_package
    package M extinction hyx basepoint).path_to z

/--
A topology package supplies endpoint-level data for the concrete chosen path
from a two-puncture basepoint to any target point.
-/
noncomputable def twoPointComplement_chosenPathEndpointData_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    PointedChosenPathEndpointData (({x} ∪ {y})ᶜ : Set M) basepoint z :=
  chosenPathEndpointData_of_pathComponent_eq_univ basepoint
    (twoPointComplement_pathComponent_eq_univ_of_topology_package
      package M extinction hyx basepoint) z

/-- The package-level two-puncture chosen path starts at its basepoint. -/
theorem twoPointComplement_chosenPath_source_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    twoPointComplement_chosenPath_of_topology_package
      package M extinction hyx basepoint z 0 = basepoint := by
  exact chosenPath_source_of_pathComponent_eq_univ basepoint
    (twoPointComplement_pathComponent_eq_univ_of_topology_package
      package M extinction hyx basepoint) z

/-- The package-level two-puncture chosen path ends at its target point. -/
theorem twoPointComplement_chosenPath_target_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    twoPointComplement_chosenPath_of_topology_package
      package M extinction hyx basepoint z 1 = z := by
  exact chosenPath_target_of_pathComponent_eq_univ basepoint
    (twoPointComplement_pathComponent_eq_univ_of_topology_package
      package M extinction hyx basepoint) z

/--
The package-level two-puncture chosen path is a concrete `Joined` witness from
the basepoint to the target.
-/
theorem twoPointComplement_chosenPath_joined_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    Joined basepoint z :=
  ⟨twoPointComplement_chosenPath_of_topology_package
    package M extinction hyx basepoint z⟩

/--
A topology package gives an explicit path between a basepoint and target in any
package-selected two-puncture complement, together with both endpoint equations.
-/
theorem twoPointComplement_exists_path_with_endpoints_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z := by
  refine ⟨twoPointComplement_chosenPath_of_topology_package
    package M extinction hyx basepoint z, ?_, ?_, ?_⟩
  · exact twoPointComplement_chosenPath_source_of_topology_package
      package M extinction hyx basepoint z
  · exact twoPointComplement_chosenPath_target_of_topology_package
      package M extinction hyx basepoint z
  · exact twoPointComplement_chosenPath_joined_of_topology_package
      package M extinction hyx basepoint z

/--
The package-selected two-puncture chosen path is homotopic to every other path
with the same endpoints.
-/
theorem twoPointComplement_chosenPath_homotopic_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) (η : Path basepoint z) :
    Path.Homotopic
      (twoPointComplement_chosenPath_of_topology_package
        package M extinction hyx basepoint z) η :=
  twoPointComplement_paths_homotopic_of_topology_package
    package M extinction hyx
    (twoPointComplement_chosenPath_of_topology_package
      package M extinction hyx basepoint z) η

/--
The package-selected two-puncture chosen path represents the unique
path-homotopy quotient class between its endpoints.
-/
theorem twoPointComplement_chosenPath_quotient_eq_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) (η : Path basepoint z) :
    (⟦twoPointComplement_chosenPath_of_topology_package
      package M extinction hyx basepoint z⟧ :
        Path.Homotopic.Quotient basepoint z) = ⟦η⟧ :=
  Quotient.sound
    (twoPointComplement_chosenPath_homotopic_of_topology_package
      package M extinction hyx basepoint z η)

/--
A package-selected two-puncture complement supplies one concrete path witness
from a chosen basepoint to a target, together with endpoint equations, the
`Joined` witness, and uniqueness up to path homotopy.
-/
theorem twoPointComplement_exists_path_with_endpoints_and_homotopy_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z ∧
        ∀ η : Path basepoint z, Path.Homotopic γ η := by
  refine ⟨twoPointComplement_chosenPath_of_topology_package
    package M extinction hyx basepoint z, ?_, ?_, ?_, ?_⟩
  · exact twoPointComplement_chosenPath_source_of_topology_package
      package M extinction hyx basepoint z
  · exact twoPointComplement_chosenPath_target_of_topology_package
      package M extinction hyx basepoint z
  · exact twoPointComplement_chosenPath_joined_of_topology_package
      package M extinction hyx basepoint z
  · intro η
    exact twoPointComplement_chosenPath_homotopic_of_topology_package
      package M extinction hyx basepoint z η

/--
A package-selected two-puncture complement supplies endpoint-certified path data
whose path is unique up to homotopy among paths with the same endpoints.
-/
theorem twoPointComplement_exists_chosenPathEndpointData_homotopy_unique_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint z : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ data : PointedChosenPathEndpointData
        (({x} ∪ {y})ᶜ : Set M) basepoint z,
      ∀ η : Path basepoint z, Path.Homotopic data.path η := by
  refine ⟨twoPointComplement_chosenPathEndpointData_of_topology_package
    package M extinction hyx basepoint z, ?_⟩
  intro η
  exact twoPointComplement_chosenPath_homotopic_of_topology_package
    package M extinction hyx basepoint z η

/--
Every path-homotopy quotient in a package-selected two-puncture complement is
a subsingleton.
-/
theorem twoPointComplement_pathQuotient_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
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
        (twoPointComplement_paths_homotopic_of_topology_package
          package M extinction hyx γ η)

/--
A completed topology extraction package exposes the actual two-puncture
punctured-Euclidean chart together with simple connectedness,
endpoint-certified chosen paths, homotopy uniqueness, and fundamental-group
triviality.
-/
theorem exists_homeomorph_twoPointComplement_puncturedEuclidean_with_endpoint_data_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ _chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          (∀ basepoint z : (({x} ∪ {y})ᶜ : Set M),
            ∃ data : PointedChosenPathEndpointData
                (({x} ∪ {y})ᶜ : Set M) basepoint z,
              ∀ η : Path basepoint z, Path.Homotopic data.path η) ∧
          (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
            Subsingleton (FundamentalGroup
              (({x} ∪ {y})ᶜ : Set M) basepoint)) ∧
          (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
            Subsingleton (HomotopyGroup.Pi 1
              (({x} ∪ {y})ᶜ : Set M) basepoint)) := by
  rcases exists_homeomorph_twoPointComplement_puncturedEuclidean_of_topology_package
      package M extinction hyx with
    ⟨puncture, ⟨chart⟩⟩
  refine ⟨puncture, chart, ?_, ?_, ?_, ?_⟩
  · exact twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  · intro basepoint z
    exact twoPointComplement_exists_chosenPathEndpointData_homotopy_unique_of_topology_package
      package M extinction hyx basepoint z
  · intro basepoint
    exact twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint
  · intro basepoint
    exact twoPointComplement_piOne_subsingleton_of_topology_package
      package M extinction hyx basepoint

/--
A package-selected two-puncture complement supplies a concrete based loop
payload: the selected loop has certified endpoints, is null-homotopic, and
represents the stationary element in the fundamental group.
-/
theorem twoPointComplement_chosenLoop_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ γ : Path basepoint basepoint,
      γ 0 = basepoint ∧ γ 1 = basepoint ∧
        Path.Homotopic γ (Path.refl basepoint) ∧
        FundamentalGroup.fromPath
            (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint) =
          FundamentalGroup.fromPath
            (⟦Path.refl basepoint⟧ :
              Path.Homotopic.Quotient basepoint basepoint) := by
  let γ : Path basepoint basepoint :=
    twoPointComplement_chosenPath_of_topology_package
      package M extinction hyx basepoint basepoint
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · exact twoPointComplement_chosenPath_source_of_topology_package
      package M extinction hyx basepoint basepoint
  · exact twoPointComplement_chosenPath_target_of_topology_package
      package M extinction hyx basepoint basepoint
  · exact twoPointComplement_chosenPath_homotopic_of_topology_package
      package M extinction hyx basepoint basepoint (Path.refl basepoint)
  · exact twoPointComplement_loop_fromPath_eq_refl_of_topology_package
      package M extinction hyx basepoint γ

/--
The package-level two-puncture complement can be consumed through the same
compact path/loop projection shape used by the transported recognition layer:
a canonical chosen path, endpoint equations, homotopy uniqueness for any
supplied path, quotient collapse, arbitrary-loop nullhomotopy, and trivial
first homotopy group.
-/
theorem twoPointComplement_chosen_path_loop_projection_bundle_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
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
      twoPointComplement_exists_path_with_endpoints_and_homotopy_unique_of_topology_package
        package M extinction hyx basepoint target with
    ⟨canonicalPath, canonicalSource, canonicalTarget, canonicalJoined,
      canonicalUnique⟩
  rcases
      twoPointComplement_paths_homotopic_payload_of_topology_package
        package M extinction hyx chosenPath canonicalPath with
    ⟨chosenHomotopic, chosenQuotientEq⟩
  have loopHomotopic :
      Path.Homotopic loop (Path.refl basepoint) :=
    twoPointComplement_loop_nullhomotopic_of_topology_package
      package M extinction hyx basepoint loop
  exact
    ⟨canonicalPath,
      twoPointComplement_nonempty_of_topology_package package M extinction hyx,
      twoPointComplement_pathComponent_eq_univ_of_topology_package
        package M extinction hyx basepoint,
      canonicalSource, canonicalTarget, canonicalJoined,
      chosenHomotopic, chosenQuotientEq, canonicalUnique,
      twoPointComplement_pathQuotient_subsingleton_of_topology_package
        package M extinction hyx basepoint target,
      Path.source loop, Path.target loop, loopHomotopic,
      twoPointComplement_loop_fromPath_eq_refl_of_topology_package
        package M extinction hyx basepoint loop,
      twoPointComplement_piOne_subsingleton_of_topology_package
        package M extinction hyx basepoint⟩

/-- Theorem contract for `twoPointComplement_chosen_path_loop_projection_bundle_of_topology_package`. -/
theorem twoPointComplement_chosen_path_loop_projection_bundle_of_topology_package_eq :
    @Poincare.twoPointComplement_chosen_path_loop_projection_bundle_of_topology_package =
      @Poincare.twoPointComplement_chosen_path_loop_projection_bundle_of_topology_package :=
  rfl

/--
A single topology-package endpoint bundles the path-homotopy payloads, chosen
path source equations, and chosen-loop payloads for both one- and two-puncture
complements.
-/
theorem singleton_and_twoPoint_path_loop_payloads_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    {a b : ({x}ᶜ : Set M)} (γ η : Path a b)
    (singleBase singleTarget : ({x}ᶜ : Set M))
    {c d : (({x} ∪ {y})ᶜ : Set M)} (γTwo ηTwo : Path c d)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M)) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ ∧
      compl_singleton_chosenPath_of_topology_package
        package M extinction x singleBase singleTarget 0 = singleBase ∧
      (∃ δ : Path singleBase singleBase,
        δ 0 = singleBase ∧ δ 1 = singleBase ∧
          Path.Homotopic δ (Path.refl singleBase) ∧
          FundamentalGroup.fromPath
              (⟦δ⟧ : Path.Homotopic.Quotient singleBase singleBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl singleBase⟧ :
                Path.Homotopic.Quotient singleBase singleBase)) ∧
      Path.Homotopic γTwo ηTwo ∧
      (⟦γTwo⟧ : Path.Homotopic.Quotient c d) = ⟦ηTwo⟧ ∧
      twoPointComplement_chosenPath_of_topology_package
        package M extinction hyx twoBase twoTarget 0 = twoBase ∧
      (∃ δ : Path twoBase twoBase,
        δ 0 = twoBase ∧ δ 1 = twoBase ∧
          Path.Homotopic δ (Path.refl twoBase) ∧
          FundamentalGroup.fromPath
              (⟦δ⟧ : Path.Homotopic.Quotient twoBase twoBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl twoBase⟧ :
                Path.Homotopic.Quotient twoBase twoBase)) := by
  rcases compl_singleton_paths_homotopic_payload_of_topology_package
      package M extinction x γ η with
    ⟨singleHomotopy, singleQuotient⟩
  have singleSource :
      compl_singleton_chosenPath_of_topology_package
        package M extinction x singleBase singleTarget 0 = singleBase :=
    compl_singleton_chosenPath_source_of_topology_package
      package M extinction x singleBase singleTarget
  rcases compl_singleton_chosenLoop_payload_of_topology_package
      package M extinction x singleBase with
    ⟨singleLoop, singleLoopSource, singleLoopTarget,
      singleLoopHomotopy, singleLoopFromPath⟩
  rcases twoPointComplement_paths_homotopic_payload_of_topology_package
      package M extinction hyx γTwo ηTwo with
    ⟨twoHomotopy, twoQuotient⟩
  have twoSource :
      twoPointComplement_chosenPath_of_topology_package
        package M extinction hyx twoBase twoTarget 0 = twoBase :=
    twoPointComplement_chosenPath_source_of_topology_package
      package M extinction hyx twoBase twoTarget
  rcases twoPointComplement_chosenLoop_payload_of_topology_package
      package M extinction hyx twoBase with
    ⟨twoLoop, twoLoopSource, twoLoopTarget,
      twoLoopHomotopy, twoLoopFromPath⟩
  refine
    ⟨singleHomotopy, singleQuotient, singleSource, ?_,
      twoHomotopy, twoQuotient, twoSource, ?_⟩
  · exact
      ⟨singleLoop, singleLoopSource, singleLoopTarget,
        singleLoopHomotopy, singleLoopFromPath⟩
  · exact
      ⟨twoLoop, twoLoopSource, twoLoopTarget,
        twoLoopHomotopy, twoLoopFromPath⟩

/--
The package-level two-puncture topology payload carries the transported
punctured-Euclidean chart together with package-selected path data, endpoint
data, a concrete path, endpoint equations, and the corresponding `Joined`
witness.
-/
theorem twoPointComplement_chosenPathTopologyPayload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
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
      (homeomorph_to_onePoint_threeSpace_of_topology_package
        package M extinction) hyx with
    ⟨puncture, chart, hAvoidsPuncture, hNonempty, hPath, hSimply⟩
  let pathData :
      PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) basepoint :=
    twoPointComplement_pointedPathComponentPathData_of_topology_package
      package M extinction hyx basepoint
  let endpointData :
      PointedChosenPathEndpointData
        (({x} ∪ {y})ᶜ : Set M) basepoint z :=
    twoPointComplement_chosenPathEndpointData_of_topology_package
      package M extinction hyx basepoint z
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
The package-level topology output can be consumed as one larger block: the
two-puncture transported chart and chosen-path topology payload, together with
the one- and two-puncture path-homotopy quotient and chosen-loop payloads.
-/
theorem topologyPackage_twoPointChartPath_and_pathLoopPayloads
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    {a b : ({x}ᶜ : Set M)} (γ η : Path a b)
    (singleBase singleTarget : ({x}ᶜ : Set M))
    {c d : (({x} ∪ {y})ᶜ : Set M)} (γTwo ηTwo : Path c d)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M)) :
    (∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) twoBase,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
            ∃ γPath : Path twoBase twoTarget,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                pathData.path_to twoTarget = γPath ∧
                endpointData.path = γPath ∧
                γPath 0 = twoBase ∧ γPath 1 = twoTarget ∧
                Joined twoBase twoTarget) ∧
      Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ ∧
      compl_singleton_chosenPath_of_topology_package
        package M extinction x singleBase singleTarget 0 = singleBase ∧
      (∃ δ : Path singleBase singleBase,
        δ 0 = singleBase ∧ δ 1 = singleBase ∧
          Path.Homotopic δ (Path.refl singleBase) ∧
          FundamentalGroup.fromPath
              (⟦δ⟧ : Path.Homotopic.Quotient singleBase singleBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl singleBase⟧ :
                Path.Homotopic.Quotient singleBase singleBase)) ∧
      Path.Homotopic γTwo ηTwo ∧
      (⟦γTwo⟧ : Path.Homotopic.Quotient c d) = ⟦ηTwo⟧ ∧
      twoPointComplement_chosenPath_of_topology_package
        package M extinction hyx twoBase twoTarget 0 = twoBase ∧
      (∃ δ : Path twoBase twoBase,
        δ 0 = twoBase ∧ δ 1 = twoBase ∧
          Path.Homotopic δ (Path.refl twoBase) ∧
          FundamentalGroup.fromPath
              (⟦δ⟧ : Path.Homotopic.Quotient twoBase twoBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl twoBase⟧ :
                Path.Homotopic.Quotient twoBase twoBase)) := by
  rcases twoPointComplement_chosenPathTopologyPayload_of_topology_package
      package M extinction hyx twoBase twoTarget with
    ⟨puncture, chart, pathData, endpointData, γPath,
      hAvoidsPuncture, hNonempty, hPathConnected, hSimplyConnected,
      hPathData, hEndpointPath, hSource, hTarget, hJoined⟩
  rcases singleton_and_twoPoint_path_loop_payloads_of_topology_package
      package M extinction hyx γ η singleBase singleTarget γTwo ηTwo
      twoBase twoTarget with
    ⟨singleHomotopy, singleQuotient, singleSource, singleLoopPayload,
      twoHomotopy, twoQuotient, twoSource, twoLoopPayload⟩
  exact
    ⟨⟨puncture, chart, pathData, endpointData, γPath,
        hAvoidsPuncture, hNonempty, hPathConnected, hSimplyConnected,
        hPathData, hEndpointPath, hSource, hTarget, hJoined⟩,
      singleHomotopy, singleQuotient, singleSource, singleLoopPayload,
      twoHomotopy, twoQuotient, twoSource, twoLoopPayload⟩

/--
The topology package can be consumed as a reusable final-topology block:
the final homeomorphism payload, one-point compactification recognition, the
two-puncture transported-chart payload, and the one- and two-puncture path-loop
payloads are all available from the same package inputs.
-/
theorem topologyPackage_finalHomeomorphism_and_pathLoopBundle
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    {a b : ({x}ᶜ : Set M)} (γ η : Path a b)
    (singleBase singleTarget : ({x}ᶜ : Set M))
    {c d : (({x} ∪ {y})ᶜ : Set M)} (γTwo ηTwo : Path c d)
    (twoBase twoTarget : (({x} ∪ {y})ᶜ : Set M)) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      FinalHomeomorphismPayloadData M extinction
        (extinction_decomposition_of_topology_package package M extinction) ∧
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        ∃ chart : (({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
          ∃ pathData :
              PointedPathComponentPathData (({x} ∪ {y})ᶜ : Set M) twoBase,
            ∃ endpointData :
                PointedChosenPathEndpointData
                  (({x} ∪ {y})ᶜ : Set M) twoBase twoTarget,
              ∃ γPath : Path twoBase twoTarget,
                (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                  Nonempty (({x} ∪ {y})ᶜ : Set M) ∧
                  PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  pathData.path_to twoTarget = γPath ∧
                  endpointData.path = γPath ∧
                  γPath 0 = twoBase ∧ γPath 1 = twoTarget ∧
                  Joined twoBase twoTarget) ∧
      Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b) = ⟦η⟧ ∧
      compl_singleton_chosenPath_of_topology_package
        package M extinction x singleBase singleTarget 0 = singleBase ∧
      (∃ δ : Path singleBase singleBase,
        δ 0 = singleBase ∧ δ 1 = singleBase ∧
          Path.Homotopic δ (Path.refl singleBase) ∧
          FundamentalGroup.fromPath
              (⟦δ⟧ : Path.Homotopic.Quotient singleBase singleBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl singleBase⟧ :
                Path.Homotopic.Quotient singleBase singleBase)) ∧
      Path.Homotopic γTwo ηTwo ∧
      (⟦γTwo⟧ : Path.Homotopic.Quotient c d) = ⟦ηTwo⟧ ∧
      twoPointComplement_chosenPath_of_topology_package
        package M extinction hyx twoBase twoTarget 0 = twoBase ∧
      (∃ δ : Path twoBase twoBase,
        δ 0 = twoBase ∧ δ 1 = twoBase ∧
          Path.Homotopic δ (Path.refl twoBase) ∧
          FundamentalGroup.fromPath
              (⟦δ⟧ : Path.Homotopic.Quotient twoBase twoBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl twoBase⟧ :
                Path.Homotopic.Quotient twoBase twoBase)) := by
  have hOnePoint :
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction
  have hFinal :
      FinalHomeomorphismPayloadData M extinction
        (extinction_decomposition_of_topology_package package M extinction) :=
    finalHomeomorphismPayloadData_of_topology_package package M extinction
  rcases topologyPackage_twoPointChartPath_and_pathLoopPayloads
      package M extinction hyx γ η singleBase singleTarget γTwo ηTwo
      twoBase twoTarget with
    ⟨twoPointPayload, singleHomotopy, singleQuotient, singleSource,
      singleLoopPayload, twoHomotopy, twoQuotient, twoSource,
      twoLoopPayload⟩
  exact
    ⟨hOnePoint, hFinal, twoPointPayload, singleHomotopy, singleQuotient,
      singleSource, singleLoopPayload, twoHomotopy, twoQuotient, twoSource,
      twoLoopPayload⟩

/--
The final-homeomorphism package route also exposes the compact two-puncture
path/loop projection bundle from the same package inputs. This gives final
certificate consumers a small endpoint that combines the recognized one-point
compactification with the path, quotient, loop, and first-homotopy-group
collapse of the two-puncture complement.
-/
theorem topologyPackage_finalHomeomorphism_and_twoPointProjectionBundle
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint target : (({x} ∪ {y})ᶜ : Set M))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      FinalHomeomorphismPayloadData M extinction
        (extinction_decomposition_of_topology_package package M extinction) ∧
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
  exact
    ⟨homeomorph_to_onePoint_threeSpace_of_topology_package
        package M extinction,
      finalHomeomorphismPayloadData_of_topology_package package M extinction,
      twoPointComplement_chosen_path_loop_projection_bundle_of_topology_package
        package M extinction hyx basepoint target chosenPath loop⟩

/-- Theorem contract for `topologyPackage_finalHomeomorphism_and_twoPointProjectionBundle`. -/
theorem topologyPackage_finalHomeomorphism_and_twoPointProjectionBundle_eq :
    @Poincare.topologyPackage_finalHomeomorphism_and_twoPointProjectionBundle =
      @Poincare.topologyPackage_finalHomeomorphism_and_twoPointProjectionBundle :=
  rfl

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

/-- A topology extraction package supplies the decomposition-data statement. -/
theorem extinctionTopologyDecompositionDataStatement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExtinctionTopologyDecompositionDataStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction
  exact (extinction_decomposition_of_topology_package package M extinction).data

/-- A topology extraction package exposes certified decomposition data for each extinction witness. -/
theorem extinction_topology_decomposition_data_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (ExtinctionTopologyDecompositionData M extinction) :=
  (extinction_decomposition_of_topology_package package M extinction).data

/-- A topology extraction package exposes certified surgery-trace reconstruction data. -/
theorem extinction_surgery_trace_reconstruction_data_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty
      (ExtinctionSurgeryTraceReconstructionData M extinction
        (extinction_decomposition_of_topology_package package M extinction)) :=
  (extinction_surgery_trace_reconstruction_of_topology_package
    package M extinction).data

/--
A topology extraction package gives a single certificate for the selected
decomposition field: it carries decomposition data, surgery-trace
reconstruction, final-homeomorphism payload data, the raw `ThreeSphere`
homeomorphism, and the induced one-point compactification recognition.
-/
theorem topologyPackage_selected_decomposition_trace_finalHomeomorphism_and_recognition_certificate
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      Nonempty (ExtinctionTopologyDecompositionData M extinction) ∧
        HasExtinctionSurgeryTraceReconstruction M extinction decomposition ∧
        Nonempty
          (ExtinctionSurgeryTraceReconstructionData M extinction decomposition) ∧
        FinalHomeomorphismPayloadData M extinction decomposition ∧
        Nonempty (M ≃ₜ ThreeSphere) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  let decomposition :
      HasExtinctionTopologyDecomposition M extinction :=
    extinction_decomposition_of_topology_package package M extinction
  have hDecompositionData :
      Nonempty (ExtinctionTopologyDecompositionData M extinction) :=
    extinction_topology_decomposition_data_of_topology_package
      package M extinction
  have hTrace :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition := by
    change HasExtinctionSurgeryTraceReconstruction M extinction
      (extinction_decomposition_of_topology_package package M extinction)
    exact extinction_surgery_trace_reconstruction_of_topology_package
      package M extinction
  have hTraceData :
      Nonempty
        (ExtinctionSurgeryTraceReconstructionData M extinction decomposition) := by
    change Nonempty
      (ExtinctionSurgeryTraceReconstructionData M extinction
        (extinction_decomposition_of_topology_package package M extinction))
    exact extinction_surgery_trace_reconstruction_data_of_topology_package
      package M extinction
  have hFinalPayload :
      FinalHomeomorphismPayloadData M extinction decomposition := by
    change FinalHomeomorphismPayloadData M extinction
      (extinction_decomposition_of_topology_package package M extinction)
    exact finalHomeomorphismPayloadData_of_topology_package
      package M extinction
  have hThreeSphere : Nonempty (M ≃ₜ ThreeSphere) :=
    homeomorphism_of_topology_package package M extinction
  have hOnePoint :
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction
  exact
    ⟨decomposition, hDecompositionData, hTrace, hTraceData, hFinalPayload,
      hThreeSphere, hOnePoint⟩

/-- Theorem contract for `topologyPackage_selected_decomposition_trace_finalHomeomorphism_and_recognition_certificate`. -/
theorem topologyPackage_selected_decomposition_trace_finalHomeomorphism_and_recognition_certificate_eq :
    @Poincare.topologyPackage_selected_decomposition_trace_finalHomeomorphism_and_recognition_certificate =
      @Poincare.topologyPackage_selected_decomposition_trace_finalHomeomorphism_and_recognition_certificate :=
  rfl

/-- Theorem contract for `extinction_topology_decomposition_data_of_topology_package`. -/
theorem extinction_topology_decomposition_data_of_topology_package_eq :
    @Poincare.extinction_topology_decomposition_data_of_topology_package =
      @Poincare.extinction_topology_decomposition_data_of_topology_package :=
  rfl

/-- Theorem contract for `extinction_surgery_trace_reconstruction_data_of_topology_package`. -/
theorem extinction_surgery_trace_reconstruction_data_of_topology_package_eq :
    @Poincare.extinction_surgery_trace_reconstruction_data_of_topology_package =
      @Poincare.extinction_surgery_trace_reconstruction_data_of_topology_package :=
  rfl

end Poincare
