/-
Proof-progress boundary for the final assembly route.

This module does not define the reserved final theorem.  It records the three
remaining package inputs that are sufficient for the current `FullAssembly`
payload, after the analytic and surgery/Perelman package-layer requirements are
projected from the stronger finite-extinction package boundary.
-/

import Poincare.CompletionTarget
import Poincare.ProofProgress.AnalyticLeviCivitaBlocker
import Poincare.ProofProgress.FiniteExtinctionPackage
import Poincare.ProofProgress.FiniteExtinctionSweepoutBoundary
import Poincare.ProofProgress.SurgeryPerelmanPackageLayer
import Poincare.ProofProgress.TopologyPackageFields

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The three package-level inputs that remain after the current proof-progress
bridges project analytic-foundation and surgery/Perelman package requirements
from the finite-extinction package.
-/
structure FinalAssemblyPackageBoundaryInputs where
  /-- Moise/smoothability package for target topological 3-manifolds. -/
  smoothability :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage
  /-- Finite-extinction surgery package family for all smooth target manifolds. -/
  finiteExtinction :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage
  /-- Post-extinction topology extraction package. -/
  topology :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.topologyPackage

/--
The current three-input assembly boundary is exactly the aggregate dependency
package consumed by the existing completion routes.
-/
def poincareProofDependencies_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    PoincareProofDependencies.{u} where
  smoothability := inputs.smoothability
  surgery := inputs.finiteExtinction
  topology := inputs.topology

/-- The smoothability package-layer requirement is one of the three inputs. -/
theorem smoothabilityPackage_requirement_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage :=
  inputs.smoothability

/--
The analytic package-layer requirement is not an additional final assembly
input: it projects from the finite-extinction package boundary.
-/
theorem analyticFoundationPackage_requirement_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.analyticFoundationPackage :=
  (dependencyPackageLayerRequirement_of_componentRequirement
    DependencyPackageLayer.analyticFoundationPackage) inputs.finiteExtinction

/--
The surgery/Perelman package-layer requirement is also projected from the
finite-extinction package boundary.
-/
theorem surgeryPackage_requirement_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.surgeryPackage :=
  surgeryPackage_requirement_of_finiteExtinctionPackage_requirement
    inputs.finiteExtinction

/-- The finite-extinction package-layer requirement is one of the three inputs. -/
theorem finiteExtinctionPackage_requirement_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage :=
  inputs.finiteExtinction

/-- The topology package-layer requirement is one of the three inputs. -/
theorem topologyPackage_requirement_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.topologyPackage :=
  inputs.topology

/--
The final package boundary exposes the topology-extraction endpoint as an
explicit homeomorphism to the project `ThreeSphere`.
-/
theorem homeomorph_to_threeSphere_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ThreeSphere) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  exact homeomorphism_of_topology_package
    inputs.topology M (finiteExtinction M)

/--
The final package boundary exposes the post-extinction recognition
homeomorphism to the one-point compactification model.
-/
theorem homeomorph_to_onePoint_threeSpace_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  exact
    homeomorph_to_onePoint_threeSpace_of_topology_package
      inputs.topology M (finiteExtinction M)

/--
The final package boundary transports every single-puncture complement to the
Euclidean chart of the one-point compactification model.
-/
theorem homeomorph_compl_singleton_euclidean_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) :
    Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) :=
  ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_finalAssemblyPackageBoundaryInputs
      inputs M) x⟩

/--
The final package boundary transports every two-puncture complement to a
punctured Euclidean chart.
-/
theorem exists_homeomorph_twoPointComplement_puncturedEuclidean_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) :=
  exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_finalAssemblyPackageBoundaryInputs
      inputs M) hyx

/--
The final package boundary exposes the stronger singleton-complement
contractibility structure supplied by topology extraction.
-/
theorem compl_singleton_contractibleSpace_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  exact
    compl_singleton_contractibleSpace_of_topology_package
      inputs.topology M (finiteExtinction M) x

/--
The same final package boundary gives simple connectedness for both singleton
and two-point complements.
-/
theorem complement_simplyConnectedSpace_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  exact
    ⟨ compl_singleton_simplyConnectedSpace_of_topology_package
        inputs.topology M (finiteExtinction M) x
    , twoPointComplement_simplyConnectedSpace_of_topology_package
        inputs.topology M (finiteExtinction M) hyx
    ⟩

/--
The final package boundary now exposes the single-puncture first-homotopy
collapse that the topology package proves from finite extinction.
-/
theorem compl_singleton_piOne_subsingleton_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  exact
    compl_singleton_piOne_subsingleton_of_topology_package
      inputs.topology M (finiteExtinction M) x basepoint

/--
The final package boundary also exposes the two-puncture first-homotopy
collapse used by recognition routes after puncture transport.
-/
theorem twoPointComplement_piOne_subsingleton_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton
      (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  exact
    twoPointComplement_piOne_subsingleton_of_topology_package
      inputs.topology M (finiteExtinction M) hyx basepoint

/--
Combined complement-collapse payload at the final assembly boundary: once the
three package inputs are supplied, both the single-puncture and two-puncture
first homotopy groups are trivial at arbitrary basepoints.
-/
theorem complement_piOne_collapse_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) := by
  exact
    ⟨ compl_singleton_piOne_subsingleton_of_finalAssemblyPackageBoundaryInputs
        inputs M x singleBasepoint
    , twoPointComplement_piOne_subsingleton_of_finalAssemblyPackageBoundaryInputs
        inputs M hyx twoBasepoint
    ⟩

/--
Stronger final-boundary complement-collapse payload: the same three package
inputs give path-connectedness, zeroth-homotopy collapse, and first-homotopy
collapse for both single-puncture and two-puncture complements.
-/
theorem complement_path_and_homotopy_collapse_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    PathConnectedSpace ({x}ᶜ : Set M) ∧
      Subsingleton
        (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
      PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      Subsingleton
        (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  let singlePathConnected :
      PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      inputs.topology M (finiteExtinction M) x
  let twoPointPathConnected :
      PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      inputs.topology M (finiteExtinction M) hyx
  have singlePiZero :
      Subsingleton
        (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) := by
    letI : PathConnectedSpace ({x}ᶜ : Set M) := singlePathConnected
    exact
      ((HomotopyGroup.pi0EquivZerothHomotopy
        (X := ({x}ᶜ : Set M))
        (x := singleBasepoint)).subsingleton_congr).mpr
          (inferInstance : Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)))
  have twoPointPiZero :
      Subsingleton
        (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) := by
    letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
      twoPointPathConnected
    exact
      ((HomotopyGroup.pi0EquivZerothHomotopy
        (X := (({x} ∪ {y})ᶜ : Set M))
        (x := twoBasepoint)).subsingleton_congr).mpr
          (inferInstance :
            Subsingleton (ZerothHomotopy (({x} ∪ {y})ᶜ : Set M)))
  exact
    ⟨ singlePathConnected
    , singlePiZero
    , compl_singleton_piOne_subsingleton_of_topology_package
        inputs.topology M (finiteExtinction M) x singleBasepoint
    , twoPointPathConnected
    , twoPointPiZero
    , twoPointComplement_piOne_subsingleton_of_topology_package
        inputs.topology M (finiteExtinction M) hyx twoBasepoint
    ⟩

/--
Path-level final-boundary complement payload: the package inputs give explicit
joined paths and path-component collapse for both single-puncture and
two-puncture complements.
-/
theorem complement_path_component_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x) :
    (∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
      (∀ basepoint : ({x}ᶜ : Set M),
        pathComponent basepoint = Set.univ) ∧
      (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
      (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
        pathComponent basepoint = Set.univ) := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  let singlePathConnected :
      PathConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_pathConnectedSpace_of_topology_package
      inputs.topology M (finiteExtinction M) x
  let twoPointPathConnected :
      PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
    twoPointComplement_pathConnectedSpace_of_topology_package
      inputs.topology M (finiteExtinction M) hyx
  constructor
  · intro a b
    letI : PathConnectedSpace ({x}ᶜ : Set M) := singlePathConnected
    exact PathConnectedSpace.joined a b
  constructor
  · intro basepoint
    letI : PathConnectedSpace ({x}ᶜ : Set M) := singlePathConnected
    ext z
    constructor
    · intro _hz
      exact Set.mem_univ z
    · intro _hz
      exact PathConnectedSpace.joined basepoint z
  constructor
  · intro a b
    letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
      twoPointPathConnected
    exact PathConnectedSpace.joined a b
  · intro basepoint
    letI : PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
      twoPointPathConnected
    ext z
    constructor
    · intro _hz
      exact Set.mem_univ z
    · intro _hz
      exact PathConnectedSpace.joined basepoint z

/--
The three-input boundary supplies all five package-layer requirements in the
crosswalk order; the analytic and surgery/Perelman entries are projections from
the finite-extinction package entry.
-/
theorem package_layer_requirements_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    ∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  exact
    ⟨ smoothabilityPackage_requirement_of_finalAssemblyPackageBoundaryInputs
        inputs
    , analyticFoundationPackage_requirement_of_finalAssemblyPackageBoundaryInputs
        inputs
    , surgeryPackage_requirement_of_finalAssemblyPackageBoundaryInputs inputs
    , finiteExtinctionPackage_requirement_of_finalAssemblyPackageBoundaryInputs
        inputs
    , topologyPackage_requirement_of_finalAssemblyPackageBoundaryInputs inputs
    ⟩

/-- The three-input boundary supplies the aggregate component payload. -/
theorem component_requirements_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    ∃ _smoothability :
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.topologyComponent := by
  exact
    dependency_component_requirements_payload_of_dependencies
      (poincareProofDependencies_of_finalAssemblyPackageBoundaryInputs inputs)

/--
The three-input boundary proves the existing full assembly payload in
`FullAssembly`.
-/
theorem poincare_full_assembly_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    ∃ _smoothabilityPackage : SmoothabilityPackage.{u},
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
    ∃ _topologyPackage : ExtinctionTopologyExtractionPackage.{u},
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
      PoincareConjectureStatement.{u} := by
  exact
    poincare_full_assembly_payload_of_surgery_and_topology_packages
      inputs.smoothability inputs.finiteExtinction inputs.topology

/-- The same three inputs expose the current project completion payload. -/
theorem poincare_completion_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_surgery_and_topology_packages
    inputs.smoothability inputs.finiteExtinction inputs.topology

/-- The same three inputs expose the canonical completion payload. -/
theorem canonical_completion_payload_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_poincareProofDependencies_component_requirements
    (poincareProofDependencies_of_finalAssemblyPackageBoundaryInputs inputs)

/--
The current final assembly boundary closes conditionally on exactly the three
package inputs above.
-/
theorem canonical_completion_target_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_poincareProofDependencies_component_requirements
    (poincareProofDependencies_of_finalAssemblyPackageBoundaryInputs inputs)

/--
The lower-level finite-extinction sub-obligation family identified in the
proof-progress modules is a sufficient replacement for the
finite-extinction-package field of `FinalAssemblyPackageBoundaryInputs`.
-/
def FinalAssemblyFiniteExtinctionSubobligationFamily : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M],
      ∃ n : ℕ∞ω,
      ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
      ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
        FiniteExtinctionSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control

/--
Alternative boundary phrasing using the current finite-extinction proof-progress
bridge: smoothability, the finite-extinction sub-obligation family, and topology
extraction are sufficient to recover the three package inputs.
-/
structure FinalAssemblySubobligationBoundaryInputs where
  /-- Moise/smoothability package for target topological 3-manifolds. -/
  smoothability :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage
  /-- Analytic/surgery/Perelman/sub-obligation family for finite extinction. -/
  finiteExtinctionSubobligations :
    FinalAssemblyFiniteExtinctionSubobligationFamily.{u}
  /-- Post-extinction topology extraction package. -/
  topology :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.topologyPackage

/-- Convert the sub-obligation boundary to the three package boundary. -/
def finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    FinalAssemblyPackageBoundaryInputs.{u} where
  smoothability := inputs.smoothability
  finiteExtinction :=
    finiteExtinctionPackage_requirement_of_subobligations_family
      inputs.finiteExtinctionSubobligations
  topology := inputs.topology

/--
The sub-obligation boundary proves the existing full assembly payload after the
finite-extinction proof-progress bridge builds the package-layer requirement.
-/
theorem poincare_full_assembly_payload_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ _smoothabilityPackage : SmoothabilityPackage.{u},
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
    ∃ _topologyPackage : ExtinctionTopologyExtractionPackage.{u},
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
      PoincareConjectureStatement.{u} :=
  poincare_full_assembly_payload_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)

/-- The sub-obligation boundary also exposes the canonical completion payload. -/
theorem canonical_completion_payload_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)

/--
The sub-obligation boundary inherits the explicit `ThreeSphere` recognition
endpoint through the package-boundary conversion.
-/
theorem homeomorph_to_threeSphere_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ThreeSphere) :=
  homeomorph_to_threeSphere_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M

/--
The sub-obligation boundary inherits one-point compactification recognition
after the finite-extinction proof-progress bridge constructs the package input.
-/
theorem homeomorph_to_onePoint_threeSpace_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  homeomorph_to_onePoint_threeSpace_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M

/--
The sub-obligation boundary inherits the concrete Euclidean chart
homeomorphism for single-puncture complements.
-/
theorem homeomorph_compl_singleton_euclidean_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) :
    Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) :=
  homeomorph_compl_singleton_euclidean_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M x

/--
The sub-obligation boundary inherits the concrete punctured-Euclidean chart
homeomorphism for two-puncture complements.
-/
theorem exists_homeomorph_twoPointComplement_puncturedEuclidean_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {x y : M} (hyx : y ≠ x) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) :=
  exists_homeomorph_twoPointComplement_puncturedEuclidean_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M hyx

/--
The sub-obligation boundary inherits singleton-complement contractibility
through the package-boundary conversion.
-/
theorem compl_singleton_contractibleSpace_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) :=
  compl_singleton_contractibleSpace_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M x

/--
The sub-obligation boundary inherits simple connectedness for both singleton
and two-point complements.
-/
theorem complement_simplyConnectedSpace_payload_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  complement_simplyConnectedSpace_payload_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M x hyx

/--
The sub-obligation boundary inherits the single-puncture first-homotopy
collapse after the finite-extinction proof-progress bridge constructs the
package-level finite-extinction input.
-/
theorem compl_singleton_piOne_subsingleton_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
  compl_singleton_piOne_subsingleton_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M x basepoint

/--
The sub-obligation boundary also inherits the two-puncture first-homotopy
collapse through the same package-boundary conversion.
-/
theorem twoPointComplement_piOne_subsingleton_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton
      (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  twoPointComplement_piOne_subsingleton_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M hyx basepoint

/--
Combined complement-collapse payload for the sub-obligation boundary.
-/
theorem complement_piOne_collapse_payload_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) :=
  complement_piOne_collapse_payload_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M x hyx singleBasepoint twoBasepoint

/--
The sub-obligation boundary inherits the stronger path, `Pi 0`, and `Pi 1`
complement-collapse payload through the package-boundary conversion.
-/
theorem complement_path_and_homotopy_collapse_payload_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x)
    (singleBasepoint : ({x}ᶜ : Set M))
    (twoBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    PathConnectedSpace ({x}ᶜ : Set M) ∧
      Subsingleton
        (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) singleBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) singleBasepoint) ∧
      PathConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      Subsingleton
        (HomotopyGroup.Pi 0 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({x} ∪ {y})ᶜ : Set M) twoBasepoint) :=
  complement_path_and_homotopy_collapse_payload_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M x hyx singleBasepoint twoBasepoint

/--
The sub-obligation boundary inherits the explicit joined-path and
path-component-collapse payload through the package-boundary conversion.
-/
theorem complement_path_component_payload_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (x : M) {y : M} (hyx : y ≠ x) :
    (∀ a b : ({x}ᶜ : Set M), Nonempty (Path a b)) ∧
      (∀ basepoint : ({x}ᶜ : Set M),
        pathComponent basepoint = Set.univ) ∧
      (∀ a b : (({x} ∪ {y})ᶜ : Set M), Nonempty (Path a b)) ∧
      (∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
        pathComponent basepoint = Set.univ) :=
  complement_path_component_payload_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs)
    M x hyx

end Poincare
