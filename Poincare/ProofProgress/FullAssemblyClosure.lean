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

end Poincare
