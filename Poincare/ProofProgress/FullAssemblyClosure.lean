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
import Poincare.ProofProgress.GroundedFiniteExtinctionCertificate
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
The finite-extinction sub-obligation family supplies a theorem-shaped
finite-extinction statement for each smooth target manifold.
-/
theorem finite_extinction_statement_of_finalAssemblyFiniteExtinctionSubobligationFamily
    (h : FinalAssemblyFiniteExtinctionSubobligationFamily.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω, FiniteExtinctionStatement n M := by
  rcases h M with
    ⟨n, _analyticFoundation, _surgeryConstruction, _perelmanControl,
      subobligations⟩
  exact
    ⟨n, finite_extinction_statement_of_subobligations_statement
      subobligations⟩

/-- Theorem contract for `finite_extinction_statement_of_finalAssemblyFiniteExtinctionSubobligationFamily`. -/
theorem finite_extinction_statement_of_finalAssemblyFiniteExtinctionSubobligationFamily_eq :
    @Poincare.finite_extinction_statement_of_finalAssemblyFiniteExtinctionSubobligationFamily =
      @Poincare.finite_extinction_statement_of_finalAssemblyFiniteExtinctionSubobligationFamily :=
  rfl

/--
The finite-extinction sub-obligation family supplies the actual extinction
witness used by the topology-extraction side of the proof.
-/
theorem finite_extinction_of_finalAssemblyFiniteExtinctionSubobligationFamily
    (h : FinalAssemblyFiniteExtinctionSubobligationFamily.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases h M with
    ⟨_n, _analyticFoundation, _surgeryConstruction, _perelmanControl,
      subobligations⟩
  exact finite_extinction_of_subobligations_statement subobligations

/-- Theorem contract for `finite_extinction_of_finalAssemblyFiniteExtinctionSubobligationFamily`. -/
theorem finite_extinction_of_finalAssemblyFiniteExtinctionSubobligationFamily_eq :
    @Poincare.finite_extinction_of_finalAssemblyFiniteExtinctionSubobligationFamily =
      @Poincare.finite_extinction_of_finalAssemblyFiniteExtinctionSubobligationFamily :=
  rfl

/--
Combined finite-extinction payload extracted from the sub-obligation family:
the chosen time parameter, the theorem-shaped finite-extinction statement, and
the projected extinction witness are all recovered from the same subobligation
data.
-/
theorem finite_extinction_statement_payload_of_finalAssemblyFiniteExtinctionSubobligationFamily
    (h : FinalAssemblyFiniteExtinctionSubobligationFamily.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω,
    ∃ _statement : FiniteExtinctionStatement n M,
      FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases h M with
    ⟨n, _analyticFoundation, _surgeryConstruction, _perelmanControl,
      subobligations⟩
  exact
    ⟨n, finite_extinction_statement_of_subobligations_statement
      subobligations,
      finite_extinction_of_subobligations_statement subobligations⟩

/-- Theorem contract for `finite_extinction_statement_payload_of_finalAssemblyFiniteExtinctionSubobligationFamily`. -/
theorem finite_extinction_statement_payload_of_finalAssemblyFiniteExtinctionSubobligationFamily_eq :
    @Poincare.finite_extinction_statement_payload_of_finalAssemblyFiniteExtinctionSubobligationFamily =
      @Poincare.finite_extinction_statement_payload_of_finalAssemblyFiniteExtinctionSubobligationFamily :=
  rfl

/--
A uniform family of grounded finite-extinction production certificates supplies
the final-assembly finite-extinction subobligation family. For each smooth
target manifold, the grounded certificate first builds a finite-extinction
surgery package; the package then exposes its analytic foundation, surgery
construction, Perelman control package, and full subobligation statement with
matching flow.
-/
theorem finalAssemblyFiniteExtinctionSubobligationFamily_of_grounded_certificates
    (h :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          GroundedFiniteExtinctionProductionCertificate M) :
    FinalAssemblyFiniteExtinctionSubobligationFamily.{u} := by
  intro M _top _t2 _charted _simple _compact _smooth
  rcases finite_extinction_surgery_package_nonempty_of_grounded_certificate
      (h M) with
    ⟨packageSigma⟩
  rcases packageSigma with ⟨n, package⟩
  refine
    ⟨n, analytic_foundation_of_surgery_package package,
      surgery_construction_package_of_surgery_package package,
      perelman_control_package_of_surgery_package package, ?_⟩
  simpa [ricci_flow_data_of_surgery_package,
    ricci_flow_with_surgery_of_surgery_package,
    perelman_singularity_control_of_surgery_package] using
    finite_extinction_subobligations_statement_of_surgery_package package

/-- Theorem contract for `finalAssemblyFiniteExtinctionSubobligationFamily_of_grounded_certificates`. -/
theorem finalAssemblyFiniteExtinctionSubobligationFamily_of_grounded_certificates_eq :
    @Poincare.finalAssemblyFiniteExtinctionSubobligationFamily_of_grounded_certificates =
      @Poincare.finalAssemblyFiniteExtinctionSubobligationFamily_of_grounded_certificates :=
  rfl

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
The sub-obligation boundary simultaneously supplies the package-layer payload,
the aggregate component payload, the full assembly payload, both completion
payloads, and the canonical target, all routed through the same derived
three-package boundary input.
-/
theorem final_assembly_certificate_bundle_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ _packagePayload :
      (∃ _smoothability :
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
          DependencyPackageLayer.topologyPackage),
    ∃ _componentPayload :
      (∃ _smoothability :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.topologyComponent),
    ∃ _fullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _completionPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _canonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
      canonicalCompletionTarget.{u} := by
  let packageInputs :=
    finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs
  exact
    ⟨ package_layer_requirements_payload_of_finalAssemblyPackageBoundaryInputs
        packageInputs
    , component_requirements_payload_of_finalAssemblyPackageBoundaryInputs
        packageInputs
    , poincare_full_assembly_payload_of_finalAssemblyPackageBoundaryInputs
        packageInputs
    , poincare_completion_payload_of_finalAssemblyPackageBoundaryInputs
        packageInputs
    , canonical_completion_payload_of_finalAssemblyPackageBoundaryInputs
        packageInputs
    , canonical_completion_target_of_finalAssemblyPackageBoundaryInputs
        packageInputs
    ⟩

/--
The sub-obligation boundary also exposes the derived package boundary input
together with both sub-obligation-level and package-level result payloads.  This
packages the existing final assembly certificate with the concrete boundary
conversion route used to obtain the three package inputs.
-/
theorem final_assembly_package_boundary_result_bundle_of_finalAssemblySubobligationBoundaryInputs
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ packageInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ _packagePayload :
      (∃ _smoothability :
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
          DependencyPackageLayer.topologyPackage),
    ∃ _componentPayload :
      (∃ _smoothability :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.topologyComponent),
    ∃ _subobligationFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _packageFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _completionPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _subobligationCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _packageCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _canonicalTarget : canonicalCompletionTarget.{u},
      packageInputs =
        finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
          inputs := by
  let packageInputs :=
    finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs
  rcases
    final_assembly_certificate_bundle_of_finalAssemblySubobligationBoundaryInputs
      inputs with
    ⟨ packagePayload
    , componentPayload
    , packageFullAssemblyPayload
    , completionPayload
    , packageCanonicalPayload
    , canonicalTarget ⟩
  exact
    ⟨ packageInputs
    , packagePayload
    , componentPayload
    , poincare_full_assembly_payload_of_finalAssemblySubobligationBoundaryInputs
        inputs
    , packageFullAssemblyPayload
    , completionPayload
    , canonical_completion_payload_of_finalAssemblySubobligationBoundaryInputs
        inputs
    , packageCanonicalPayload
    , canonicalTarget
    , rfl
    ⟩

/--
**Step 3694 source.** The sub-obligation boundary now yields the derived
package boundary together with the full-assembly statement and both completion
payloads on that same boundary.

Reference source: this proof fixes
`finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs`,
uses `poincare_full_assembly_payload_of_finalAssemblyPackageBoundaryInputs` to
extract the actual `PoincareConjectureStatement`, and combines it with
`poincare_completion_payload_of_finalAssemblyPackageBoundaryInputs`,
`canonical_completion_payload_of_finalAssemblyPackageBoundaryInputs`, and
`canonical_completion_target_of_finalAssemblyPackageBoundaryInputs`.  This
fills the final-assembly bridge with the project statement and completion
payloads instead of merely naming the conversion route.
-/
theorem final_assembly_subobligation_boundary_statement_and_completion_payload_bundle
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ packageInputs : FinalAssemblyPackageBoundaryInputs.{u},
      packageInputs =
        finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
          inputs ∧
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}) ∧
      PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} := by
  let packageInputs :=
    finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs inputs
  have fullPayload :
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
      packageInputs
  rcases fullPayload with
    ⟨smoothabilityPackage, surgeryPackages, topologyPackage,
      finiteExtinction, extractSphere, projectStatement⟩
  exact
    ⟨packageInputs, rfl,
      ⟨smoothabilityPackage, surgeryPackages, topologyPackage,
        finiteExtinction, extractSphere, projectStatement⟩,
      projectStatement,
      poincare_completion_payload_of_finalAssemblyPackageBoundaryInputs
        packageInputs,
      canonical_completion_payload_of_finalAssemblyPackageBoundaryInputs
        packageInputs,
      canonical_completion_target_of_finalAssemblyPackageBoundaryInputs
        packageInputs⟩

/--
**Step 3700 source.** The sub-obligation boundary now carries a full
certificate bundle combining the package-boundary payloads with the extracted
Poincare statement and completion targets.

Reference source: this proof destructs
`final_assembly_package_boundary_result_bundle_of_finalAssemblySubobligationBoundaryInputs`
to obtain the derived package inputs, package-layer requirements, component
requirements, sub-obligation and package full-assembly payloads, completion
payloads, canonical payloads, canonical target, and boundary-conversion
equality.  It then independently destructs
`final_assembly_subobligation_boundary_statement_and_completion_payload_bundle`
to add the project-level `PoincareConjectureStatement` extracted from the same
boundary.  This is a proof-bearing consolidation of two compiled final-assembly
endpoints rather than a route alias.
-/
theorem final_assembly_subobligation_boundary_full_certificate_and_statement_bundle
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ packageInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ _packagePayload :
      (∃ _smoothability :
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
          DependencyPackageLayer.topologyPackage),
    ∃ _componentPayload :
      (∃ _smoothability :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.topologyComponent),
    ∃ _subobligationFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _packageFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _projectStatement : PoincareConjectureStatement.{u},
    ∃ _completionPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _subobligationCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _packageCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _canonicalTarget : canonicalCompletionTarget.{u},
      packageInputs =
        finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
          inputs := by
  rcases
    final_assembly_package_boundary_result_bundle_of_finalAssemblySubobligationBoundaryInputs
      inputs with
    ⟨ packageInputs
    , packagePayload
    , componentPayload
    , subobligationFullAssemblyPayload
    , packageFullAssemblyPayload
    , completionPayload
    , subobligationCanonicalPayload
    , packageCanonicalPayload
    , canonicalTarget
    , hpackageInputs ⟩
  rcases
    final_assembly_subobligation_boundary_statement_and_completion_payload_bundle
      inputs with
    ⟨ _statementPackageInputs
    , _hstatementPackageInputs
    , _statementFullAssemblyPayload
    , projectStatement
    , _statementCompletionPayload
    , _statementCanonicalPayload
    , _statementCanonicalTarget ⟩
  exact
    ⟨ packageInputs
    , packagePayload
    , componentPayload
    , subobligationFullAssemblyPayload
    , packageFullAssemblyPayload
    , projectStatement
    , completionPayload
    , subobligationCanonicalPayload
    , packageCanonicalPayload
    , canonicalTarget
    , hpackageInputs
    ⟩

/--
The full sub-obligation certificate still remembers the raw
analytic/surgery/Perelman finite-extinction witness family.  Destructing the
assembled certificate and its package-layer payload exposes both the derived
finite-extinction package requirement and the uncompressed sub-obligation family
alongside the final assembly and completion targets.
-/
theorem final_assembly_subobligation_boundary_witness_family_completion_certificate_bundle
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ packageInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ _rawSubobligations :
      FinalAssemblyFiniteExtinctionSubobligationFamily.{u},
    ∃ _finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
    ∃ _subobligationFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _packageFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _projectStatement : PoincareConjectureStatement.{u},
    ∃ _completionPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _subobligationCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _packageCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _canonicalTarget : canonicalCompletionTarget.{u},
      packageInputs =
        finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
          inputs := by
  rcases
    final_assembly_subobligation_boundary_full_certificate_and_statement_bundle
      inputs with
    ⟨ packageInputs
    , packagePayload
    , _componentPayload
    , subobligationFullAssemblyPayload
    , packageFullAssemblyPayload
    , projectStatement
    , completionPayload
    , subobligationCanonicalPayload
    , packageCanonicalPayload
    , canonicalTarget
    , hpackageInputs ⟩
  rcases packagePayload with
    ⟨ _smoothabilityRequirement
    , _analyticRequirement
    , _surgeryRequirement
    , finiteExtinctionRequirement
    , _topologyRequirement ⟩
  exact
    ⟨ packageInputs
    , inputs.finiteExtinctionSubobligations
    , finiteExtinctionRequirement
    , subobligationFullAssemblyPayload
    , packageFullAssemblyPayload
    , projectStatement
    , completionPayload
    , subobligationCanonicalPayload
    , packageCanonicalPayload
    , canonicalTarget
    , hpackageInputs
    ⟩

/--
The same sub-obligation boundary certificate also carries the component-level
requirements.  This bundles the raw finite-extinction witness family with the
finite-extinction package requirement and the smoothability/surgery/topology
component requirements used by the final assembly route.
-/
theorem final_assembly_subobligation_boundary_component_witness_family_completion_certificate_bundle
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u}) :
    ∃ packageInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ _rawSubobligations :
      FinalAssemblyFiniteExtinctionSubobligationFamily.{u},
    ∃ _finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
    ∃ _componentPayload :
      (∃ _smoothability :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.topologyComponent),
    ∃ _smoothabilityComponent :
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgeryComponent :
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.surgeryComponent,
    ∃ _topologyComponent :
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.topologyComponent,
    ∃ _subobligationFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _packageFullAssemblyPayload :
      (∃ _smoothabilityPackage : SmoothabilityPackage.{u},
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
        PoincareConjectureStatement.{u}),
    ∃ _projectStatement : PoincareConjectureStatement.{u},
    ∃ _completionPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _subobligationCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _packageCanonicalPayload :
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _canonicalTarget : canonicalCompletionTarget.{u},
      packageInputs =
        finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
          inputs := by
  rcases
    final_assembly_subobligation_boundary_full_certificate_and_statement_bundle
      inputs with
    ⟨ packageInputs
    , packagePayload
    , componentPayload
    , subobligationFullAssemblyPayload
    , packageFullAssemblyPayload
    , projectStatement
    , completionPayload
    , subobligationCanonicalPayload
    , packageCanonicalPayload
    , canonicalTarget
    , hpackageInputs ⟩
  rcases packagePayload with
    ⟨ _smoothabilityRequirement
    , _analyticRequirement
    , _surgeryRequirement
    , finiteExtinctionRequirement
    , _topologyRequirement ⟩
  rcases componentPayload with
    ⟨ smoothabilityComponent, surgeryComponent, topologyComponent ⟩
  exact
    ⟨ packageInputs
    , inputs.finiteExtinctionSubobligations
    , finiteExtinctionRequirement
    , ⟨smoothabilityComponent, surgeryComponent, topologyComponent⟩
    , smoothabilityComponent
    , surgeryComponent
    , topologyComponent
    , subobligationFullAssemblyPayload
    , packageFullAssemblyPayload
    , projectStatement
    , completionPayload
    , subobligationCanonicalPayload
    , packageCanonicalPayload
    , canonicalTarget
    , hpackageInputs
    ⟩

/-- Theorem contract for `final_assembly_subobligation_boundary_component_witness_family_completion_certificate_bundle`. -/
theorem final_assembly_subobligation_boundary_component_witness_family_completion_certificate_bundle_eq :
    @Poincare.final_assembly_subobligation_boundary_component_witness_family_completion_certificate_bundle =
      @Poincare.final_assembly_subobligation_boundary_component_witness_family_completion_certificate_bundle :=
  rfl

/--
The final-assembly sub-obligation boundary can be pushed to a concrete target
sweepout certificate: its finite-extinction package requirement selects a
surgery package for the target manifold, and the sweepout interface projects
the existence, parameter-space, continuity, area-bound, and nontriviality
records needed downstream.
-/
theorem final_assembly_subobligation_boundary_target_sweepout_package_certificate_bundle
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ packageInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ _rawSubobligations :
      FinalAssemblyFiniteExtinctionSubobligationFamily.{u},
    ∃ _finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
    ∃ _componentPayload :
      (∃ _smoothability :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.topologyComponent),
    ∃ _targetSweepoutCertificate :
      TargetFiniteExtinctionSweepoutPackageCertificate M,
    ∃ _projectStatement : PoincareConjectureStatement.{u},
    ∃ _completionPayload :
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness),
    ∃ _canonicalTarget : canonicalCompletionTarget.{u},
      packageInputs =
        finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
          inputs := by
  rcases
      final_assembly_subobligation_boundary_component_witness_family_completion_certificate_bundle
        inputs with
    ⟨packageInputs, rawSubobligations, finiteExtinctionRequirement,
      componentPayload, _smoothabilityComponent, _surgeryComponent,
      _topologyComponent, _subobligationFullAssemblyPayload,
      _packageFullAssemblyPayload, projectStatement, completionPayload,
      _subobligationCanonicalPayload, _packageCanonicalPayload,
      canonicalTarget, hpackageInputs⟩
  let targetSweepoutCertificate :=
    target_finite_extinction_sweepout_package_certificate_of_finiteExtinctionPackage_requirement
      finiteExtinctionRequirement M
  exact
    ⟨packageInputs, rawSubobligations, finiteExtinctionRequirement,
      componentPayload, targetSweepoutCertificate, projectStatement,
      completionPayload, canonicalTarget, hpackageInputs⟩

/-- Theorem contract for `final_assembly_subobligation_boundary_target_sweepout_package_certificate_bundle`. -/
theorem final_assembly_subobligation_boundary_target_sweepout_package_certificate_bundle_eq :
    @Poincare.final_assembly_subobligation_boundary_target_sweepout_package_certificate_bundle =
      @Poincare.final_assembly_subobligation_boundary_target_sweepout_package_certificate_bundle :=
  rfl

/--
The final-assembly sub-obligation boundary reaches the richer target sweepout
interface frontier, not only the package-level target certificate.  The same
finite-extinction package requirement extracted from the boundary supplies the
target sweepout package certificate, the target interface bundle, and the five
interface projections used by downstream sweepout arguments.
-/
theorem final_assembly_subobligation_boundary_target_sweepout_interface_projection_certificate_bundle
    (inputs : FinalAssemblySubobligationBoundaryInputs.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ packageInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ _rawSubobligations :
      FinalAssemblyFiniteExtinctionSubobligationFamily.{u},
    ∃ finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
    ∃ _componentPayload :
      (∃ _smoothability :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u}
          DependencyComponentSlot.topologyComponent),
    ∃ certificate : TargetFiniteExtinctionSweepoutPackageCertificate M,
    ∃ bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M,
      certificate =
          target_finite_extinction_sweepout_package_certificate_of_finiteExtinctionPackage_requirement
            finiteExtinctionRequirement M ∧
      bundle =
          target_finite_extinction_sweepout_interface_bundle_of_finiteExtinctionPackage_requirement
            finiteExtinctionRequirement M ∧
      HasFiniteExtinctionSweepoutExistence M
          finite_extinction_fundamental_group_input_of_target ∧
      HasFiniteExtinctionSweepoutParameterSpace M
          finite_extinction_fundamental_group_input_of_target ∧
      HasFiniteExtinctionSweepoutContinuity M
          finite_extinction_fundamental_group_input_of_target
          (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
      HasFiniteExtinctionSweepoutAreaBound M
          finite_extinction_fundamental_group_input_of_target
          (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
      HasFiniteExtinctionSweepoutNontriviality M
          finite_extinction_fundamental_group_input_of_target
          (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
      (∃ _projectStatement : PoincareConjectureStatement.{u},
       ∃ _completionPayload :
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness),
       ∃ _canonicalTarget : canonicalCompletionTarget.{u},
        packageInputs =
          finalAssemblyPackageBoundaryInputs_of_subobligationBoundaryInputs
            inputs) := by
  rcases
      final_assembly_subobligation_boundary_component_witness_family_completion_certificate_bundle
        inputs with
    ⟨packageInputs, rawSubobligations, finiteExtinctionRequirement,
      componentPayload, _smoothabilityComponent, _surgeryComponent,
      _topologyComponent, _subobligationFullAssemblyPayload,
      _packageFullAssemblyPayload, projectStatement, completionPayload,
      _subobligationCanonicalPayload, _packageCanonicalPayload,
      canonicalTarget, hpackageInputs⟩
  rcases
      target_finite_extinction_sweepout_certificate_and_interface_projection_bundle_of_finiteExtinctionPackage_requirement
        finiteExtinctionRequirement M with
    ⟨certificate, bundle, hcertificate, hbundle, hexistence,
      hparameterSpace, hcontinuity, hareaBound, hnontriviality⟩
  exact
    ⟨packageInputs, rawSubobligations, finiteExtinctionRequirement,
      componentPayload, certificate, bundle, hcertificate, hbundle,
      hexistence, hparameterSpace, hcontinuity, hareaBound, hnontriviality,
      projectStatement, completionPayload, canonicalTarget, hpackageInputs⟩

/-- Theorem contract for `final_assembly_subobligation_boundary_target_sweepout_interface_projection_certificate_bundle`. -/
theorem final_assembly_subobligation_boundary_target_sweepout_interface_projection_certificate_bundle_eq :
    @Poincare.final_assembly_subobligation_boundary_target_sweepout_interface_projection_certificate_bundle =
      @Poincare.final_assembly_subobligation_boundary_target_sweepout_interface_projection_certificate_bundle :=
  rfl

end Poincare
