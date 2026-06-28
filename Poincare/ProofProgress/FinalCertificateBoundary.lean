/-
Final certificate boundary for the canonical completion payload.

This module does not define the reserved final theorem.  It records the
smallest package-layer boundary found by the current assembly bridge: the
canonical completion target and payload need universal finite extinction
together with the post-extinction topology extraction bridge.
-/

import Poincare.CanonicalBridges
import Poincare.ProofProgress.FullAssemblyClosure
import Poincare.ProofProgress.GroundedFiniteExtinctionCertificate
import Poincare.ProofProgress.TopologyProductionPackageNextField

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Minimal production package inputs for the current canonical completion route.

The topology package remains part of the fuller assembly payload because it
supplies the post-extinction extraction bridge used by the canonical completion
target/payload after smoothability turns topological targets into smooth surgery
targets.
-/
structure FinalCertificateMinimalPackageInputs where
  /-- Moise/smoothability package for target topological 3-manifolds. -/
  smoothability :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage
  /-- Finite-extinction surgery package family for all smooth target manifolds. -/
  finiteExtinction :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage

/--
Primitive named input for the canonical completion route after the production
packages have already assembled finite extinction for topological targets.
-/
structure FinalCertificatePrimitiveInputs where
  /-- Universal finite extinction for the topological target family. -/
  universalFiniteExtinction : UniversalFiniteExtinctionStatement.{u}
  /-- Extraction from finite-extinction outputs to the 3-sphere conclusion. -/
  extinctionImpliesSphere : ExtinctionImpliesSphereStatement.{u}

/--
The old three-package final assembly boundary projects to the two package
inputs actually used by the canonical completion route.
-/
def finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    FinalCertificateMinimalPackageInputs.{u} where
  smoothability := inputs.smoothability
  finiteExtinction := inputs.finiteExtinction

/--
The two production package inputs assemble the primitive named universal
finite-extinction input consumed by `CompletionTarget`.
-/
def finalCertificatePrimitiveInputs_of_minimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    FinalCertificatePrimitiveInputs.{u} where
  universalFiniteExtinction :=
    universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  extinctionImpliesSphere := extractSphere

/-- The primitive finite-extinction input proves the canonical completion target. -/
theorem canonical_completion_target_of_finalCertificatePrimitiveInputs
    (inputs : FinalCertificatePrimitiveInputs.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_universalFiniteExtinctionStatement
    inputs.universalFiniteExtinction
    inputs.extinctionImpliesSphere

/-- The primitive finite-extinction input exposes the canonical completion payload. -/
theorem canonical_completion_payload_of_finalCertificatePrimitiveInputs
    (inputs : FinalCertificatePrimitiveInputs.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_universalFiniteExtinctionStatement
    inputs.universalFiniteExtinction
    inputs.extinctionImpliesSphere

/--
The two minimal package inputs prove the canonical completion target by first
assembling the primitive universal finite-extinction statement.
-/
theorem canonical_completion_target_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_finalCertificatePrimitiveInputs
    (finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs extractSphere)

/--
The two minimal package inputs expose the canonical completion payload by first
assembling the primitive universal finite-extinction statement.
-/
theorem canonical_completion_payload_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_finalCertificatePrimitiveInputs
    (finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs extractSphere)

/--
Single-statement boundary: the current canonical completion target and payload
close conditionally from the smoothability package, the finite-extinction
package layer, and the explicit post-extinction extraction bridge.
-/
theorem final_certificate_boundary_of_smoothability_and_finiteExtinctionPackage
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonicalCompletionTarget.{u} ∧
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
  exact
    ⟨ canonical_completion_target_of_finalCertificateMinimalPackageInputs
        inputs extractSphere
    , canonical_completion_payload_of_finalCertificateMinimalPackageInputs
        inputs extractSphere
    ⟩

/--
The canonical payload obtained from the old three-input boundary is the payload
obtained from its two-input final-certificate projection.
-/
theorem canonical_completion_payload_of_finalAssemblyPackageBoundaryInputs_to_minimalPackageInputs_eq
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    canonical_completion_payload_of_finalAssemblyPackageBoundaryInputs
        inputs =
      canonical_completion_payload_of_finalCertificateMinimalPackageInputs
        (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
          inputs)
        (extinction_implies_sphere_of_topology_package inputs.topology) := by
  apply Subsingleton.elim

/--
The canonical target obtained from the old three-input boundary is the target
obtained from its two-input final-certificate projection.
-/
theorem canonical_completion_target_of_finalAssemblyPackageBoundaryInputs_to_minimalPackageInputs_eq
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    canonical_completion_target_of_finalAssemblyPackageBoundaryInputs
        inputs =
      canonical_completion_target_of_finalCertificateMinimalPackageInputs
        (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
          inputs)
        (extinction_implies_sphere_of_topology_package inputs.topology) := by
  apply Subsingleton.elim

/--
The checked certificate proposition still carries the repository's current
remaining-dependency package field.  Given that field and the primitive
universal finite-extinction input, the existing certificate constructor closes.
-/
theorem completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
    (dependencies : RemainingDependencyPackage.{u})
    (inputs : FinalCertificatePrimitiveInputs.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
    dependencies inputs.universalFiniteExtinction

/--
The certificate constructor above has the same canonical completion payload as
the primitive universal finite-extinction route.
-/
theorem canonical_completion_payload_of_completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs_eq
    (dependencies : RemainingDependencyPackage.{u})
    (inputs : FinalCertificatePrimitiveInputs.{u}) :
    canonical_completion_payload_of_completion_certificate
        (completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
          dependencies inputs) =
      canonical_completion_payload_of_finalCertificatePrimitiveInputs inputs := by
  exact
    canonical_completion_payload_of_completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement_eq
      dependencies inputs.universalFiniteExtinction

/--
Grounded universal finite extinction closes the checked certificate through the
same remaining-dependency constructor after converting the grounded pillar to
the legacy universal finite-extinction interface.
-/
theorem completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
    dependencies (universalFiniteExtinctionStatement_of_grounded grounded)

/--
The grounded certificate constructor is definitionally the existing
remaining-dependency/universal finite-extinction constructor after the grounded
pillar is converted to the legacy interface.
-/
theorem completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement
        dependencies grounded =
      completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
        dependencies (universalFiniteExtinctionStatement_of_grounded grounded) := by
  apply Subsingleton.elim

/--
The canonical payload extracted from the grounded certificate constructor is
the payload of the converted universal finite-extinction statement.
-/
theorem canonical_completion_payload_of_completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    canonical_completion_payload_of_completion_certificate
        (completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement
          dependencies grounded) =
      canonical_completion_payload_of_universalFiniteExtinctionStatement
        (universalFiniteExtinctionStatement_of_grounded grounded)
        (extinction_implies_sphere_of_topology_package dependencies.topology) := by
  exact
    canonical_completion_payload_of_completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement_eq
      dependencies (universalFiniteExtinctionStatement_of_grounded grounded)

/--
The primitive finite-extinction input and the current remaining-dependency
package together expose the full canonical certificate-facing payload:
canonical target, canonical completion payload, and checked completion
certificate.
-/
theorem canonical_payload_and_final_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
    (dependencies : RemainingDependencyPackage.{u})
    (inputs : FinalCertificatePrimitiveInputs.{u}) :
    canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  ⟨ canonical_completion_target_of_finalCertificatePrimitiveInputs inputs
  , canonical_completion_payload_of_finalCertificatePrimitiveInputs inputs
  , completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
      dependencies inputs
  ⟩

/--
The primitive-input/remaining-dependency payload is exactly the tuple of the
primitive canonical target, primitive canonical payload, and existing checked
certificate constructor.
-/
theorem canonical_payload_and_final_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs_eq
    (dependencies : RemainingDependencyPackage.{u})
    (inputs : FinalCertificatePrimitiveInputs.{u}) :
    canonical_payload_and_final_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
        dependencies inputs =
      ⟨ canonical_completion_target_of_finalCertificatePrimitiveInputs inputs
      , canonical_completion_payload_of_finalCertificatePrimitiveInputs inputs
      , completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
          dependencies inputs
      ⟩ := by
  apply Subsingleton.elim

/--
The remaining dependency package, grounded universal finite extinction, and a
theorem-shaped topology extraction statement close the canonical
certificate-facing payload.  The topology statement supplies the extractor used
for the canonical target and completion payload; the remaining dependency
package is needed only for the checked certificate proposition.
-/
theorem canonical_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement
    (dependencies : RemainingDependencyPackage.{u})
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  ⟨ canonical_completion_target_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      finiteExtinction topologyStatement
  , canonical_completion_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      finiteExtinction topologyStatement
  , completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      dependencies finiteExtinction
  ⟩

/--
The topology-extraction-statement final payload is exactly the tuple of the
canonical target route, canonical payload route, and checked certificate
constructor using the same universal finite-extinction statement.
-/
theorem canonical_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies finiteExtinction topologyStatement =
      ⟨ canonical_completion_target_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          finiteExtinction topologyStatement
      , canonical_completion_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          finiteExtinction topologyStatement
      , completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
          dependencies finiteExtinction
      ⟩ := by
  apply Subsingleton.elim

/--
The remaining dependency package, universal finite extinction, and a
theorem-shaped topology extraction statement also close the project-level
certificate-facing payload: the Poincare project statement, its completion
payload, and the checked completion certificate.
-/
theorem project_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement
    (dependencies : RemainingDependencyPackage.{u})
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  ⟨ poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      finiteExtinction topologyStatement
  , poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      finiteExtinction topologyStatement
  , completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      dependencies finiteExtinction
  ⟩

/--
The project-level topology-extraction-statement final payload is exactly the
tuple of the project statement route, project payload route, and checked
certificate constructor using the same universal finite-extinction statement.
-/
theorem project_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    project_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies finiteExtinction topologyStatement =
      ⟨ poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          finiteExtinction topologyStatement
      , poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          finiteExtinction topologyStatement
      , completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
          dependencies finiteExtinction
      ⟩ := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction and a theorem-shaped topology extraction
statement close the same canonical certificate-facing payload, with the
grounded pillar first converted to the legacy universal finite-extinction
interface consumed by the existing certificate constructor.
-/
theorem canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  ⟨ canonical_completion_target_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      (universalFiniteExtinctionStatement_of_grounded grounded)
      topologyStatement
  , canonical_completion_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      (universalFiniteExtinctionStatement_of_grounded grounded)
      topologyStatement
  , completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement
      dependencies grounded
  ⟩

/--
The grounded finite-extinction final payload is exactly the
universal-finite-extinction/topology-extraction payload after converting the
grounded statement to the legacy universal finite-extinction interface.
-/
theorem canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies grounded topologyStatement =
      canonical_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies (universalFiniteExtinctionStatement_of_grounded grounded)
        topologyStatement := by
  apply Subsingleton.elim

/--
The grounded finite-extinction final payload is the tuple of the canonical
target route, canonical payload route, and direct grounded certificate
constructor.
-/
theorem canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement_tuple_eq
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies grounded topologyStatement =
      ⟨ canonical_completion_target_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          (universalFiniteExtinctionStatement_of_grounded grounded)
          topologyStatement
      , canonical_completion_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          (universalFiniteExtinctionStatement_of_grounded grounded)
          topologyStatement
      , completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement
          dependencies grounded
      ⟩ := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction and theorem-shaped topology extraction
close the project-level certificate-facing payload, with the checked
certificate built from the direct grounded certificate constructor.
-/
theorem project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  ⟨ poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      (universalFiniteExtinctionStatement_of_grounded grounded)
      topologyStatement
  , poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      (universalFiniteExtinctionStatement_of_grounded grounded)
      topologyStatement
  , completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement
      dependencies grounded
  ⟩

/--
The grounded project-level final payload is exactly the universal
finite-extinction/topology-extraction project payload after converting the
grounded statement to the legacy universal finite-extinction interface.
-/
theorem project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies grounded topologyStatement =
      project_payload_and_final_certificate_of_remainingDependencyPackage_universalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies (universalFiniteExtinctionStatement_of_grounded grounded)
        topologyStatement := by
  apply Subsingleton.elim

/--
The grounded project-level final payload is the tuple of the project statement
route, project payload route, and direct grounded certificate constructor.
-/
theorem project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement_tuple_eq
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
        dependencies grounded topologyStatement =
      ⟨ poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          (universalFiniteExtinctionStatement_of_grounded grounded)
          topologyStatement
      , poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          (universalFiniteExtinctionStatement_of_grounded grounded)
          topologyStatement
      , completion_certificate_of_remainingDependencyPackage_and_groundedUniversalFiniteExtinctionStatement
          dependencies grounded
      ⟩ := by
  apply Subsingleton.elim

/--
The checked certificate proposition itself has no extra primitive
finite-extinction field: existing projections make it equivalent to the current
remaining dependency package.
-/
theorem final_certificate_iff_remainingDependencyPackage :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  poincareCompletionCertificate_iff_remainingDependencyPackage

/--
The remaining dependency package can be repackaged as the three production
package inputs used by the full assembly boundary.
-/
def finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
    (dependencies : RemainingDependencyPackage.{u}) :
    FinalAssemblyPackageBoundaryInputs.{u} where
  smoothability := dependencies.smoothability
  finiteExtinction := dependencies.surgery
  topology := dependencies.topology

/-- The three production package inputs supply the remaining dependency package. -/
def remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    RemainingDependencyPackage.{u} :=
  remainingDependencyPackage_iff_poincareProofDependencies.mpr
    (poincareProofDependencies_of_finalAssemblyPackageBoundaryInputs inputs)

/--
The full assembly package boundary is exactly the nonempty data form of the
remaining dependency package.
-/
theorem nonempty_finalAssemblyPackageBoundaryInputs_iff_remainingDependencyPackage :
    Nonempty (FinalAssemblyPackageBoundaryInputs.{u}) ↔
      RemainingDependencyPackage.{u} := by
  constructor
  · rintro ⟨inputs⟩
    exact remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs inputs
  · intro dependencies
    exact ⟨finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
      dependencies⟩

/--
The checked certificate is therefore equivalent to the nonempty three-package
final assembly boundary.  The topology package is still present here because it
is part of `RemainingDependencyPackage`.
-/
theorem final_certificate_iff_nonempty_finalAssemblyPackageBoundaryInputs :
    PoincareCompletionCertificate.{u} ↔
      Nonempty (FinalAssemblyPackageBoundaryInputs.{u}) := by
  constructor
  · intro certificate
    exact
      ⟨finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
        (remaining_dependency_package_of_completion_certificate certificate)⟩
  · rintro ⟨inputs⟩
    exact
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
          inputs)

/-- The old three-input final assembly boundary closes the checked certificate. -/
theorem completion_certificate_of_finalAssemblyPackageBoundaryInputs
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_package
    (remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs inputs)

/--
The certificate from the three-input boundary is exactly the existing
remaining-dependency certificate constructor applied to the same repackaged
dependency field.
-/
theorem completion_certificate_of_finalAssemblyPackageBoundaryInputs_eq
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    completion_certificate_of_finalAssemblyPackageBoundaryInputs inputs =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
          inputs) := by
  apply Subsingleton.elim

/--
The two-input canonical boundary plus the topology package is precisely enough
to close the checked certificate, because those three fields reconstruct
`RemainingDependencyPackage`.
-/
theorem completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_finalAssemblyPackageBoundaryInputs
    { smoothability := inputs.smoothability
      finiteExtinction := inputs.finiteExtinction
      topology := topology }

/--
The current certificate boundary, expressed directly as named package-layer
requirements: smoothability, finite extinction, and topology.
-/
theorem completion_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
    topology

/--
The three named final package-layer requirements close the complete canonical
certificate-facing payload: canonical target, canonical completion payload, and
the checked completion certificate.  The topology package supplies the
post-extinction extractor needed by the two-input canonical boundary and also
reconstructs the remaining dependency package for the checked certificate.
-/
theorem canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
  exact
    ⟨ canonical_completion_target_of_finalCertificateMinimalPackageInputs
        inputs (extinction_implies_sphere_of_topology_package topology)
    , canonical_completion_payload_of_finalCertificateMinimalPackageInputs
        inputs (extinction_implies_sphere_of_topology_package topology)
    , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs topology
    ⟩

/--
The named package-layer canonical payload is exactly the tuple obtained by
projecting through the minimal two-input canonical boundary and the topology
package certificate constructor.
-/
theorem canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage_eq
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        smoothability finiteExtinction topology =
      (let inputs : FinalCertificateMinimalPackageInputs.{u} :=
        { smoothability := smoothability
          finiteExtinction := finiteExtinction }
      ⟨ canonical_completion_target_of_finalCertificateMinimalPackageInputs
          inputs (extinction_implies_sphere_of_topology_package topology)
      , canonical_completion_payload_of_finalCertificateMinimalPackageInputs
          inputs (extinction_implies_sphere_of_topology_package topology)
      , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      ⟩) := by
  apply Subsingleton.elim

/--
The two canonical package inputs plus the topology package also close the
project-level payload: the Poincare statement, its completion payload, and the
checked completion certificate.  This packages the topology extraction
statement supplied by the topology package with the universal finite-extinction
statement assembled from smoothability and finite extinction.
-/
theorem project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  let finiteExtinction : UniversalFiniteExtinctionStatement.{u} :=
    universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
      inputs.smoothability inputs.finiteExtinction
  let topologyStatement : ExtinctionTopologyExtractionStatement.{u} :=
    extinction_topology_extraction_statement_of_topology_package topology
  ⟨ poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      finiteExtinction topologyStatement
  , poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
      finiteExtinction topologyStatement
  , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs topology
  ⟩

/--
The minimal-input/topology-package project payload is exactly the tuple formed
from the assembled universal finite-extinction statement, the topology
package's extraction statement, and the checked certificate constructor.
-/
theorem project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage_eq
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs topology =
      (let finiteExtinction : UniversalFiniteExtinctionStatement.{u} :=
        universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
          inputs.smoothability inputs.finiteExtinction
      let topologyStatement : ExtinctionTopologyExtractionStatement.{u} :=
        extinction_topology_extraction_statement_of_topology_package topology
      ⟨ poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          finiteExtinction topologyStatement
      , poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
          finiteExtinction topologyStatement
      , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      ⟩) := by
  apply Subsingleton.elim

/--
The simply connected extinction-recognition prefix now supplies the topology
package-layer requirement consumed by final assembly.
-/
def topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.topologyPackage :=
  extinctionTopologyExtractionPackage_of_simplyConnectedExtinctionRecognitionPrefixPackage
    recognitionPrefix

/--
The two non-topology final-certificate package inputs plus the simply connected
recognition prefix reconstruct the old three-input final assembly boundary.
-/
def finalAssemblyPackageBoundaryInputs_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    FinalAssemblyPackageBoundaryInputs.{u} where
  smoothability := inputs.smoothability
  finiteExtinction := inputs.finiteExtinction
  topology :=
    topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix

/--
After the topology package is constructed from the recognition prefix, the
checked completion certificate only still needs the smoothability and
finite-extinction package inputs carried by `FinalCertificateMinimalPackageInputs`.
-/
theorem completion_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_finalAssemblyPackageBoundaryInputs
    (finalAssemblyPackageBoundaryInputs_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix)

/--
The canonical target, canonical payload, and checked certificate close from the
two non-topology package inputs plus the simply connected recognition prefix.
-/
theorem canonical_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  let topology :=
    topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix
  ⟨ canonical_completion_target_of_finalCertificateMinimalPackageInputs
      inputs (extinction_implies_sphere_of_topology_package topology)
  , canonical_completion_payload_of_finalCertificateMinimalPackageInputs
      inputs (extinction_implies_sphere_of_topology_package topology)
  , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs topology
  ⟩

/--
The same recognition prefix also closes the project-level final payload by
first constructing the topology package requirement and then using the
minimal-input/topology-package project route.
-/
theorem project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  let topology :=
    topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix
  project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    inputs topology

/--
The recognition-prefix project payload is exactly the minimal-input/topology
package payload after constructing the topology package from the prefix.
-/
theorem project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix_eq
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        inputs recognitionPrefix =
      (let topology :=
        topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
          recognitionPrefix
      project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs topology) := by
  rfl

/--
The smoothability and finite-extinction package requirements plus a simply
connected extinction-recognition prefix close the complete final-certificate
payload.  This avoids requiring downstream code to separately manufacture the
minimal input record before consuming the recognition-prefix topology package.
-/
theorem canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  canonical_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
    recognitionPrefix

/--
The direct recognition-prefix final-certificate route is exactly the
minimal-input recognition-prefix theorem after packing the two named
non-topology package requirements.
-/
theorem canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix_eq
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
        smoothability finiteExtinction recognitionPrefix =
      canonical_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        { smoothability := smoothability
          finiteExtinction := finiteExtinction }
        recognitionPrefix := by
  apply Subsingleton.elim

/--
The smoothability and finite-extinction package requirements plus a simply
connected extinction-recognition prefix also close the project-level final
payload directly, without requiring downstream code to pack the minimal-input
record first.
-/
theorem project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} :=
  project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
    recognitionPrefix

/--
The direct recognition-prefix project route is exactly the minimal-input
recognition-prefix theorem after packing the two named non-topology package
requirements.
-/
theorem project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix_eq
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
        smoothability finiteExtinction recognitionPrefix =
      project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        { smoothability := smoothability
          finiteExtinction := finiteExtinction }
        recognitionPrefix := by
  rfl

/--
The direct recognition-prefix boundary can expose both final payload layers at
once: the public Poincare statement/payload, the canonical completion
target/payload, and the checked certificate.
-/
theorem project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} := by
  let projectPayload :=
    project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix
  let canonicalPayload :=
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix
  exact
    ⟨ projectPayload.1
    , projectPayload.2.1
    , canonicalPayload.1
    , canonicalPayload.2.1
    , projectPayload.2.2
    ⟩

/--
The bundled recognition-prefix final payload is exactly the tuple assembled
from the direct project route, the direct canonical route, and the checked
certificate carried by the project route.
-/
theorem project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix_eq
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
        smoothability finiteExtinction recognitionPrefix =
      (let projectPayload :=
        project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
          smoothability finiteExtinction recognitionPrefix
      let canonicalPayload :=
        canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
          smoothability finiteExtinction recognitionPrefix
      ⟨ projectPayload.1
      , projectPayload.2.1
      , canonicalPayload.1
      , canonicalPayload.2.1
      , projectPayload.2.2
      ⟩) := by
  apply Subsingleton.elim

/--
The direct recognition-prefix boundary discharges each universe-indexed
completion criterion, by projecting the canonical payload component from the
same package-layer inputs.
-/
theorem completion_criterion_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (witness : Type u)
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  (canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    smoothability finiteExtinction recognitionPrefix).2.1.choose_spec witness

/--
The direct criterion theorem is exactly the witness projection from the
canonical payload route over the same recognition-prefix package inputs.
-/
theorem completion_criterion_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix_eq
    (witness : Type u)
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    completion_criterion_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
        witness smoothability finiteExtinction recognitionPrefix =
      (canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
        smoothability finiteExtinction recognitionPrefix).2.1.choose_spec witness := by
  apply Subsingleton.elim

/--
Projecting the remaining dependency package out of the certificate built from
the three package inputs recovers the same repackaged dependency field.
-/
theorem remainingDependencyPackage_of_completion_certificate_of_finalAssemblyPackageBoundaryInputs_eq
    (inputs : FinalAssemblyPackageBoundaryInputs.{u}) :
    remaining_dependency_package_of_completion_certificate
        (completion_certificate_of_finalAssemblyPackageBoundaryInputs inputs) =
      remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
        inputs := by
  apply Subsingleton.elim

/--
Every checked certificate projects back to the three package-layer requirements
carried by `RemainingDependencyPackage`.
-/
theorem package_layer_requirements_payload_of_final_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  let dependencies : RemainingDependencyPackage.{u} :=
    remaining_dependency_package_of_completion_certificate certificate
  exact ⟨dependencies.smoothability, dependencies.surgery,
    dependencies.topology⟩

/-- A checked certificate forces the smoothability package-layer requirement. -/
theorem smoothabilityPackage_requirement_of_final_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage := by
  rcases package_layer_requirements_payload_of_final_certificate
      certificate with
    ⟨smoothability, _finiteExtinction, _topology⟩
  exact smoothability

/-- A checked certificate forces the finite-extinction package-layer requirement. -/
theorem finiteExtinctionPackage_requirement_of_final_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage := by
  rcases package_layer_requirements_payload_of_final_certificate
      certificate with
    ⟨_smoothability, finiteExtinction, _topology⟩
  exact finiteExtinction

/-- A checked certificate forces the topology package-layer requirement. -/
theorem topologyPackage_requirement_of_final_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.topologyPackage := by
  rcases package_layer_requirements_payload_of_final_certificate
      certificate with
    ⟨_smoothability, _finiteExtinction, topology⟩
  exact topology

/--
Exact remaining certificate boundary as named package-layer requirements.  This
is the same data as `RemainingDependencyPackage`, unfolded through the current
package crosswalk.
-/
theorem final_certificate_iff_named_package_layer_requirements :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · exact package_layer_requirements_payload_of_final_certificate
  · rintro ⟨smoothability, finiteExtinction, topology⟩
    exact
      completion_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        smoothability finiteExtinction topology

/--
Equivalent phrasing: the two-input canonical boundary plus the topology package
is exactly the current checked-certificate boundary.
-/
theorem final_certificate_iff_minimalPackageInputs_and_topologyPackage :
    PoincareCompletionCertificate.{u} ↔
      ∃ _inputs : FinalCertificateMinimalPackageInputs.{u},
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · intro certificate
    exact
      ⟨ { smoothability :=
            smoothabilityPackage_requirement_of_final_certificate certificate
          finiteExtinction :=
            finiteExtinctionPackage_requirement_of_final_certificate
              certificate }
      , topologyPackage_requirement_of_final_certificate certificate
      ⟩
  · rintro ⟨inputs, topology⟩
    exact
      completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs topology

/--
Once the two canonical package inputs are fixed, the checked completion
certificate is equivalent to the topology package alone. Thus the remaining
certificate boundary over the current canonical route is exactly the topology
package field unless another compiled projection constructs that field.
-/
theorem final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    PoincareCompletionCertificate.{u} ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · exact topologyPackage_requirement_of_final_certificate
  · intro topology
    exact
      completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs topology

/--
Exact remaining boundary for upgrading the current canonical route to the
checked completion certificate. The two canonical package inputs provide
universal finite extinction; the topology package supplies the extraction bridge
needed for the canonical target, payload, and checked certificate.
-/
theorem canonical_payload_and_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u}) ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact topologyPackage_requirement_of_final_certificate payload.2.2
  · intro topology
    exact
      ⟨ canonical_completion_target_of_finalCertificateMinimalPackageInputs
          inputs
          (extinction_implies_sphere_of_topology_package topology)
      , canonical_completion_payload_of_finalCertificateMinimalPackageInputs
          inputs
          (extinction_implies_sphere_of_topology_package topology)
      , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      ⟩

end Poincare
