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
The minimal final-certificate inputs plus a topology package discharge each
universe-indexed completion criterion directly, by projecting the canonical
completion payload carried by the same package inputs.
-/
theorem completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    (witness : Type u)
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    CompletionCriterionAtUniverse witness :=
  (canonical_completion_payload_of_finalCertificateMinimalPackageInputs
    inputs (extinction_implies_sphere_of_topology_package topology)).choose_spec
      witness

/--
The minimal-input topology-package criterion theorem is exactly the witness
projection from the canonical completion payload over those same inputs.
-/
theorem completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage_eq
    (witness : Type u)
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        witness inputs topology =
      (canonical_completion_payload_of_finalCertificateMinimalPackageInputs
        inputs
        (extinction_implies_sphere_of_topology_package topology)).choose_spec
        witness := by
  apply Subsingleton.elim

/--
The three named final package-layer requirements discharge each
universe-indexed completion criterion directly.
-/
theorem completion_criterion_of_smoothability_finiteExtinctionPackage_and_topologyPackage
    (witness : Type u)
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    CompletionCriterionAtUniverse witness :=
  completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    witness
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
    topology

/--
The named package-layer criterion theorem is exactly the minimal-input
criterion theorem after packing smoothability and finite extinction.
-/
theorem completion_criterion_of_smoothability_finiteExtinctionPackage_and_topologyPackage_eq
    (witness : Type u)
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    completion_criterion_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        witness smoothability finiteExtinction topology =
      completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        witness
        { smoothability := smoothability
          finiteExtinction := finiteExtinction }
        topology := by
  rfl

/--
The three named final package-layer requirements expose both final payload
layers at once: the public Poincare payload, the canonical completion payload,
and the checked certificate.
-/
theorem project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
  let projectPayload :=
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs topology
  let canonicalPayload :=
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
      smoothability finiteExtinction topology
  exact
    ⟨ projectPayload.1
    , projectPayload.2.1
    , canonicalPayload.1
    , canonicalPayload.2.1
    , projectPayload.2.2
    ⟩

/--
The package-layer bundled final payload is exactly the tuple assembled from
the direct topology-package project route, canonical route, and checked
certificate carried by the project route.
-/
theorem project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage_eq
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        smoothability finiteExtinction topology =
      (let inputs : FinalCertificateMinimalPackageInputs.{u} :=
        { smoothability := smoothability
          finiteExtinction := finiteExtinction }
      let projectPayload :=
        project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      let canonicalPayload :=
        canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
          smoothability finiteExtinction topology
      ⟨ projectPayload.1
      , projectPayload.2.1
      , canonicalPayload.1
      , canonicalPayload.2.1
      , projectPayload.2.2
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
A completed topology package projects back to the simply connected
extinction-recognition prefix.  This is the reverse boundary needed to state
the final-certificate route directly against the recognition prefix rather
than only against the full topology package.
-/
def simplyConnectedExtinctionRecognitionPrefixPackage_of_topologyPackage
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u} :=
  extinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage_of_topology_package
    topology

/--
The topology-package projection to the recognition prefix is exactly the
package-level prefix projection from the topology production package.
-/
theorem simplyConnectedExtinctionRecognitionPrefixPackage_of_topologyPackage_eq
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    simplyConnectedExtinctionRecognitionPrefixPackage_of_topologyPackage
        topology =
      extinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage_of_topology_package
        topology := by
  rfl

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
The fixed minimal final-certificate inputs plus a simply connected
extinction-recognition prefix discharge each universe-indexed completion
criterion. This projects the topology package from the recognition prefix and
then applies the minimal-input topology-package criterion theorem.
-/
theorem completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (witness : Type u)
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    witness inputs
    (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix)

/--
The minimal-input recognition-prefix criterion theorem is definitionally the
topology-package criterion theorem after projecting the topology package from
the recognition prefix.
-/
theorem completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix_eq
    (witness : Type u)
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        witness inputs recognitionPrefix =
      completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        witness inputs
        (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
          recognitionPrefix) := by
  rfl

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
The simply connected recognition prefix directly yields the public Poincare
statement over the fixed non-topology package inputs, by first manufacturing
the topology package consumed by the final-certificate route.
-/
theorem poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  (project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    inputs recognitionPrefix).1

/--
The same recognition prefix also produces an inhabited checked completion
certificate over the fixed smoothability and finite-extinction package inputs.
-/
theorem nonempty_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    Nonempty PoincareCompletionCertificate.{u} :=
  ⟨ completion_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix ⟩

/--
Bundled endpoint projection from the concrete recognition prefix: the prefix
closes both the public Poincare statement and the inhabited checked completion
certificate once the smoothability and finite-extinction package inputs are
fixed.
-/
theorem poincare_statement_and_nonempty_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} :=
  ⟨ poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix
  , nonempty_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix
  ⟩

/--
The minimal final-certificate inputs plus the recognition prefix simultaneously
expose the public Poincare statement, an inhabited checked certificate, and any
requested universe-indexed completion criterion.
-/
theorem poincare_statement_final_certificate_and_completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (witness : Type u)
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      CompletionCriterionAtUniverse witness :=
  ⟨ poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix
  , nonempty_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix
  , completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      witness inputs recognitionPrefix
  ⟩

/--
The minimal final-certificate inputs plus the recognition prefix expose the
public Poincare statement, an inhabited checked certificate, and the full
universe-indexed completion-criterion family.
-/
theorem poincare_statement_final_certificate_and_completion_criteria_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) :=
  ⟨ poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix
  , nonempty_final_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
      inputs recognitionPrefix
  , fun witness =>
      completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        witness inputs recognitionPrefix
  ⟩

/--
The minimal final-certificate inputs plus the recognition prefix expose the
same final endpoint with the concrete checked completion certificate, not only
an inhabited certificate wrapper.  This is the recognition-prefix analogue of
the topology-assembly checked-certificate endpoint.
-/
theorem poincare_statement_checked_certificate_and_completion_criteria_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  exact
    ⟨ poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        inputs recognitionPrefix
    , completion_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        inputs recognitionPrefix
    , fun witness =>
        completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
          witness inputs recognitionPrefix
    ⟩

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
The named smoothability and finite-extinction package requirements plus a
recognition prefix produce an inhabited checked completion certificate directly.
-/
theorem nonempty_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    Nonempty PoincareCompletionCertificate.{u} :=
  ⟨ (project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix).2.2 ⟩

/--
Bundled public endpoint projection from named package requirements plus the
recognition prefix: this gives the Poincare statement and an inhabited checked
certificate without requiring callers to pack minimal inputs first.
-/
theorem poincare_statement_and_nonempty_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} :=
  ⟨ (project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix).1
  , nonempty_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix
  ⟩

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
The named smoothability and finite-extinction package requirements plus the
recognition prefix simultaneously expose the public Poincare statement, an
inhabited checked certificate, and any requested universe-indexed completion
criterion.
-/
theorem poincare_statement_final_certificate_and_completion_criterion_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (witness : Type u)
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      CompletionCriterionAtUniverse witness :=
  ⟨ (project_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix).1
  , nonempty_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix
  , completion_criterion_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      witness smoothability finiteExtinction recognitionPrefix
  ⟩

/--
The named smoothability and finite-extinction package requirements plus the
recognition prefix expose both public and canonical final payload layers, the
checked certificate, and any requested universe-indexed completion criterion in
one endpoint.
-/
theorem project_canonical_final_certificate_and_completion_criterion_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
    (witness : Type u)
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
      PoincareCompletionCertificate.{u} ∧
      CompletionCriterionAtUniverse witness := by
  rcases
    project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_recognitionPrefix
      smoothability finiteExtinction recognitionPrefix with
    ⟨ hStatement, hProjectPayload, hCanonicalTarget, hCanonicalPayload,
      hCertificate ⟩
  exact
    ⟨ hStatement, hProjectPayload, hCanonicalTarget, hCanonicalPayload,
      hCertificate, hCanonicalPayload.choose_spec witness ⟩

/--
The checked remaining-dependency package, grounded universal finite extinction,
and a simply connected recognition prefix close both public and canonical
payload layers.  The recognition prefix contributes only the topology
extraction statement; the grounded pillar supplies the universal
finite-extinction route used by both payloads.
-/
theorem project_and_canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_recognitionPrefix
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} := by
  let topology :=
    topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix
  let topologyStatement : ExtinctionTopologyExtractionStatement.{u} :=
    extinction_topology_extraction_statement_of_topology_package topology
  let projectPayload :=
    project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
      dependencies grounded topologyStatement
  let canonicalPayload :=
    canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
      dependencies grounded topologyStatement
  exact
    ⟨ projectPayload.1
    , projectPayload.2.1
    , canonicalPayload.1
    , canonicalPayload.2.1
    , projectPayload.2.2
    ⟩

/--
The grounded remaining-dependency recognition-prefix route also discharges any
requested universe-indexed completion criterion by projecting the canonical
payload carried in the same bundled final-certificate endpoint.
-/
theorem project_canonical_final_certificate_and_completion_criterion_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_recognitionPrefix
    (witness : Type u)
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} ∧
      CompletionCriterionAtUniverse witness := by
  let payload :=
    project_and_canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_recognitionPrefix
      dependencies grounded recognitionPrefix
  exact
    ⟨ payload.1
    , payload.2.1
    , payload.2.2.1
    , payload.2.2.2.1
    , payload.2.2.2.2
    , payload.2.2.2.1.choose_spec witness
    ⟩

/--
Field-based endpoint for the grounded finite-extinction plus simply connected
recognition-prefix route.  It keeps the topology package produced by the
recognition prefix, the corresponding topology extraction statement, both
public and canonical payloads, the checked certificate, and all completion
criteria in one reusable certificate object.
-/
structure GroundedRecognitionPrefixFinalCertificatePayload
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) where
  topologyPackage :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.topologyPackage
  topologyStatement : ExtinctionTopologyExtractionStatement.{u}
  publicStatement : PoincareConjectureStatement.{u}
  publicPayload :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness
  canonicalTarget : canonicalCompletionTarget.{u}
  canonicalPayload :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness
  checkedCertificate : PoincareCompletionCertificate.{u}
  completionCriteria :
    ∀ witness : Type u, CompletionCriterionAtUniverse witness

/--
Construct the field-based final certificate endpoint from the grounded
finite-extinction pillar and the simply connected recognition prefix.
-/
def groundedRecognitionPrefixFinalCertificatePayload
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    GroundedRecognitionPrefixFinalCertificatePayload
      dependencies grounded recognitionPrefix := by
  let topologyPackage :=
    topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix
  let topologyStatement : ExtinctionTopologyExtractionStatement.{u} :=
    extinction_topology_extraction_statement_of_topology_package
      topologyPackage
  let projectPayload :=
    project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
      dependencies grounded topologyStatement
  let canonicalPayload :=
    canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
      dependencies grounded topologyStatement
  exact
    { topologyPackage := topologyPackage
      topologyStatement := topologyStatement
      publicStatement := projectPayload.1
      publicPayload := projectPayload.2.1
      canonicalTarget := canonicalPayload.1
      canonicalPayload := canonicalPayload.2.1
      checkedCertificate := projectPayload.2.2
      completionCriteria := fun witness =>
        canonicalPayload.2.1.choose_spec witness }

/--
The grounded recognition-prefix endpoint projects to the same public,
canonical, certificate, and criterion tuple used by theorem-shaped consumers.
-/
theorem groundedRecognitionPrefixFinalCertificatePayload_fields
    (witness : Type u)
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u} ∧
      CompletionCriterionAtUniverse witness := by
  let payload :=
    groundedRecognitionPrefixFinalCertificatePayload
      dependencies grounded recognitionPrefix
  exact
    ⟨ payload.publicStatement
    , payload.publicPayload
    , payload.canonicalTarget
    , payload.canonicalPayload
    , payload.checkedCertificate
    , payload.completionCriteria witness
    ⟩

/--
The same grounded recognition-prefix endpoint also exposes the full certificate
route: topology input, topology extraction statement, public statement,
inhabited checked certificate, canonical target, and both public and canonical
completion-criterion families.
-/
theorem groundedRecognitionPrefixFinalCertificatePayload_certificate_route_fields
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage ∧
      ExtinctionTopologyExtractionStatement.{u} ∧
      PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload :=
    groundedRecognitionPrefixFinalCertificatePayload
      dependencies grounded recognitionPrefix
  exact
    ⟨ payload.topologyPackage
    , payload.topologyStatement
    , payload.publicStatement
    , ⟨payload.checkedCertificate⟩
    , payload.canonicalTarget
    , payload.completionCriteria
    , payload.publicPayload
    , payload.canonicalPayload
    ⟩

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
After the two canonical non-topology package inputs are fixed, a checked final
certificate is equivalent to the simply connected extinction-recognition
prefix.  The forward direction projects the certificate to the topology
package and then to the recognition prefix; the reverse direction constructs
the topology package from the prefix and assembles the certificate.
-/
theorem final_certificate_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    PoincareCompletionCertificate.{u} ↔
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u} := by
  constructor
  · intro certificate
    exact
      simplyConnectedExtinctionRecognitionPrefixPackage_of_topologyPackage
        (topologyPackage_requirement_of_final_certificate certificate)
  · intro recognitionPrefix
    exact
      completion_certificate_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        inputs recognitionPrefix

/--
The inhabited-certificate form of the same fixed-input recognition-prefix
boundary.  This is the shape consumed by the standard nonempty-certificate
bridge to the public Poincare statement.
-/
theorem nonempty_final_certificate_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    Nonempty PoincareCompletionCertificate.{u} ↔
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u} := by
  constructor
  · rintro ⟨certificate⟩
    exact
      (final_certificate_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
        inputs).1 certificate
  · intro recognitionPrefix
    exact
      ⟨ (final_certificate_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
          inputs).2 recognitionPrefix ⟩

/--
After the two canonical non-topology package inputs are fixed, the final
statement-level endpoint with an inhabited checked certificate and one
universe-indexed completion criterion is equivalent to the simply connected
extinction-recognition prefix.
-/
theorem poincare_statement_nonempty_final_certificate_and_completion_criterion_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
    (witness : Type u)
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      CompletionCriterionAtUniverse witness) ↔
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u} := by
  constructor
  · intro payload
    exact
      (nonempty_final_certificate_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
        inputs).1 payload.2.1
  · intro recognitionPrefix
    exact
      poincare_statement_final_certificate_and_completion_criterion_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        witness inputs recognitionPrefix

/--
After the two canonical non-topology package inputs are fixed, the final
statement-level endpoint with an inhabited checked certificate and the full
universe-indexed completion-criterion family is equivalent to the simply
connected extinction-recognition prefix.
-/
theorem poincare_statement_nonempty_final_certificate_and_completion_criteria_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u} := by
  constructor
  · intro payload
    exact
      (nonempty_final_certificate_iff_recognitionPrefix_of_finalCertificateMinimalPackageInputs
        inputs).1 payload.2.1
  · intro recognitionPrefix
    exact
      poincare_statement_final_certificate_and_completion_criteria_of_finalCertificateMinimalPackageInputs_and_recognitionPrefix
        inputs recognitionPrefix

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

/--
Exact remaining boundary for the full public-plus-canonical final payload over
fixed smoothability and finite-extinction inputs: the only remaining package
field is the topology package.  The forward direction extracts that package
from the checked certificate component; the reverse direction assembles both
payload layers and the checked certificate from the same topology field.
-/
theorem project_and_canonical_payload_and_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      PoincareCompletionCertificate.{u}) ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact topologyPackage_requirement_of_final_certificate payload.2.2.2.2
  · intro topology
    exact
      project_and_canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        inputs.smoothability inputs.finiteExtinction topology

/--
Over fixed smoothability and finite-extinction package inputs, a topology
package directly yields the public Poincare statement.  This is the
statement-level projection of the checked final-certificate payload, without
requiring downstream code to unpack the larger tuple.
-/
theorem poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareConjectureStatement.{u} :=
  (project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    inputs topology).1

/--
After the two canonical non-topology package inputs are fixed, proving the
public Poincare statement together with a checked completion certificate is
equivalent to producing the topology package.  The reverse direction constructs
both the public statement and certificate from the same topology package; the
forward direction extracts the topology requirement from the checked
certificate component.
-/
theorem poincare_statement_and_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧ PoincareCompletionCertificate.{u}) ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact topologyPackage_requirement_of_final_certificate payload.2
  · intro topology
    exact
      ⟨ poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      ⟩

/--
The same fixed-input boundary stated in the inhabitance form consumed by
completion-certificate collapse routes: a nonempty checked certificate is
equivalent to the topology package.  The forward direction extracts the package
from the chosen certificate; the reverse direction builds that certificate from
the topology package and wraps it as an inhabitant.
-/
theorem nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    Nonempty PoincareCompletionCertificate.{u} ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · rintro ⟨certificate⟩
    exact topologyPackage_requirement_of_final_certificate certificate
  · intro topology
    exact
      ⟨ completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology ⟩

/--
The fixed minimal package inputs plus a topology package discharge the public
Poincare statement through the nonempty checked-certificate route.  This keeps
the final projection aligned with the reserved endpoint reduction while still
leaving the unconditional reserved theorem undeclared.
-/
theorem poincare_conjecture_statement_of_nonempty_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareConjectureStatement.{u} :=
  poincare_conjecture_of_nonempty_completion_certificate
    ((nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
      inputs).2 topology)

/--
After the two canonical non-topology package inputs are fixed, the public
Poincare statement together with an inhabited checked certificate is equivalent
to the topology package.  The reverse direction constructs the nonempty
certificate first, then projects the public statement through the standard
nonempty-certificate endpoint bridge.
-/
theorem poincare_statement_and_nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u}) ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact
      (nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).1 payload.2
  · intro topology
    let nonemptyCertificate : Nonempty PoincareCompletionCertificate.{u} :=
      (nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).2 topology
    exact
      ⟨ poincare_conjecture_of_nonempty_completion_certificate
          nonemptyCertificate
      , nonemptyCertificate
      ⟩

/--
After the two canonical non-topology package inputs are fixed, the full
statement-level final endpoint with a checked certificate and the universe
completion criterion is equivalent to the topology package.  The reverse
direction constructs the checked certificate and criterion from the same
topology requirement, so no separate final-certificate hypothesis is hidden in
the criterion projection.
-/
theorem poincare_statement_final_certificate_and_completion_criterion_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact topologyPackage_requirement_of_final_certificate payload.2.1
  · intro topology
    exact
      ⟨ poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      , completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
          inputs topology
      , fun witness =>
          completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
            witness inputs topology
      ⟩

/--
After the two canonical non-topology package inputs are fixed, the
statement-level endpoint using an inhabited checked certificate and the full
universe completion-criterion family is equivalent to the topology package.
This is the nonempty-certificate collapse form of the same final boundary.
-/
theorem poincare_statement_nonempty_final_certificate_and_completion_criteria_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact
      (nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).1 payload.2.1
  · intro topology
    let nonemptyCertificate : Nonempty PoincareCompletionCertificate.{u} :=
      (nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).2 topology
    exact
      ⟨ poincare_conjecture_of_nonempty_completion_certificate
          nonemptyCertificate
      , nonemptyCertificate
      , fun witness =>
          completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
            witness inputs topology
      ⟩

/--
Single assembly payload for the final-certificate topology boundary over fixed
smoothability and finite-extinction inputs.  A topology package yields the
public Poincare statement, the checked certificate, its inhabited form, the
canonical target, and both public/canonical completion payloads from the same
input.
-/
structure FinalCertificateTopologyAssemblyPayload
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) where
  publicStatement : PoincareConjectureStatement.{u}
  checkedCertificate : PoincareCompletionCertificate.{u}
  nonemptyCertificate : Nonempty PoincareCompletionCertificate.{u}
  canonicalTarget : canonicalCompletionTarget.{u}
  publicPayload :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness
  canonicalPayload :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness
  completionCriteria :
    ∀ witness : Type u, CompletionCriterionAtUniverse witness

/--
Fixed minimal package inputs plus a topology package construct the complete
final-certificate assembly payload.
-/
def finalCertificateTopologyAssemblyPayload
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    FinalCertificateTopologyAssemblyPayload inputs topology where
  publicStatement :=
    poincare_conjecture_statement_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs topology
  checkedCertificate :=
    completion_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs topology
  nonemptyCertificate :=
    (nonempty_final_certificate_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
      inputs).2 topology
  canonicalTarget :=
    canonical_completion_target_of_finalCertificateMinimalPackageInputs
      inputs (extinction_implies_sphere_of_topology_package topology)
  publicPayload :=
    (project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs topology).2.1
  canonicalPayload :=
    canonical_completion_payload_of_finalCertificateMinimalPackageInputs
      inputs (extinction_implies_sphere_of_topology_package topology)
  completionCriteria :=
    fun witness =>
      completion_criterion_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        witness inputs topology

/--
The topology assembly payload unpacks to the standard public/certificate/
canonical/criterion tuple.
-/
theorem finalCertificateTopologyAssemblyPayload_fields
    (inputs : FinalCertificateMinimalPackageInputs.{u})
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload := finalCertificateTopologyAssemblyPayload inputs topology
  exact
    ⟨ payload.publicStatement
    , payload.checkedCertificate
    , payload.nonemptyCertificate
    , payload.canonicalTarget
    , payload.publicPayload
    , payload.canonicalPayload
    , payload.completionCriteria
    ⟩

/--
Any inhabited final-certificate topology assembly payload is already enough
for downstream final-certificate consumers: it exposes the public Poincare
statement, the checked certificate in inhabited form, the canonical target,
both public and canonical payloads, and the full completion-criterion family.
-/
theorem finalCertificateTopologyAssemblyPayload_fields_of_nonempty
    {inputs : FinalCertificateMinimalPackageInputs.{u}}
    {topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage}
    (payload :
      Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology)) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.publicStatement
    , payload.nonemptyCertificate
    , payload.canonicalTarget
    , payload.publicPayload
    , payload.canonicalPayload
    , payload.completionCriteria
    ⟩

/--
An inhabited final-certificate topology assembly payload is exactly the
concrete public statement, checked completion certificate, inhabited
certificate witness, canonical target, public and canonical completion
payloads, and completion-criterion family it carries.  The reverse direction
rebuilds the assembly payload directly from those endpoint fields, keeping the
checked certificate object rather than only its inhabited wrapper.
-/
theorem nonempty_finalCertificateTopologyAssemblyPayload_iff_endpoint_fields
    {inputs : FinalCertificateMinimalPackageInputs.{u}}
    {topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage} :
    Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology) ↔
      PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.publicStatement
      , payload.checkedCertificate
      , payload.nonemptyCertificate
      , payload.canonicalTarget
      , payload.publicPayload
      , payload.canonicalPayload
      , payload.completionCriteria
      ⟩
  · rintro
      ⟨ publicStatement
      , checkedCertificate
      , nonemptyCertificate
      , canonicalTarget
      , publicPayload
      , canonicalPayload
      , completionCriteria
      ⟩
    exact
      ⟨ { publicStatement := publicStatement
          checkedCertificate := checkedCertificate
          nonemptyCertificate := nonemptyCertificate
          canonicalTarget := canonicalTarget
          publicPayload := publicPayload
          canonicalPayload := canonicalPayload
          completionCriteria := completionCriteria } ⟩

/--
A checked remaining-dependency package plus the simply connected recognition
prefix constructs the generic final-certificate topology assembly payload.  The
remaining-dependency package supplies the smoothability and finite-extinction
package inputs, while the recognition prefix supplies the topology package.
-/
def finalCertificateTopologyAssemblyPayload_of_remainingDependencyPackage_and_recognitionPrefix
    (dependencies : RemainingDependencyPackage.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    FinalCertificateTopologyAssemblyPayload
      (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
        (finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
          dependencies))
      (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
        recognitionPrefix) :=
  finalCertificateTopologyAssemblyPayload
    (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
      (finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
        dependencies))
    (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix)

/--
The remaining-dependency recognition-prefix route exposes the same public
statement, checked certificate, inhabited certificate, canonical target, public
payload, canonical payload, and completion criteria as the generic topology
assembly payload.
-/
theorem finalCertificateTopologyAssemblyPayload_fields_of_remainingDependencyPackage_and_recognitionPrefix
    (dependencies : RemainingDependencyPackage.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) :=
  finalCertificateTopologyAssemblyPayload_fields
    (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
      (finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
        dependencies))
    (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix)

/--
The remaining-dependency recognition-prefix route constructs an inhabited
final-certificate topology assembly payload, not only its unpacked field tuple.
-/
theorem nonempty_finalCertificateTopologyAssemblyPayload_of_remainingDependencyPackage_and_recognitionPrefix
    (dependencies : RemainingDependencyPackage.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    Nonempty
      (FinalCertificateTopologyAssemblyPayload
        (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
          (finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
            dependencies))
        (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
          recognitionPrefix)) :=
  ⟨finalCertificateTopologyAssemblyPayload_of_remainingDependencyPackage_and_recognitionPrefix
    dependencies recognitionPrefix⟩

/--
The same route exposes both the inhabited assembly payload and the standard
public/certificate/canonical/criterion tuple extracted from it.
-/
theorem nonempty_finalCertificateTopologyAssemblyPayload_and_fields_of_remainingDependencyPackage_and_recognitionPrefix
    (dependencies : RemainingDependencyPackage.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    Nonempty
      (FinalCertificateTopologyAssemblyPayload
        (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
          (finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
            dependencies))
        (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
          recognitionPrefix)) ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  exact
    ⟨ nonempty_finalCertificateTopologyAssemblyPayload_of_remainingDependencyPackage_and_recognitionPrefix
        dependencies recognitionPrefix
    , finalCertificateTopologyAssemblyPayload_fields_of_remainingDependencyPackage_and_recognitionPrefix
        dependencies recognitionPrefix
    ⟩

/--
The grounded recognition-prefix route and the generic final-certificate
topology assembly route can be consumed together from the same
remaining-dependency package and recognition prefix.  This endpoint constructs
both inhabited payloads and exposes the topology input, topology extraction
statement, checked certificate, inhabited certificate, canonical target, and
full completion-criterion family.
-/
theorem groundedRecognitionPrefixPayload_and_finalCertificateTopologyAssemblyPayload_route_fields
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    Nonempty
        (GroundedRecognitionPrefixFinalCertificatePayload
          dependencies grounded recognitionPrefix) ∧
      Nonempty
        (FinalCertificateTopologyAssemblyPayload
          (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
            (finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
              dependencies))
          (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
            recognitionPrefix)) ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage ∧
      ExtinctionTopologyExtractionStatement.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let groundedPayload :=
    groundedRecognitionPrefixFinalCertificatePayload
      dependencies grounded recognitionPrefix
  let topologyPayload :=
    finalCertificateTopologyAssemblyPayload_of_remainingDependencyPackage_and_recognitionPrefix
      dependencies recognitionPrefix
  exact
    ⟨ ⟨groundedPayload⟩
    , ⟨topologyPayload⟩
    , groundedPayload.topologyPackage
    , groundedPayload.topologyStatement
    , topologyPayload.publicStatement
    , topologyPayload.checkedCertificate
    , topologyPayload.nonemptyCertificate
    , topologyPayload.canonicalTarget
    , topologyPayload.publicPayload
    , topologyPayload.canonicalPayload
    , topologyPayload.completionCriteria
    ⟩

/--
The grounded recognition-prefix payload and the generic topology-assembly
payload built from the same remaining-dependency package and recognition
prefix carry the same final endpoint fields.  This lets final-collapse
consumers select both payload objects once and use either route for the public
statement, checked certificate, canonical target, public/canonical payloads,
and all completion criteria without rebuilding the topology package boundary.
-/
theorem groundedRecognitionPrefixPayload_topologyAssemblyPayload_selected_endpoint_fields
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    ∃ groundedPayload :
      GroundedRecognitionPrefixFinalCertificatePayload
        dependencies grounded recognitionPrefix,
    ∃ topologyPayload :
      FinalCertificateTopologyAssemblyPayload
        (finalCertificateMinimalPackageInputs_of_finalAssemblyPackageBoundaryInputs
          (finalAssemblyPackageBoundaryInputs_of_remainingDependencyPackage
            dependencies))
        (topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
          recognitionPrefix),
      groundedPayload.topologyPackage =
          topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
            recognitionPrefix ∧
        groundedPayload.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            groundedPayload.topologyPackage ∧
        groundedPayload.publicStatement = topologyPayload.publicStatement ∧
        groundedPayload.checkedCertificate =
          topologyPayload.checkedCertificate ∧
        groundedPayload.canonicalTarget = topologyPayload.canonicalTarget ∧
        groundedPayload.publicPayload = topologyPayload.publicPayload ∧
        groundedPayload.canonicalPayload = topologyPayload.canonicalPayload ∧
        groundedPayload.completionCriteria =
          topologyPayload.completionCriteria ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let groundedPayload :=
    groundedRecognitionPrefixFinalCertificatePayload
      dependencies grounded recognitionPrefix
  let topologyPayload :=
    finalCertificateTopologyAssemblyPayload_of_remainingDependencyPackage_and_recognitionPrefix
      dependencies recognitionPrefix
  exact
    ⟨ groundedPayload
    , topologyPayload
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , topologyPayload.publicStatement
    , topologyPayload.checkedCertificate
    , topologyPayload.nonemptyCertificate
    , topologyPayload.canonicalTarget
    , topologyPayload.publicPayload
    , topologyPayload.canonicalPayload
    , topologyPayload.completionCriteria
    ⟩

/--
The selected grounded recognition-prefix endpoint retains the explicit
project-level and canonical payload routes used to build its fields.  This
keeps the topology input, topology extraction statement, public payload,
canonical payload, checked certificate, and completion-criterion family tied to
the same selected grounded payload instead of forcing final-collapse consumers
to reconstruct the project and canonical routes separately.
-/
theorem groundedRecognitionPrefixPayload_selected_projectCanonical_route_and_completionCriteria
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    ∃ groundedPayload :
      GroundedRecognitionPrefixFinalCertificatePayload
        dependencies grounded recognitionPrefix,
    ∃ topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage,
    ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u},
    ∃ canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u},
      topology =
          topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
            recognitionPrefix ∧
        topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            topology ∧
        groundedPayload.topologyPackage = topology ∧
        groundedPayload.topologyStatement = topologyStatement ∧
        projectPayload =
          project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
            dependencies grounded topologyStatement ∧
        canonicalPayload =
          canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
            dependencies grounded topologyStatement ∧
        projectPayload.1 = groundedPayload.publicStatement ∧
        projectPayload.2.1 = groundedPayload.publicPayload ∧
        projectPayload.2.2 = groundedPayload.checkedCertificate ∧
        canonicalPayload.1 = groundedPayload.canonicalTarget ∧
        canonicalPayload.2.1 = groundedPayload.canonicalPayload ∧
        canonicalPayload.2.2 = groundedPayload.checkedCertificate ∧
        groundedPayload.completionCriteria =
          (fun witness : Type u =>
            canonicalPayload.2.1.choose_spec witness) ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let topology :=
    topologyPackage_requirement_of_simplyConnectedExtinctionRecognitionPrefixPackage
      recognitionPrefix
  let topologyStatement : ExtinctionTopologyExtractionStatement.{u} :=
    extinction_topology_extraction_statement_of_topology_package topology
  let projectPayload :=
    project_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
      dependencies grounded topologyStatement
  let canonicalPayload :=
    canonical_payload_and_final_certificate_of_remainingDependencyPackage_groundedUniversalFiniteExtinctionStatement_and_topologyExtractionStatement
      dependencies grounded topologyStatement
  let groundedPayload :=
    groundedRecognitionPrefixFinalCertificatePayload
      dependencies grounded recognitionPrefix
  exact
    ⟨ groundedPayload
    , topology
    , topologyStatement
    , projectPayload
    , canonicalPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , groundedPayload.publicStatement
    , groundedPayload.checkedCertificate
    , groundedPayload.canonicalTarget
    , groundedPayload.publicPayload
    , groundedPayload.canonicalPayload
    , groundedPayload.completionCriteria
    ⟩

/--
Consumer-facing collapse of the joined grounded recognition-prefix and topology
assembly route: the same inputs produce the public Poincare statement,
inhabited checked certificate, and all completion criteria.
-/
theorem poincare_statement_nonempty_certificate_and_completion_criteria_of_groundedRecognitionPrefix_and_finalCertificateTopologyAssembly
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases
    groundedRecognitionPrefixPayload_and_finalCertificateTopologyAssemblyPayload_route_fields
      dependencies grounded recognitionPrefix with
    ⟨ _groundedPayload
    , _topologyPayload
    , _topologyPackage
    , _topologyStatement
    , publicStatement
    , _checkedCertificate
    , nonemptyCertificate
    , _canonicalTarget
    , _publicPayload
    , _canonicalPayload
    , completionCriteria
    ⟩
  exact
    ⟨ publicStatement
    , nonemptyCertificate
    , completionCriteria
    ⟩

/--
Checked-certificate form of the joined grounded recognition-prefix and topology
assembly route: the same inputs produce the public Poincare statement, the
concrete checked completion certificate, and all completion criteria.
-/
theorem poincare_statement_checked_certificate_and_completion_criteria_of_groundedRecognitionPrefix_and_finalCertificateTopologyAssembly
    (dependencies : RemainingDependencyPackage.{u})
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (recognitionPrefix :
      ExtinctionTopologySimplyConnectedExtinctionRecognitionPrefixPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases
    groundedRecognitionPrefixPayload_and_finalCertificateTopologyAssemblyPayload_route_fields
      dependencies grounded recognitionPrefix with
    ⟨ _groundedPayload
    , _topologyPayload
    , _topologyPackage
    , _topologyStatement
    , publicStatement
    , checkedCertificate
    , _nonemptyCertificate
    , _canonicalTarget
    , _publicPayload
    , _canonicalPayload
    , completionCriteria
    ⟩
  exact
    ⟨ publicStatement
    , checkedCertificate
    , completionCriteria
    ⟩

/--
For fixed smoothability and finite-extinction inputs, existence of the complete
topology assembly payload is exactly the topology-package requirement.  The
reverse direction constructs the checked final certificate and all completion
criteria through `finalCertificateTopologyAssemblyPayload`; the forward
direction exposes the topology witness carried by the existential.
-/
theorem nonempty_finalCertificateTopologyAssemblyPayload_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (∃ topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage,
        Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology)) ↔
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact payload.1
  · intro topology
    exact
      ⟨ topology
      , ⟨finalCertificateTopologyAssemblyPayload inputs topology⟩
      ⟩

/--
For fixed smoothability and finite-extinction inputs, an inhabited topology
assembly payload is equivalent to the final public endpoint tuple: the Poincare
statement, an inhabited checked completion certificate, and the full universe
completion-criterion family.  This collapses the existential assembly payload
surface directly to the consumer-facing final-certificate endpoint while still
keeping the theorem conditional on the topology package boundary.
-/
theorem poincare_statement_nonempty_final_certificate_and_completion_criteria_iff_nonempty_finalCertificateTopologyAssemblyPayload_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      (∃ topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage,
          Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology)) := by
  constructor
  · intro endpoint
    have topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage :=
      (poincare_statement_nonempty_final_certificate_and_completion_criteria_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).1 endpoint
    exact
      (nonempty_finalCertificateTopologyAssemblyPayload_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).2 topology
  · intro payload
    have topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage :=
      (nonempty_finalCertificateTopologyAssemblyPayload_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).1 payload
    exact
      (poincare_statement_nonempty_final_certificate_and_completion_criteria_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).2 topology

/--
For fixed smoothability and finite-extinction inputs, an inhabited topology
assembly payload is also equivalent to the checked-certificate final endpoint:
the public Poincare statement, an actual checked completion certificate, and
the full universe completion-criterion family.  This strengthens the preceding
inhabited-certificate collapse by exposing the concrete checked certificate
carried by the topology assembly route.
-/
theorem poincare_statement_final_certificate_and_completion_criteria_iff_nonempty_finalCertificateTopologyAssemblyPayload_of_finalCertificateMinimalPackageInputs
    (inputs : FinalCertificateMinimalPackageInputs.{u}) :
    (PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      (∃ topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage,
          Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology)) := by
  constructor
  · intro endpoint
    have topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage :=
      (poincare_statement_final_certificate_and_completion_criterion_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).1 endpoint
    exact
      (nonempty_finalCertificateTopologyAssemblyPayload_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).2 topology
  · intro payload
    have topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage :=
      (nonempty_finalCertificateTopologyAssemblyPayload_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).1 payload
    exact
      (poincare_statement_final_certificate_and_completion_criterion_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).2 topology

/--
Exact named-package boundary for the full checked final endpoint: the public
Poincare statement, a concrete checked completion certificate, and all
universe-indexed completion criteria are equivalent to the three package-layer
requirements currently carried by `RemainingDependencyPackage`.
-/
theorem poincare_statement_final_certificate_and_completion_criteria_iff_named_package_layer_requirements :
    (PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · intro endpoint
    exact
      (final_certificate_iff_named_package_layer_requirements).1
        endpoint.2.1
  · rintro ⟨smoothability, finiteExtinction, topology⟩
    let inputs : FinalCertificateMinimalPackageInputs.{u} :=
      { smoothability := smoothability
        finiteExtinction := finiteExtinction }
    exact
      (poincare_statement_final_certificate_and_completion_criterion_iff_topologyPackage_of_finalCertificateMinimalPackageInputs
        inputs).2 topology

/--
Complete consumer payload for the named package-layer final endpoint.  It
retains the three package requirements, the concrete topology assembly payload
they construct, the public statement, checked certificate, canonical target,
both public/canonical completion payloads, and the full completion-criterion
family.
-/
structure FinalCertificateNamedPackageLayerConsumerPayload where
  smoothability :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage
  finiteExtinction :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage
  topology :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.topologyPackage
  topologyAssemblyPayload :
    FinalCertificateTopologyAssemblyPayload
      { smoothability := smoothability
        finiteExtinction := finiteExtinction }
      topology
  publicStatement : PoincareConjectureStatement.{u}
  checkedCertificate : PoincareCompletionCertificate.{u}
  canonicalTarget : canonicalCompletionTarget.{u}
  publicPayload :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness
  canonicalPayload :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness
  completionCriteria :
    ∀ witness : Type u, CompletionCriterionAtUniverse witness

/--
The three named package-layer requirements construct the complete final
consumer payload while retaining the intermediate topology assembly payload
used to produce the checked certificate.
-/
def finalCertificateNamedPackageLayerConsumerPayload
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    FinalCertificateNamedPackageLayerConsumerPayload.{u} := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := smoothability
      finiteExtinction := finiteExtinction }
  let payload := finalCertificateTopologyAssemblyPayload inputs topology
  exact
    { smoothability := smoothability
      finiteExtinction := finiteExtinction
      topology := topology
      topologyAssemblyPayload := payload
      publicStatement := payload.publicStatement
      checkedCertificate := payload.checkedCertificate
      canonicalTarget := payload.canonicalTarget
      publicPayload := payload.publicPayload
      canonicalPayload := payload.canonicalPayload
      completionCriteria := payload.completionCriteria }

/--
The complete named-package consumer payload projects to the final checked
endpoint tuple: public Poincare statement, checked certificate, and all
completion criteria.
-/
theorem poincare_statement_final_certificate_and_completion_criteria_of_namedPackageLayerConsumerPayload
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨ payload.publicStatement
  , payload.checkedCertificate
  , payload.completionCriteria
  ⟩

/--
The same complete named-package consumer payload also supplies the
inhabited-certificate final endpoint used by nonempty-certificate collapse
routes.
-/
theorem poincare_statement_nonempty_certificate_and_completion_criteria_of_namedPackageLayerConsumerPayload
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨ payload.publicStatement
  , ⟨payload.checkedCertificate⟩
  , payload.completionCriteria
  ⟩

/--
The complete named-package consumer payload discharges the reserved public
Poincare statement by projecting through its checked completion certificate.
-/
theorem poincare_conjecture_of_namedPackageLayerConsumerPayload
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_conjecture_of_completion_certificate payload.checkedCertificate

/--
The complete named-package consumer payload exposes the final endpoint through
its checked completion certificate: the public statement component is obtained
by certificate projection, while the concrete checked certificate and all
completion criteria remain the fields carried by the same payload.
-/
theorem poincare_conjecture_certificate_and_completion_criteria_of_namedPackageLayerConsumerPayload
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨ poincare_conjecture_of_namedPackageLayerConsumerPayload payload
  , payload.checkedCertificate
  , payload.completionCriteria
  ⟩

/--
The named-consumer reserved endpoint is exactly the checked-certificate
projection carried by that same consumer payload.
-/
theorem poincare_conjecture_of_namedPackageLayerConsumerPayload_eq
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    poincare_conjecture_of_namedPackageLayerConsumerPayload payload =
      poincare_conjecture_of_completion_certificate
        payload.checkedCertificate := by
  apply Subsingleton.elim

/--
An inhabited complete named-package consumer payload discharges the reserved
public Poincare statement by selecting its checked completion certificate.
-/
theorem poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
    (payload : Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases payload with ⟨payload⟩
  exact poincare_conjecture_of_namedPackageLayerConsumerPayload payload

/--
The complete named-package consumer payload also retains the concrete topology
assembly payload and both the public and canonical completion payloads used to
produce the checked final endpoint.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_topologyAssembly_and_endpoint_fields
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage,
      Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology) ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction }
  exact
    ⟨ inputs
    , payload.topology
    , ⟨payload.topologyAssemblyPayload⟩
    , payload.publicStatement
    , payload.checkedCertificate
    , payload.canonicalTarget
    , payload.publicPayload
    , payload.canonicalPayload
    , payload.completionCriteria
    ⟩

/--
The complete named-package consumer payload exposes all three package-layer
requirements together with the inhabited topology assembly payload and the
checked final endpoint data carried by that same assembly.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_requirements_topologyAssembly_and_checkedEndpoint
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
      ∃ topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage,
        Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology) ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          canonicalCompletionTarget.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction }
  exact
    ⟨ payload.smoothability
    , payload.finiteExtinction
    , inputs
    , payload.topology
    , ⟨payload.topologyAssemblyPayload⟩
    , payload.publicStatement
    , payload.checkedCertificate
    , payload.canonicalTarget
    , payload.completionCriteria
    ⟩

/--
The complete named-package consumer payload also determines the concrete
minimal final-certificate inputs, the old three-input assembly object, and the
remaining-dependency package used by the legacy certificate constructor.  Its
stored checked certificate is the same proposition-level endpoint as that
remaining-dependency certificate route.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_dependency_objects_and_certificate_route
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ _assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
      FinalCertificateTopologyAssemblyPayload inputs payload.topology ∧
        PoincareCompletionCertificate.{u} ∧
        payload.checkedCertificate =
          completion_certificate_of_remaining_dependency_package
            dependencies := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction }
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction
      topology := payload.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  exact
    ⟨ inputs
    , assemblyInputs
    , dependencies
    , payload.topologyAssemblyPayload
    , payload.checkedCertificate
    , by apply Subsingleton.elim
    ⟩

/--
The complete named-package consumer payload ties the remaining-dependency
certificate route to the final checked endpoint: the checked certificate is the
same proposition-level endpoint as the legacy dependency-route certificate, and
the public Poincare statement is the certificate projection from that checked
certificate.  The same witness also carries the canonical target and both
completion-criterion payloads.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_dependency_route_and_certificate_projected_endpoint
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ _assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
      FinalCertificateTopologyAssemblyPayload inputs payload.topology ∧
        payload.checkedCertificate =
          completion_certificate_of_remaining_dependency_package
            dependencies ∧
        PoincareCompletionCertificate.{u} ∧
        PoincareConjectureStatement.{u} ∧
        poincare_conjecture_of_completion_certificate
            payload.checkedCertificate =
          payload.publicStatement ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction }
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction
      topology := payload.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  exact
    ⟨ inputs
    , assemblyInputs
    , dependencies
    , payload.topologyAssemblyPayload
    , by apply Subsingleton.elim
    , payload.checkedCertificate
    , poincare_conjecture_of_completion_certificate payload.checkedCertificate
    , by apply Subsingleton.elim
    , payload.canonicalTarget
    , payload.publicPayload
    , payload.canonicalPayload
    , payload.completionCriteria
    ⟩

/--
The complete named-package consumer payload also exposes the primitive
final-certificate inputs that drive the canonical target/payload route:
universal finite extinction assembled from smoothability and finite extinction,
and the post-extinction sphere extraction supplied by the same topology
package.  The checked certificate is propositionally the one obtained by
feeding those primitive inputs to the remaining-dependency certificate route.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_primitiveInputs_and_certificate_projected_endpoint
    (payload : FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ _assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
      FinalCertificateTopologyAssemblyPayload inputs payload.topology ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package
              payload.topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            payload.smoothability payload.finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package payload.topology ∧
        payload.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} ∧
        PoincareConjectureStatement.{u} ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package payload.topology)
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := payload.smoothability
      finiteExtinction := payload.finiteExtinction
      topology := payload.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  exact
    ⟨ inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , payload.topologyAssemblyPayload
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , payload.canonicalTarget
    , payload.canonicalPayload
    , payload.checkedCertificate
    , poincare_conjecture_of_completion_certificate payload.checkedCertificate
    , payload.completionCriteria
    ⟩

/--
The three named package-layer requirements directly produce the primitive
final-certificate inputs, the remaining-dependency certificate route, and the
certificate-projected endpoint.  This is the caller-facing version of
`finalCertificateNamedPackageLayerConsumerPayload_primitiveInputs_and_certificate_projected_endpoint`:
it constructs the complete consumer payload internally, but still exposes that
payload together with the primitive inputs and checked endpoint fields.
-/
theorem finalCertificateNamedPackageLayerRequirements_primitiveInputs_and_certificate_projected_endpoint
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ payload : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ _assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
      payload.smoothability = smoothability ∧
        payload.finiteExtinction = finiteExtinction ∧
        payload.topology = topology ∧
        FinalCertificateTopologyAssemblyPayload inputs topology ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            smoothability finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package topology ∧
        payload.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} ∧
        PoincareConjectureStatement.{u} ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  rcases
    finalCertificateNamedPackageLayerConsumerPayload_primitiveInputs_and_certificate_projected_endpoint
      payload with
    ⟨ inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , hPrimitiveInputs
    , hUniversalFiniteExtinction
    , hExtinctionImpliesSphere
    , hCertificate
    , canonicalTarget
    , canonicalPayload
    , checkedCertificate
    , publicStatement
    , completionCriteria
    ⟩
  exact
    ⟨ payload
    , inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , rfl
    , rfl
    , rfl
    , topologyAssemblyPayload
    , hPrimitiveInputs
    , hUniversalFiniteExtinction
    , hExtinctionImpliesSphere
    , hCertificate
    , canonicalTarget
    , canonicalPayload
    , checkedCertificate
    , publicStatement
    , completionCriteria
    ⟩

/--
The named package-layer requirements also discharge any requested completion
criterion through the same primitive-input certificate route.  This keeps the
complete consumer payload, primitive inputs, remaining-dependency certificate,
certificate-projected public statement, and the witness-specific completion
criterion tied to one constructed endpoint.
-/
theorem finalCertificateNamedPackageLayerRequirements_primitiveInputs_certificate_projected_endpoint_and_completionCriterion
    (witness : Type u)
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ payload : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ _assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
      payload.smoothability = smoothability ∧
        payload.finiteExtinction = finiteExtinction ∧
        payload.topology = topology ∧
        FinalCertificateTopologyAssemblyPayload inputs topology ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            smoothability finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package topology ∧
        payload.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        poincare_conjecture_of_completion_certificate
            payload.checkedCertificate =
          payload.publicStatement ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} ∧
        PoincareConjectureStatement.{u} ∧
        CompletionCriterionAtUniverse witness := by
  let payload :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  rcases
    finalCertificateNamedPackageLayerConsumerPayload_primitiveInputs_and_certificate_projected_endpoint
      payload with
    ⟨ inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , hPrimitiveInputs
    , hUniversalFiniteExtinction
    , hExtinctionImpliesSphere
    , hCertificate
    , canonicalTarget
    , canonicalPayload
    , _checkedCertificate
    , _publicStatement
    , completionCriteria
    ⟩
  exact
    ⟨ payload
    , inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , rfl
    , rfl
    , rfl
    , topologyAssemblyPayload
    , hPrimitiveInputs
    , hUniversalFiniteExtinction
    , hExtinctionImpliesSphere
    , hCertificate
    , by apply Subsingleton.elim
    , canonicalTarget
    , payload.publicPayload
    , canonicalPayload
    , payload.checkedCertificate
    , poincare_conjecture_of_completion_certificate payload.checkedCertificate
    , completionCriteria witness
    ⟩

/--
The three named package-layer requirements directly produce the
remaining-dependency certificate route and the certificate-projected final
endpoint.  This is the consumer-facing form of
`finalCertificateNamedPackageLayerConsumerPayload_dependency_route_and_certificate_projected_endpoint`:
it constructs the complete named-package consumer payload internally and then
exposes the dependency-route certificate, public statement, canonical target,
and completion criteria without requiring callers to name the payload first.
-/
theorem finalCertificateNamedPackageLayerRequirements_dependency_route_and_certificate_projected_endpoint
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ _assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
      FinalCertificateTopologyAssemblyPayload inputs topology ∧
        ∃ checkedCertificate : PoincareCompletionCertificate.{u},
        checkedCertificate =
          completion_certificate_of_remaining_dependency_package
            dependencies ∧
        ∃ publicStatement : PoincareConjectureStatement.{u},
        poincare_conjecture_of_completion_certificate
            (completion_certificate_of_remaining_dependency_package
              dependencies) =
          publicStatement ∧
          canonicalCompletionTarget.{u} ∧
          (∃ _target : PoincareConjectureStatement.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ _target : canonicalCompletionTarget.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  rcases
    finalCertificateNamedPackageLayerConsumerPayload_dependency_route_and_certificate_projected_endpoint
      payload with
    ⟨ inputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , hCertificateRoute
    , checkedCertificate
    , _publicStatement
    , _hPublicStatement
    , canonicalTarget
    , publicPayload
    , canonicalPayload
    , completionCriteria
    ⟩
  exact
    ⟨ inputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , checkedCertificate
    , hCertificateRoute
    , poincare_conjecture_of_completion_certificate
        (completion_certificate_of_remaining_dependency_package
          dependencies)
    , by apply Subsingleton.elim
    , canonicalTarget
    , publicPayload
    , canonicalPayload
    , completionCriteria
    ⟩

/--
The three named package-layer requirements construct both concrete final
consumer objects used by the endpoint: the complete named-package consumer
payload and the topology-assembly payload for the corresponding minimal
package inputs.  This exposes the checked public statement, concrete checked
certificate, inhabited certificate, canonical target, and completion criteria
from both constructed objects without requiring downstream callers to rebuild
or unpack either constructor.
-/
theorem finalCertificateNamedPackageLayerRequirements_consumerPayload_topologyAssembly_and_checkedEndpoint
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ payload : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ _topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload
        { smoothability := smoothability
          finiteExtinction := finiteExtinction }
        topology,
      payload.smoothability = smoothability ∧
        payload.finiteExtinction = finiteExtinction ∧
        payload.topology = topology ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload
        { smoothability := smoothability
          finiteExtinction := finiteExtinction }
        topology :=
    finalCertificateTopologyAssemblyPayload
      { smoothability := smoothability
        finiteExtinction := finiteExtinction }
      topology
  exact
    ⟨ payload
    , topologyAssemblyPayload
    , rfl
    , rfl
    , rfl
    , topologyAssemblyPayload.publicStatement
    , topologyAssemblyPayload.checkedCertificate
    , topologyAssemblyPayload.nonemptyCertificate
    , topologyAssemblyPayload.canonicalTarget
    , topologyAssemblyPayload.publicPayload
    , topologyAssemblyPayload.canonicalPayload
    , topologyAssemblyPayload.completionCriteria
    , payload.publicStatement
    , payload.checkedCertificate
    , ⟨payload.checkedCertificate⟩
    , payload.canonicalTarget
    , payload.publicPayload
    , payload.canonicalPayload
    , payload.completionCriteria
    ⟩

/--
The inhabited complete named-package consumer payload exposes all three
package-layer requirements, the inhabited topology assembly payload, and the
checked final endpoint data carried by the selected payload.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_requirements_topologyAssembly_and_checkedEndpoint_of_nonempty
    (payload : Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
      ∃ topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage,
        Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology) ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          canonicalCompletionTarget.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨payload⟩
  exact
    finalCertificateNamedPackageLayerConsumerPayload_requirements_topologyAssembly_and_checkedEndpoint
      payload

/--
An inhabited named-package final consumer payload can be selected once and then
used as a complete final endpoint: the selected payload exposes all three
package-layer requirements, its public statement as the checked-certificate
projection, the concrete checked certificate, its inhabited form, the canonical
target, both public/canonical completion payloads, and all completion criteria.
This keeps downstream final-collapse code from separately combining the
nonempty consumer equivalence with the certificate-projection theorem.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_selected_projected_endpoint_fields_of_nonempty
    (payload : Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
      dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage ∧
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage ∧
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨selected⟩
  exact
    ⟨ selected
    , selected.smoothability
    , selected.finiteExtinction
    , selected.topology
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria
    ⟩

/--
Equivalently, the three named package-layer requirements construct an inhabited
complete final consumer payload.
-/
theorem nonempty_finalCertificateNamedPackageLayerConsumerPayload_of_named_package_layer_requirements
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} :=
  ⟨finalCertificateNamedPackageLayerConsumerPayload
    smoothability finiteExtinction topology⟩

/--
The complete final consumer payload is equivalent to the named package-layer
requirements: it stores the three package witnesses in one direction, and the
reverse direction constructs the checked topology-assembly consumer payload.
-/
theorem nonempty_finalCertificateNamedPackageLayerConsumerPayload_iff_named_package_layer_requirements :
    Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.smoothability
      , payload.finiteExtinction
      , payload.topology
      ⟩
  · rintro ⟨smoothability, finiteExtinction, topology⟩
    exact
      nonempty_finalCertificateNamedPackageLayerConsumerPayload_of_named_package_layer_requirements
        smoothability finiteExtinction topology

/--
The complete final named-package consumer payload is exactly the three named
package-layer requirements together with a concrete topology-assembly payload
and the checked endpoint fields.  The reverse direction rebuilds the complete
consumer payload from those fields without reopening the package constructors.
-/
theorem nonempty_finalCertificateNamedPackageLayerConsumerPayload_iff_requirements_topologyAssembly_and_endpoint_fields :
    Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} ↔
      ∃ smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
      ∃ topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage,
      ∃ _topologyAssemblyPayload :
        FinalCertificateTopologyAssemblyPayload
          { smoothability := smoothability
            finiteExtinction := finiteExtinction }
          topology,
        PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          canonicalCompletionTarget.{u} ∧
          (∃ _target : PoincareConjectureStatement.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ _target : canonicalCompletionTarget.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.smoothability
      , payload.finiteExtinction
      , payload.topology
      , payload.topologyAssemblyPayload
      , payload.publicStatement
      , payload.checkedCertificate
      , payload.canonicalTarget
      , payload.publicPayload
      , payload.canonicalPayload
      , payload.completionCriteria
      ⟩
  · rintro
      ⟨ smoothability
      , finiteExtinction
      , topology
      , topologyAssemblyPayload
      , publicStatement
      , checkedCertificate
      , canonicalTarget
      , publicPayload
      , canonicalPayload
      , completionCriteria
      ⟩
    exact
      ⟨ { smoothability := smoothability
          finiteExtinction := finiteExtinction
          topology := topology
          topologyAssemblyPayload := topologyAssemblyPayload
          publicStatement := publicStatement
          checkedCertificate := checkedCertificate
          canonicalTarget := canonicalTarget
          publicPayload := publicPayload
          canonicalPayload := canonicalPayload
          completionCriteria := completionCriteria } ⟩

/--
Final checked endpoint through the complete consumer payload: the public
Poincare statement, a concrete checked completion certificate, and all
completion criteria are equivalent to inhabiting the named-package consumer
payload.
-/
theorem poincare_statement_final_certificate_and_completion_criteria_iff_nonempty_namedPackageLayerConsumerPayload :
    (PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} := by
  constructor
  · intro endpoint
    have requirements :
        ∃ _smoothability :
          dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.smoothabilityPackage,
        ∃ _finiteExtinction :
          dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.finiteExtinctionPackage,
          dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.topologyPackage :=
      (poincare_statement_final_certificate_and_completion_criteria_iff_named_package_layer_requirements).1
        endpoint
    exact
      nonempty_finalCertificateNamedPackageLayerConsumerPayload_iff_named_package_layer_requirements.2
        requirements
  · intro payload
    rcases payload with ⟨payload⟩
    exact
      poincare_statement_final_certificate_and_completion_criteria_of_namedPackageLayerConsumerPayload
        payload

/--
Inhabited-certificate final endpoint through the complete consumer payload:
the public Poincare statement, an inhabited checked completion certificate, and
all completion criteria are equivalent to inhabiting the named-package consumer
payload.
-/
theorem poincare_statement_nonempty_certificate_and_completion_criteria_iff_nonempty_namedPackageLayerConsumerPayload :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} := by
  constructor
  · rintro ⟨statement, ⟨certificate⟩, completionCriteria⟩
    exact
      poincare_statement_final_certificate_and_completion_criteria_iff_nonempty_namedPackageLayerConsumerPayload.1
        ⟨statement, certificate, completionCriteria⟩
  · rintro ⟨payload⟩
    exact
      poincare_statement_nonempty_certificate_and_completion_criteria_of_namedPackageLayerConsumerPayload
        payload

/--
Inhabited-certificate final endpoint directly through the named package-layer
requirements: the public Poincare statement, an inhabited checked completion
certificate, and all completion criteria are equivalent to the three named
package-layer requirements.
-/
theorem poincare_statement_nonempty_certificate_and_completion_criteria_iff_named_package_layer_requirements :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · rintro ⟨statement, ⟨certificate⟩, completionCriteria⟩
    exact
      (poincare_statement_final_certificate_and_completion_criteria_iff_named_package_layer_requirements).1
        ⟨statement, certificate, completionCriteria⟩
  · intro requirements
    rcases
      (poincare_statement_final_certificate_and_completion_criteria_iff_named_package_layer_requirements).2
        requirements with
      ⟨statement, certificate, completionCriteria⟩
    exact ⟨statement, ⟨certificate⟩, completionCriteria⟩

/--
The inhabited-certificate final endpoint is equivalent to the fully explicit
named-package field package: three package-layer requirements, a concrete
topology-assembly payload, and the checked public/canonical endpoint fields.
-/
theorem poincare_statement_nonempty_certificate_and_completion_criteria_iff_requirements_topologyAssembly_and_endpoint_fields :
    (PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      ∃ smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
      ∃ topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage,
      ∃ _topologyAssemblyPayload :
        FinalCertificateTopologyAssemblyPayload
          { smoothability := smoothability
            finiteExtinction := finiteExtinction }
          topology,
        PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          canonicalCompletionTarget.{u} ∧
          (∃ _target : PoincareConjectureStatement.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ _target : canonicalCompletionTarget.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  constructor
  · intro endpoint
    exact
      nonempty_finalCertificateNamedPackageLayerConsumerPayload_iff_requirements_topologyAssembly_and_endpoint_fields.1
        ((poincare_statement_nonempty_certificate_and_completion_criteria_iff_nonempty_namedPackageLayerConsumerPayload).1
          endpoint)
  · intro fieldPackage
    exact
      (poincare_statement_nonempty_certificate_and_completion_criteria_iff_nonempty_namedPackageLayerConsumerPayload).2
        (nonempty_finalCertificateNamedPackageLayerConsumerPayload_iff_requirements_topologyAssembly_and_endpoint_fields.2
          fieldPackage)

/--
The concrete-certificate final endpoint is equivalent to the same explicit
named-package field package.  This keeps the checked certificate object, rather
than only its inhabited wrapper, connected directly to the three package-layer
requirements and topology-assembly endpoint fields.
-/
theorem poincare_statement_final_certificate_and_completion_criteria_iff_requirements_topologyAssembly_and_endpoint_fields :
    (PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      ∃ smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
      ∃ topology :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage,
      ∃ _topologyAssemblyPayload :
        FinalCertificateTopologyAssemblyPayload
          { smoothability := smoothability
            finiteExtinction := finiteExtinction }
          topology,
        PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          canonicalCompletionTarget.{u} ∧
          (∃ _target : PoincareConjectureStatement.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ _target : canonicalCompletionTarget.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  constructor
  · intro endpoint
    exact
      nonempty_finalCertificateNamedPackageLayerConsumerPayload_iff_requirements_topologyAssembly_and_endpoint_fields.1
        ((poincare_statement_final_certificate_and_completion_criteria_iff_nonempty_namedPackageLayerConsumerPayload).1
          endpoint)
  · intro fieldPackage
    exact
      (poincare_statement_final_certificate_and_completion_criteria_iff_nonempty_namedPackageLayerConsumerPayload).2
        (nonempty_finalCertificateNamedPackageLayerConsumerPayload_iff_requirements_topologyAssembly_and_endpoint_fields.2
          fieldPackage)

/--
An inhabited complete final consumer payload can be selected once and collapsed
to a fixed-witness endpoint: the selected payload retains the concrete topology
assembly object, the reserved public statement obtained from the nonempty
consumer route is identified with the selected checked-certificate projection,
and the same selected payload supplies the requested completion criterion.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_selected_reserved_endpoint_topologyAssembly_and_completionCriterion_of_nonempty
    (payload : Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u})
    (witness : Type u) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage,
      selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        selected.topology = topology ∧
        Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology) ∧
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
            payload =
          selected.publicStatement ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        CompletionCriterionAtUniverse witness := by
  rcases payload with ⟨selected⟩
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  exact
    ⟨ selected
    , inputs
    , selected.topology
    , rfl
    , rfl
    , rfl
    , ⟨selected.topologyAssemblyPayload⟩
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria witness
    ⟩

/--
The same selected complete final consumer payload exposes the full
universe-indexed completion-criteria family, not only one requested witness.
This is the all-witness final endpoint for downstream consumers that select an
inhabited named-package payload once and then need the checked certificate,
reserved public statement route, topology assembly object, and every
completion criterion together.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_selected_reserved_endpoint_topologyAssembly_and_completionCriteria_of_nonempty
    (payload : Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage,
      selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        selected.topology = topology ∧
        Nonempty (FinalCertificateTopologyAssemblyPayload inputs topology) ∧
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
            payload =
          selected.publicStatement ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨selected⟩
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  exact
    ⟨ selected
    , inputs
    , selected.topology
    , rfl
    , rfl
    , rfl
    , ⟨selected.topologyAssemblyPayload⟩
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria
    ⟩

/--
The selected complete final consumer payload also retains the primitive
certificate route that builds the checked certificate from the minimal package
inputs, primitive finite-extinction input, and remaining-dependency package.
This is the selected endpoint used by the final collapse when downstream code
needs the concrete topology-assembly payload fields and the all-witness
completion criteria tied to the same chosen consumer.
-/
theorem finalCertificateNamedPackageLayerConsumerPayload_selected_primitive_certificate_route_and_completionCriteria_of_nonempty
    (payload : Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u}) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
    ∃ topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology,
      selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        assemblyInputs.smoothability = selected.smoothability ∧
        assemblyInputs.finiteExtinction = selected.finiteExtinction ∧
        assemblyInputs.topology = selected.topology ∧
        dependencies =
          remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
            assemblyInputs ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package
              selected.topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            selected.smoothability selected.finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package selected.topology ∧
        selected.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
            payload =
          selected.publicStatement ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        topologyAssemblyPayload.publicStatement =
          selected.publicStatement ∧
        topologyAssemblyPayload.checkedCertificate =
          selected.checkedCertificate ∧
        topologyAssemblyPayload.canonicalTarget =
          selected.canonicalTarget ∧
        topologyAssemblyPayload.publicPayload =
          selected.publicPayload ∧
        topologyAssemblyPayload.canonicalPayload =
          selected.canonicalPayload ∧
        topologyAssemblyPayload.completionCriteria =
          selected.completionCriteria ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨selected⟩
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction
      topology := selected.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  exact
    ⟨ selected
    , inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria
    ⟩

/--
The three named package-layer requirements select the same primitive
certificate route as the complete-consumer theorem, but specialize the
completion-criteria family to one requested witness.  This is the fixed-witness
final-collapse endpoint that still retains the selected consumer, primitive
inputs, remaining-dependency certificate route, and topology-assembly field
equalities.
-/
theorem finalCertificateNamedPackageLayerRequirements_selected_primitive_certificate_route_and_completionCriterion
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (witness : Type u) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
    ∃ topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology,
      selected.smoothability = smoothability ∧
        selected.finiteExtinction = finiteExtinction ∧
        selected.topology = topology ∧
        selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        assemblyInputs.smoothability = selected.smoothability ∧
        assemblyInputs.finiteExtinction = selected.finiteExtinction ∧
        assemblyInputs.topology = selected.topology ∧
        dependencies =
          remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
            assemblyInputs ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package
              selected.topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            selected.smoothability selected.finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package selected.topology ∧
        selected.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
            ⟨selected⟩ =
          selected.publicStatement ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        topologyAssemblyPayload.publicStatement =
          selected.publicStatement ∧
        topologyAssemblyPayload.checkedCertificate =
          selected.checkedCertificate ∧
        topologyAssemblyPayload.canonicalTarget =
          selected.canonicalTarget ∧
        topologyAssemblyPayload.publicPayload =
          selected.publicPayload ∧
        topologyAssemblyPayload.canonicalPayload =
          selected.canonicalPayload ∧
        topologyAssemblyPayload.completionCriteria =
          selected.completionCriteria ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        CompletionCriterionAtUniverse witness := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction
      topology := selected.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  exact
    ⟨ selected
    , inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria witness
    ⟩

/--
The three named package-layer requirements also expose the all-witness
primitive certificate route directly.  This is the requirements-level companion
to the selected complete-consumer endpoint: the same selected consumer retains
the minimal inputs, primitive finite-extinction input, remaining-dependency
certificate constructor, topology-assembly field equalities, checked
certificate, public payloads, and every completion criterion.
-/
theorem finalCertificateNamedPackageLayerRequirements_selected_primitive_certificate_route_and_completionCriteria
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
    ∃ topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology,
      selected.smoothability = smoothability ∧
        selected.finiteExtinction = finiteExtinction ∧
        selected.topology = topology ∧
        selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        assemblyInputs.smoothability = selected.smoothability ∧
        assemblyInputs.finiteExtinction = selected.finiteExtinction ∧
        assemblyInputs.topology = selected.topology ∧
        dependencies =
          remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
            assemblyInputs ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package
              selected.topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            selected.smoothability selected.finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package selected.topology ∧
        selected.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
            ⟨selected⟩ =
          selected.publicStatement ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        topologyAssemblyPayload.publicStatement =
          selected.publicStatement ∧
        topologyAssemblyPayload.checkedCertificate =
          selected.checkedCertificate ∧
        topologyAssemblyPayload.canonicalTarget =
          selected.canonicalTarget ∧
        topologyAssemblyPayload.publicPayload =
          selected.publicPayload ∧
        topologyAssemblyPayload.canonicalPayload =
          selected.canonicalPayload ∧
        topologyAssemblyPayload.completionCriteria =
          selected.completionCriteria ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction
      topology := selected.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  exact
    ⟨ selected
    , inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria
    ⟩

/--
The three named package-layer requirements select the concrete constructed
final consumer payload, not just an existentially equivalent one, while exposing
the same all-witness primitive certificate route.  This endpoint keeps the
constructor identity, inhabited consumer payload, primitive inputs,
remaining-dependency package, topology-assembly field equalities, checked
certificate, public payloads, and every completion criterion synchronized for
the final collapse.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_selected_primitive_certificate_route_and_completionCriteria
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
    ∃ topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology,
      selected =
          finalCertificateNamedPackageLayerConsumerPayload
            smoothability finiteExtinction topology ∧
        Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} ∧
        selected.smoothability = smoothability ∧
        selected.finiteExtinction = finiteExtinction ∧
        selected.topology = topology ∧
        selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        assemblyInputs.smoothability = selected.smoothability ∧
        assemblyInputs.finiteExtinction = selected.finiteExtinction ∧
        assemblyInputs.topology = selected.topology ∧
        dependencies =
          remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
            assemblyInputs ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package
              selected.topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            selected.smoothability selected.finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package selected.topology ∧
        selected.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
            ⟨selected⟩ =
          selected.publicStatement ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        topologyAssemblyPayload.publicStatement =
          selected.publicStatement ∧
        topologyAssemblyPayload.checkedCertificate =
          selected.checkedCertificate ∧
        topologyAssemblyPayload.canonicalTarget =
          selected.canonicalTarget ∧
        topologyAssemblyPayload.publicPayload =
          selected.publicPayload ∧
        topologyAssemblyPayload.canonicalPayload =
          selected.canonicalPayload ∧
        topologyAssemblyPayload.completionCriteria =
          selected.completionCriteria ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction
      topology := selected.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  exact
    ⟨ selected
    , inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , rfl
    , ⟨selected⟩
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria
    ⟩

/--
The constructed final consumer also retains the project-level and canonical
payload routes that feed the reserved endpoint.  This keeps the named
constructor, primitive certificate route, project payload, canonical payload,
checked certificate, and all completion criteria synchronized for downstream
final-collapse consumers.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_projectCanonical_primitive_route_and_completionCriteria
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u},
    ∃ dependencies : RemainingDependencyPackage.{u},
    ∃ topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology,
    ∃ projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u},
    ∃ canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u},
      selected =
          finalCertificateNamedPackageLayerConsumerPayload
            smoothability finiteExtinction topology ∧
        Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} ∧
        selected.smoothability = smoothability ∧
        selected.finiteExtinction = finiteExtinction ∧
        selected.topology = topology ∧
        selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        assemblyInputs.smoothability = selected.smoothability ∧
        assemblyInputs.finiteExtinction = selected.finiteExtinction ∧
        assemblyInputs.topology = selected.topology ∧
        dependencies =
          remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
            assemblyInputs ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package
              selected.topology) ∧
        selected.checkedCertificate =
          completion_certificate_of_remainingDependencyPackage_and_finalCertificatePrimitiveInputs
            dependencies primitiveInputs ∧
        projectPayload =
          project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
            inputs selected.topology ∧
        canonicalPayload =
          canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
            selected.smoothability selected.finiteExtinction selected.topology ∧
        projectPayload.1 = selected.publicStatement ∧
        projectPayload.2.1 = selected.publicPayload ∧
        projectPayload.2.2 = selected.checkedCertificate ∧
        canonicalPayload.1 = selected.canonicalTarget ∧
        canonicalPayload.2.1 = selected.canonicalPayload ∧
        canonicalPayload.2.2 = selected.checkedCertificate ∧
        topologyAssemblyPayload.publicStatement =
          selected.publicStatement ∧
        topologyAssemblyPayload.checkedCertificate =
          selected.checkedCertificate ∧
        topologyAssemblyPayload.canonicalTarget =
          selected.canonicalTarget ∧
        topologyAssemblyPayload.publicPayload =
          selected.publicPayload ∧
        topologyAssemblyPayload.canonicalPayload =
          selected.canonicalPayload ∧
        topologyAssemblyPayload.completionCriteria =
          selected.completionCriteria ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  let assemblyInputs : FinalAssemblyPackageBoundaryInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction
      topology := selected.topology }
  let dependencies : RemainingDependencyPackage.{u} :=
    remainingDependencyPackage_of_finalAssemblyPackageBoundaryInputs
      assemblyInputs
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  let projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs selected.topology
  let canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
      selected.smoothability selected.finiteExtinction selected.topology
  exact
    ⟨ selected
    , inputs
    , primitiveInputs
    , assemblyInputs
    , dependencies
    , topologyAssemblyPayload
    , projectPayload
    , canonicalPayload
    , rfl
    , ⟨selected⟩
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.publicPayload
    , selected.canonicalPayload
    , selected.completionCriteria
    ⟩

/--
For the constructed named-package consumer, the primitive final-certificate
inputs obtained from the selected smoothability, finite-extinction, and
topology package fields feed the named final assembly theorems directly.  This
records that the selected reserved public statement is the same statement
obtained by applying the final assembly layer to those primitive inputs, while
retaining the checked certificate and all completion criteria from the same
consumer.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_primitive_finalAssembly_routes
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    let selected :=
      finalCertificateNamedPackageLayerConsumerPayload
        smoothability finiteExtinction topology
    let inputs : FinalCertificateMinimalPackageInputs.{u} :=
      { smoothability := selected.smoothability
        finiteExtinction := selected.finiteExtinction }
    let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
      finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
        (extinction_implies_sphere_of_topology_package selected.topology)
    primitiveInputs.universalFiniteExtinction =
        universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
          selected.smoothability selected.finiteExtinction ∧
      primitiveInputs.extinctionImpliesSphere =
        extinction_implies_sphere_of_topology_package selected.topology ∧
      poincare_statement_of_extinction_and_extraction
          primitiveInputs.universalFiniteExtinction
          primitiveInputs.extinctionImpliesSphere =
        selected.publicStatement ∧
      poincare_conjecture_of_extinction_and_extraction
          primitiveInputs.universalFiniteExtinction
          primitiveInputs.extinctionImpliesSphere =
        selected.publicStatement ∧
      selected.publicStatement =
        poincare_conjecture_of_completion_certificate
          selected.checkedCertificate ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  exact
    ⟨ rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , selected.completionCriteria
    ⟩

/--
For the constructed named-package consumer, the project payload statement, the
nonempty-consumer endpoint, and the checked-certificate endpoint are the same
reserved public statement.  The same fixed consumer also identifies the public
and canonical checked-certificate fields and retains the all-witness completion
criteria used by the final collapse.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_reserved_endpoint_projectCanonical_consistency
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    let selected :=
      finalCertificateNamedPackageLayerConsumerPayload
        smoothability finiteExtinction topology
    let inputs : FinalCertificateMinimalPackageInputs.{u} :=
      { smoothability := selected.smoothability
        finiteExtinction := selected.finiteExtinction }
    let projectPayload :
        PoincareConjectureStatement.{u} ∧
          (∃ _target : PoincareConjectureStatement.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          PoincareCompletionCertificate.{u} :=
      project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs selected.topology
    let canonicalPayload :
        canonicalCompletionTarget.{u} ∧
          (∃ _target : canonicalCompletionTarget.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          PoincareCompletionCertificate.{u} :=
      canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        selected.smoothability selected.finiteExtinction selected.topology
    projectPayload.1 =
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
          ⟨selected⟩ ∧
      projectPayload.1 =
        poincare_conjecture_of_completion_certificate
          selected.checkedCertificate ∧
      projectPayload.2.2 = selected.checkedCertificate ∧
      canonicalPayload.2.2 = selected.checkedCertificate ∧
      projectPayload.2.2 = canonicalPayload.2.2 ∧
      projectPayload.2.1 = selected.publicPayload ∧
      canonicalPayload.2.1 = selected.canonicalPayload ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  dsimp
  exact
    ⟨ by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , (finalCertificateNamedPackageLayerConsumerPayload
        smoothability finiteExtinction topology).completionCriteria
    ⟩

/--
For the constructed named-package consumer, the selected public statement is
the same endpoint reached by the nonempty-consumer route, the project payload,
and the checked-certificate route.  The same selected consumer also retains the
concrete checked certificate, inhabited consumer package, public/canonical
payload fields, and all completion criteria.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_selected_reserved_endpoint_all_routes
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    let selected :=
      finalCertificateNamedPackageLayerConsumerPayload
        smoothability finiteExtinction topology
    let inputs : FinalCertificateMinimalPackageInputs.{u} :=
      { smoothability := selected.smoothability
        finiteExtinction := selected.finiteExtinction }
    let projectPayload :
        PoincareConjectureStatement.{u} ∧
          (∃ _target : PoincareConjectureStatement.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          PoincareCompletionCertificate.{u} :=
      project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs selected.topology
    let canonicalPayload :
        canonicalCompletionTarget.{u} ∧
          (∃ _target : canonicalCompletionTarget.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          PoincareCompletionCertificate.{u} :=
      canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        selected.smoothability selected.finiteExtinction selected.topology
    selected.publicStatement =
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
          ⟨selected⟩ ∧
      selected.publicStatement =
        poincare_conjecture_of_completion_certificate
          selected.checkedCertificate ∧
      projectPayload.1 = selected.publicStatement ∧
      projectPayload.2.1 = selected.publicPayload ∧
      projectPayload.2.2 = selected.checkedCertificate ∧
      canonicalPayload.1 = selected.canonicalTarget ∧
      canonicalPayload.2.1 = selected.canonicalPayload ∧
      canonicalPayload.2.2 = selected.checkedCertificate ∧
      Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs selected.topology
  let canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
      selected.smoothability selected.finiteExtinction selected.topology
  exact
    ⟨ by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , ⟨selected⟩
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.completionCriteria
    ⟩

/--
For the constructed named-package consumer, the selected reserved endpoint can
be used together with the concrete topology-assembly payload fields.  This
single endpoint retains the public/canonical route equalities, the checked
certificate route, the topology-assembly projections, and the all-witness
completion criteria from the same selected consumer.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_selected_reserved_endpoint_all_routes_and_topologyAssembly_fields
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    let selected :=
      finalCertificateNamedPackageLayerConsumerPayload
        smoothability finiteExtinction topology
    let inputs : FinalCertificateMinimalPackageInputs.{u} :=
      { smoothability := selected.smoothability
        finiteExtinction := selected.finiteExtinction }
    let topologyAssemblyPayload :
        FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
      selected.topologyAssemblyPayload
    let projectPayload :
        PoincareConjectureStatement.{u} ∧
          (∃ _target : PoincareConjectureStatement.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          PoincareCompletionCertificate.{u} :=
      project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs selected.topology
    let canonicalPayload :
        canonicalCompletionTarget.{u} ∧
          (∃ _target : canonicalCompletionTarget.{u},
            ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          PoincareCompletionCertificate.{u} :=
      canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        selected.smoothability selected.finiteExtinction selected.topology
    topologyAssemblyPayload.publicStatement =
        selected.publicStatement ∧
      topologyAssemblyPayload.checkedCertificate =
        selected.checkedCertificate ∧
      topologyAssemblyPayload.canonicalTarget =
        selected.canonicalTarget ∧
      topologyAssemblyPayload.publicPayload =
        selected.publicPayload ∧
      topologyAssemblyPayload.canonicalPayload =
        selected.canonicalPayload ∧
      topologyAssemblyPayload.completionCriteria =
        selected.completionCriteria ∧
      selected.publicStatement =
        poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
          ⟨selected⟩ ∧
      selected.publicStatement =
        poincare_conjecture_of_completion_certificate
          selected.checkedCertificate ∧
      projectPayload.1 = selected.publicStatement ∧
      projectPayload.2.1 = selected.publicPayload ∧
      projectPayload.2.2 = selected.checkedCertificate ∧
      canonicalPayload.1 = selected.canonicalTarget ∧
      canonicalPayload.2.1 = selected.canonicalPayload ∧
      canonicalPayload.2.2 = selected.checkedCertificate ∧
      Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      canonicalCompletionTarget.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  let projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs selected.topology
  let canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
      selected.smoothability selected.finiteExtinction selected.topology
  exact
    ⟨ by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , ⟨selected⟩
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.completionCriteria
    ⟩

/--
For the constructed named-package consumer, the primitive final-assembly route
and the concrete topology-assembly payload fields are retained together.  This
keeps the primitive universal finite-extinction and extraction inputs,
project-level final assembly statement, checked certificate, public/canonical
payload fields, and all-witness completion criteria synchronized at the same
selected consumer.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_primitive_finalAssembly_routes_and_topologyAssembly_fields
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    let selected :=
      finalCertificateNamedPackageLayerConsumerPayload
        smoothability finiteExtinction topology
    let inputs : FinalCertificateMinimalPackageInputs.{u} :=
      { smoothability := selected.smoothability
        finiteExtinction := selected.finiteExtinction }
    let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
      finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
        (extinction_implies_sphere_of_topology_package selected.topology)
    let topologyAssemblyPayload :
        FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
      selected.topologyAssemblyPayload
    primitiveInputs.universalFiniteExtinction =
        universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
          selected.smoothability selected.finiteExtinction ∧
      primitiveInputs.extinctionImpliesSphere =
        extinction_implies_sphere_of_topology_package selected.topology ∧
      poincare_statement_of_extinction_and_extraction
          primitiveInputs.universalFiniteExtinction
          primitiveInputs.extinctionImpliesSphere =
        selected.publicStatement ∧
      poincare_conjecture_of_extinction_and_extraction
          primitiveInputs.universalFiniteExtinction
          primitiveInputs.extinctionImpliesSphere =
        selected.publicStatement ∧
      topologyAssemblyPayload.publicStatement =
        selected.publicStatement ∧
      topologyAssemblyPayload.checkedCertificate =
        selected.checkedCertificate ∧
      topologyAssemblyPayload.canonicalTarget =
        selected.canonicalTarget ∧
      topologyAssemblyPayload.publicPayload =
        selected.publicPayload ∧
      topologyAssemblyPayload.canonicalPayload =
        selected.canonicalPayload ∧
      topologyAssemblyPayload.completionCriteria =
        selected.completionCriteria ∧
      selected.publicStatement =
        poincare_conjecture_of_completion_certificate
          selected.checkedCertificate ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  exact
    ⟨ rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , selected.completionCriteria
    ⟩

/--
For the constructed named-package consumer, the primitive final-assembly route
and the project/canonical payload routes are retained in one endpoint.  This
keeps the selected consumer, primitive inputs, topology-assembly fields,
project-level payload, canonical payload, checked certificate, and all-witness
completion criteria synchronized for final-collapse consumers.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_projectCanonical_primitive_finalAssembly_routes_and_topologyAssembly_fields
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ selected : FinalCertificateNamedPackageLayerConsumerPayload.{u},
    ∃ inputs : FinalCertificateMinimalPackageInputs.{u},
    ∃ primitiveInputs : FinalCertificatePrimitiveInputs.{u},
    ∃ topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology,
    ∃ projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u},
    ∃ canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u},
      selected =
          finalCertificateNamedPackageLayerConsumerPayload
            smoothability finiteExtinction topology ∧
        Nonempty FinalCertificateNamedPackageLayerConsumerPayload.{u} ∧
        selected.smoothability = smoothability ∧
        selected.finiteExtinction = finiteExtinction ∧
        selected.topology = topology ∧
        selected.smoothability = inputs.smoothability ∧
        selected.finiteExtinction = inputs.finiteExtinction ∧
        primitiveInputs =
          finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
            (extinction_implies_sphere_of_topology_package
              selected.topology) ∧
        primitiveInputs.universalFiniteExtinction =
          universalFiniteExtinctionStatement_of_smoothability_and_surgery_packages
            selected.smoothability selected.finiteExtinction ∧
        primitiveInputs.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package selected.topology ∧
        poincare_statement_of_extinction_and_extraction
            primitiveInputs.universalFiniteExtinction
            primitiveInputs.extinctionImpliesSphere =
          selected.publicStatement ∧
        poincare_conjecture_of_extinction_and_extraction
            primitiveInputs.universalFiniteExtinction
            primitiveInputs.extinctionImpliesSphere =
          selected.publicStatement ∧
        projectPayload =
          project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
            inputs selected.topology ∧
        canonicalPayload =
          canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
            selected.smoothability selected.finiteExtinction selected.topology ∧
        projectPayload.1 = selected.publicStatement ∧
        projectPayload.2.1 = selected.publicPayload ∧
        projectPayload.2.2 = selected.checkedCertificate ∧
        canonicalPayload.1 = selected.canonicalTarget ∧
        canonicalPayload.2.1 = selected.canonicalPayload ∧
        canonicalPayload.2.2 = selected.checkedCertificate ∧
        topologyAssemblyPayload.publicStatement =
          selected.publicStatement ∧
        topologyAssemblyPayload.checkedCertificate =
          selected.checkedCertificate ∧
        topologyAssemblyPayload.canonicalTarget =
          selected.canonicalTarget ∧
        topologyAssemblyPayload.publicPayload =
          selected.publicPayload ∧
        topologyAssemblyPayload.canonicalPayload =
          selected.canonicalPayload ∧
        topologyAssemblyPayload.completionCriteria =
          selected.completionCriteria ∧
        selected.publicStatement =
          poincare_conjecture_of_nonempty_namedPackageLayerConsumerPayload
            ⟨selected⟩ ∧
        selected.publicStatement =
          poincare_conjecture_of_completion_certificate
            selected.checkedCertificate ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} ∧
        canonicalCompletionTarget.{u} ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let primitiveInputs : FinalCertificatePrimitiveInputs.{u} :=
    finalCertificatePrimitiveInputs_of_minimalPackageInputs inputs
      (extinction_implies_sphere_of_topology_package selected.topology)
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  let projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs selected.topology
  let canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
      selected.smoothability selected.finiteExtinction selected.topology
  exact
    ⟨ selected
    , inputs
    , primitiveInputs
    , topologyAssemblyPayload
    , projectPayload
    , canonicalPayload
    , rfl
    , ⟨selected⟩
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.publicStatement
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    , selected.canonicalTarget
    , selected.completionCriteria
    ⟩

/--
For the constructed named-package consumer, the project and canonical payload
existentials can be opened while staying synchronized with the same selected
consumer and topology-assembly payload.  This endpoint gives final-collapse
callers named public/canonical payload targets and their all-witness completion
criteria, and proves that both criteria coincide with the selected consumer's
completion-criteria field.
-/
theorem finalCertificateNamedPackageLayerRequirements_constructedConsumer_projectCanonical_payload_targets_and_completionCriteria
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topology :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    let selected :=
      finalCertificateNamedPackageLayerConsumerPayload
        smoothability finiteExtinction topology
    let inputs : FinalCertificateMinimalPackageInputs.{u} :=
      { smoothability := selected.smoothability
        finiteExtinction := selected.finiteExtinction }
    let topologyAssemblyPayload :
        FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
      selected.topologyAssemblyPayload
    let projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
      project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
        inputs selected.topology
    let canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
      canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
        selected.smoothability selected.finiteExtinction selected.topology
    ∃ publicTarget : PoincareConjectureStatement.{u},
    ∃ publicCriteria :
      ∀ witness : Type u, CompletionCriterionAtUniverse witness,
    ∃ canonicalTarget : canonicalCompletionTarget.{u},
    ∃ canonicalCriteria :
      ∀ witness : Type u, CompletionCriterionAtUniverse witness,
      selected.publicPayload = ⟨publicTarget, publicCriteria⟩ ∧
        selected.canonicalPayload = ⟨canonicalTarget, canonicalCriteria⟩ ∧
        topologyAssemblyPayload.publicPayload = selected.publicPayload ∧
        topologyAssemblyPayload.canonicalPayload = selected.canonicalPayload ∧
        topologyAssemblyPayload.completionCriteria =
          selected.completionCriteria ∧
        projectPayload.2.1 = selected.publicPayload ∧
        projectPayload.2.2 = selected.checkedCertificate ∧
        canonicalPayload.1 = selected.canonicalTarget ∧
        canonicalPayload.2.1 = selected.canonicalPayload ∧
        canonicalPayload.2.2 = selected.checkedCertificate ∧
        publicCriteria = selected.completionCriteria ∧
        canonicalCriteria = selected.completionCriteria ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} ∧
        Nonempty PoincareCompletionCertificate.{u} := by
  let selected :=
    finalCertificateNamedPackageLayerConsumerPayload
      smoothability finiteExtinction topology
  let inputs : FinalCertificateMinimalPackageInputs.{u} :=
    { smoothability := selected.smoothability
      finiteExtinction := selected.finiteExtinction }
  let topologyAssemblyPayload :
      FinalCertificateTopologyAssemblyPayload inputs selected.topology :=
    selected.topologyAssemblyPayload
  let projectPayload :
      PoincareConjectureStatement.{u} ∧
        (∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    project_payload_and_final_certificate_of_finalCertificateMinimalPackageInputs_and_topologyPackage
      inputs selected.topology
  let canonicalPayload :
      canonicalCompletionTarget.{u} ∧
        (∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
        PoincareCompletionCertificate.{u} :=
    canonical_payload_and_final_certificate_of_smoothability_finiteExtinctionPackage_and_topologyPackage
      selected.smoothability selected.finiteExtinction selected.topology
  rcases selected.publicPayload with ⟨publicTarget, publicCriteria⟩
  rcases selected.canonicalPayload with ⟨canonicalTarget, canonicalCriteria⟩
  exact
    ⟨ publicTarget
    , publicCriteria
    , canonicalTarget
    , canonicalCriteria
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , selected.completionCriteria
    , selected.checkedCertificate
    , ⟨selected.checkedCertificate⟩
    ⟩

end Poincare
