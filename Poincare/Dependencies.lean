/-
Aggregate dependency package for the current conditional Poincare proof spine.

This module names the exact bundle of future theorem inputs that would turn the
current conditional assembly into the project target statement.
-/

import Poincare.FullAssembly

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
All currently identified external mathematical dependencies needed by the
conditional proof spine.
-/
structure PoincareProofDependencies where
  /-- Smoothability bridge from topological 3-manifolds to the surgery model. -/
  smoothability : SmoothabilityPackage.{u}
  /-- Completed Ricci-flow-with-surgery packages for all target manifolds. -/
  surgery :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)
  /-- Completed post-extinction topological extraction package. -/
  topology : ExtinctionTopologyExtractionPackage.{u}

/--
The aggregate package exposes exactly its three outstanding component inputs:
smoothability, the target-family surgery package, and topology extraction.
-/
theorem poincareProofDependencies_components_payload
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _smoothability : SmoothabilityPackage.{u},
    ∃ _surgery :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
      ExtinctionTopologyExtractionPackage.{u} := by
  exact ⟨dependencies.smoothability, dependencies.surgery, dependencies.topology⟩

/--
The aggregate dependency component payload is the tuple of the three stored
dependency fields.
-/
theorem poincareProofDependencies_components_payload_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincareProofDependencies_components_payload dependencies =
      ⟨dependencies.smoothability, dependencies.surgery,
        dependencies.topology⟩ := by
  apply Subsingleton.elim

/--
The aggregate dependency package is equivalent to exactly its three component
inputs.
-/
theorem poincareProofDependencies_iff_components :
    PoincareProofDependencies.{u} ↔
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u} := by
  constructor
  · exact poincareProofDependencies_components_payload
  · rintro ⟨smoothability, surgery, topology⟩
    exact ⟨smoothability, surgery, topology⟩

/--
The raw component payload reconstructs the aggregate dependency package.
-/
theorem poincareProofDependencies_of_components_payload :
    (∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u}) →
      PoincareProofDependencies.{u} := by
  rintro ⟨smoothability, surgery, topology⟩
  exact ⟨smoothability, surgery, topology⟩

/--
The raw component equivalence is exactly the named forward payload projection
paired with the named reverse constructor.
-/
theorem poincareProofDependencies_iff_components_eq :
    poincareProofDependencies_iff_components.{u} =
      ⟨poincareProofDependencies_components_payload,
        poincareProofDependencies_of_components_payload⟩ := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the two theorem-shaped inputs consumed
by the final finite-extinction/topology-extraction assembly theorem.
-/
theorem poincare_assembly_inputs_payload_of_aggregate_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionImpliesSphereStatement.{u} := by
  rcases poincare_assembly_inputs_payload_of_surgery_and_topology_packages
      dependencies.smoothability dependencies.surgery dependencies.topology with
    ⟨finiteExtinction, extractSphere⟩
  exact ⟨finiteExtinction, extractSphere⟩

/--
The aggregate assembly-input payload is selected from the package-level
surgery/topology assembly-input payload.
-/
theorem poincare_assembly_inputs_payload_of_aggregate_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_assembly_inputs_payload_of_aggregate_dependencies dependencies =
      (by
        rcases poincare_assembly_inputs_payload_of_surgery_and_topology_packages
            dependencies.smoothability dependencies.surgery dependencies.topology with
          ⟨finiteExtinction, extractSphere⟩
        exact ⟨finiteExtinction, extractSphere⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package also exposes the final finite-extinction input
together with a certified final extractor and its topology derivation
certificate.
-/
theorem poincare_assembly_inputs_payload_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  rcases
      poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology with
    ⟨finiteExtinction, extractSphere, derivation⟩
  exact ⟨finiteExtinction, extractSphere, derivation⟩

/--
The certified aggregate assembly-input payload is selected from the
package-level certified surgery/topology payload.
-/
theorem poincare_assembly_inputs_payload_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_assembly_inputs_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation
            dependencies.smoothability dependencies.surgery dependencies.topology with
          ⟨finiteExtinction, extractSphere, derivation⟩
        exact ⟨finiteExtinction, extractSphere, derivation⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the final assembly inputs, target
statement, and universe-indexed completion criterion through one named payload.
-/
theorem poincare_target_payload_of_aggregate_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_assembly_inputs_payload_of_aggregate_dependencies
      dependencies with
    ⟨finiteExtinction, extractSphere⟩
  rcases poincare_payload_of_extinction_and_extraction
      finiteExtinction extractSphere with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extractSphere, target, criterion⟩

/--
The aggregate target payload is selected from the named aggregate assembly-input
payload and the finite-extinction/extraction assembly bridge.
-/
theorem poincare_target_payload_of_aggregate_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_aggregate_dependencies dependencies =
      (by
        rcases poincare_assembly_inputs_payload_of_aggregate_dependencies
            dependencies with
          ⟨finiteExtinction, extractSphere⟩
        rcases poincare_payload_of_extinction_and_extraction
            finiteExtinction extractSphere with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extractSphere, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the certified final extractor,
derivation certificate, target statement, and universe-indexed completion
criterion through one named payload.
-/
theorem poincare_target_payload_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact
    poincare_target_payload_of_surgery_and_topology_package_extraction_derivation
      dependencies.smoothability dependencies.surgery dependencies.topology

/--
The certified aggregate target payload is the package-level certified
surgery/topology target payload.
-/
theorem poincare_target_payload_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      poincare_target_payload_of_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the explicit end-to-end assembly
inputs and target statement.
-/
theorem poincare_full_assembly_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
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
  rcases poincare_target_payload_of_aggregate_dependencies dependencies with
    ⟨finiteExtinction, extractSphere, target, _criterion⟩
  exact ⟨dependencies.smoothability, dependencies.surgery, dependencies.topology,
    finiteExtinction, extractSphere, target⟩

/--
The aggregate full-assembly payload is selected from the named aggregate target
payload and the stored dependency fields.
-/
theorem poincare_full_assembly_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_dependencies dependencies =
      (by
        rcases poincare_target_payload_of_aggregate_dependencies
            dependencies with
          ⟨finiteExtinction, extractSphere, target, _criterion⟩
        exact ⟨dependencies.smoothability, dependencies.surgery,
          dependencies.topology, finiteExtinction, extractSphere, target⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the explicit end-to-end certified
extraction-derivation assembly inputs and target statement.
-/
theorem poincare_full_assembly_payload_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
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
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
      PoincareConjectureStatement.{u} := by
  rcases
      poincare_target_payload_of_aggregate_extraction_derivation_dependencies
        dependencies with
    ⟨finiteExtinction, extractSphere, derivation, target, _criterion⟩
  exact ⟨dependencies.smoothability, dependencies.surgery, dependencies.topology,
    finiteExtinction, extractSphere, derivation, target⟩

/--
The certified aggregate full-assembly payload is selected from the named
certified aggregate target payload and the stored dependency fields.
-/
theorem poincare_full_assembly_payload_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            poincare_target_payload_of_aggregate_extraction_derivation_dependencies
            dependencies with
          ⟨finiteExtinction, extractSphere, derivation, target, _criterion⟩
        exact ⟨dependencies.smoothability, dependencies.surgery,
          dependencies.topology, finiteExtinction, extractSphere, derivation,
          target⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package is sufficient for the target Poincare
statement.
-/
theorem poincare_assembly_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _smoothabilityPackage : SmoothabilityPackage.{u},
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
    ∃ _topologyPackage : ExtinctionTopologyExtractionPackage.{u},
      PoincareConjectureStatement.{u} := by
  rcases poincare_full_assembly_payload_of_dependencies dependencies with
    ⟨smoothabilityPackage, surgeryPackages, topologyPackage,
      _finiteExtinction, _extractSphere, target⟩
  exact ⟨smoothabilityPackage, surgeryPackages, topologyPackage, target⟩

/--
The aggregate assembly payload is selected from the named aggregate
full-assembly payload.
-/
theorem poincare_assembly_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_assembly_payload_of_dependencies dependencies =
      (by
        rcases poincare_full_assembly_payload_of_dependencies dependencies with
          ⟨smoothabilityPackage, surgeryPackages, topologyPackage,
            _finiteExtinction, _extractSphere, target⟩
        exact ⟨smoothabilityPackage, surgeryPackages, topologyPackage,
          target⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the local target and the
universe-indexed completion criterion as one payload.
-/
theorem poincare_completion_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_aggregate_dependencies dependencies with
    ⟨_finiteExtinction, _extractSphere, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The aggregate completion payload is selected from the named aggregate target
payload.
-/
theorem poincare_completion_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_dependencies dependencies =
      (by
        rcases poincare_target_payload_of_aggregate_dependencies
            dependencies with
          ⟨_finiteExtinction, _extractSphere, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the local target and completion
criterion through the certified extraction-derivation route.
-/
theorem poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_aggregate_extraction_derivation_dependencies
        dependencies with
    ⟨_finiteExtinction, _extractSphere, _derivation, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The certified aggregate completion payload is selected from the named certified
aggregate target payload.
-/
theorem poincare_completion_payload_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            poincare_target_payload_of_aggregate_extraction_derivation_dependencies
            dependencies with
          ⟨_finiteExtinction, _extractSphere, _derivation, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The aggregate dependency package is sufficient for the target Poincare
statement, extracted from the aggregate assembly payload.
-/
theorem poincare_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_completion_payload_of_dependencies dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The aggregate Poincare statement is selected from the named aggregate
completion payload.
-/
theorem poincare_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_dependencies dependencies =
      (by
        rcases poincare_completion_payload_of_dependencies dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The aggregate dependency package is sufficient for the target Poincare
statement through the certified extraction-derivation route.
-/
theorem poincare_statement_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The certified aggregate Poincare statement is selected from the named certified
aggregate completion payload.
-/
theorem poincare_statement_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The aggregate dependency package exposes the canonical mathlib-shaped
topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_dependencies dependencies)

/--
The aggregate canonical topological sphere statement is the canonical bridge
applied to the named aggregate Poincare statement.
-/
theorem canonical_three_sphere_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_dependencies dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The aggregate dependency package also exposes the canonical mathlib-shaped
topological 3-sphere statement through the certified extraction-derivation
route.
-/
theorem canonical_three_sphere_statement_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_aggregate_extraction_derivation_dependencies
      dependencies)

/--
The certified aggregate canonical topological sphere statement is the canonical
bridge applied to the named certified aggregate Poincare statement.
-/
theorem canonical_three_sphere_statement_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_aggregate_extraction_derivation_dependencies
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_aggregate_extraction_derivation_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate dependency package also discharges the project's explicit
completion criterion at the same universe.
-/
theorem completion_criterion_of_dependencies
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases poincare_completion_payload_of_dependencies dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The aggregate completion criterion is selected from the named aggregate
completion payload.
-/
theorem completion_criterion_of_dependencies_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_dependencies witness dependencies =
      (by
        rcases poincare_completion_payload_of_dependencies dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The aggregate dependency package also discharges the project's explicit
completion criterion through the certified extraction-derivation route.
-/
theorem completion_criterion_of_aggregate_extraction_derivation_dependencies
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The certified aggregate completion criterion is selected from the named
certified aggregate completion payload.
-/
theorem completion_criterion_of_aggregate_extraction_derivation_dependencies_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_aggregate_extraction_derivation_dependencies
      witness dependencies =
      (by
        rcases
            poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

end Poincare
