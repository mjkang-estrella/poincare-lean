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
Aggregate dependency package strengthened with explicit smooth-piece
Ricci-flow equation boundaries for the selected finite-extinction surgery
packages.

This records a sharper version of the large remaining analytic obligation:
finite extinction still comes through the ordinary surgery package, while the
same selected package must also carry a concrete boundary proof of
`∂ₜ g = -2 Ricci`.
-/
structure PoincareProofDependenciesWithEquationBoundary where
  /-- Smoothability bridge from topological 3-manifolds to the surgery model. -/
  smoothability : SmoothabilityPackage.{u}
  /-- Completed surgery packages with explicit equation boundaries. -/
  surgery :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty
          (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M)
  /-- Completed post-extinction topological extraction package. -/
  topology : ExtinctionTopologyExtractionPackage.{u}

/--
Forget explicit equation boundaries from the strengthened dependency package,
recovering the ordinary aggregate dependencies consumed by the existing final
assembly theorem.
-/
noncomputable def dependencies_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareProofDependencies.{u} where
  smoothability := dependencies.smoothability
  surgery := fun M => (dependencies.surgery M).map
    (fun payload =>
      ⟨payload.1,
        surgery_package_of_equation_boundary_surgery_package payload.2⟩)
  topology := dependencies.topology

/--
The strengthened dependency forgetful projection keeps smoothability and
topology fixed and maps each strengthened surgery package to its base package.
-/
theorem dependencies_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencies_of_equation_boundary_dependencies dependencies =
      ({ smoothability := dependencies.smoothability
         surgery := fun M => (dependencies.surgery M).map
           (fun payload =>
             ⟨payload.1,
               surgery_package_of_equation_boundary_surgery_package payload.2⟩)
         topology := dependencies.topology } : PoincareProofDependencies.{u}) :=
  rfl

/--
Lift ordinary aggregate dependencies to the strengthened equation-boundary
dependency package when every ordinary surgery package in the family is
equipped with an explicit Ricci-flow equation verification.
-/
noncomputable def equation_boundary_dependencies_of_dependencies_and_verification_family
    (dependencies : PoincareProofDependencies.{u})
    (verificationFamily :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M]
        (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package payload.2))) :
    PoincareProofDependenciesWithEquationBoundary.{u} where
  smoothability := dependencies.smoothability
  surgery := fun M => (dependencies.surgery M).map
    (fun payload =>
      ⟨payload.1,
        surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
          payload.2
          (verificationFamily M payload)⟩)
  topology := dependencies.topology

/--
The verification-family lift keeps smoothability and topology fixed while
mapping each ordinary surgery package through the surgery-level
verification-to-boundary constructor.
-/
theorem equation_boundary_dependencies_of_dependencies_and_verification_family_eq
    (dependencies : PoincareProofDependencies.{u})
    (verificationFamily :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M]
        (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package payload.2))) :
    equation_boundary_dependencies_of_dependencies_and_verification_family
        dependencies verificationFamily =
      ({ smoothability := dependencies.smoothability
         surgery := fun M => (dependencies.surgery M).map
           (fun payload =>
             ⟨payload.1,
               surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
                 payload.2
                 (verificationFamily M payload)⟩)
         topology := dependencies.topology } :
        PoincareProofDependenciesWithEquationBoundary.{u}) :=
  rfl

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

/-- Project the smoothability obligation from the aggregate dependency package. -/
theorem smoothabilityPackage_of_poincareProofDependencies
    (dependencies : PoincareProofDependencies.{u}) :
    SmoothabilityPackage.{u} :=
  dependencies.smoothability

/--
The aggregate smoothability projection is the stored smoothability field.
-/
theorem smoothabilityPackage_of_poincareProofDependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothabilityPackage_of_poincareProofDependencies dependencies =
      dependencies.smoothability := by
  apply Subsingleton.elim

/--
Project the universal finite-extinction surgery package family from the
aggregate dependency package.
-/
theorem surgeryPackages_of_poincareProofDependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) :=
  dependencies.surgery

/--
The aggregate surgery-package projection is the stored surgery family field.
-/
theorem surgeryPackages_of_poincareProofDependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgeryPackages_of_poincareProofDependencies dependencies =
      dependencies.surgery := by
  apply Subsingleton.elim

/-- Project the topology extraction obligation from the aggregate dependency package. -/
theorem topologyExtractionPackage_of_poincareProofDependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ExtinctionTopologyExtractionPackage.{u} :=
  dependencies.topology

/--
The aggregate topology-extraction projection is the stored topology field.
-/
theorem topologyExtractionPackage_of_poincareProofDependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topologyExtractionPackage_of_poincareProofDependencies dependencies =
      dependencies.topology := by
  apply Subsingleton.elim

/--
The aggregate component payload is the tuple of the named dependency
projections.
-/
theorem poincareProofDependencies_components_payload_to_named_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincareProofDependencies_components_payload dependencies =
      ⟨smoothabilityPackage_of_poincareProofDependencies dependencies,
        surgeryPackages_of_poincareProofDependencies dependencies,
        topologyExtractionPackage_of_poincareProofDependencies
          dependencies⟩ := by
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
The reverse component constructor is exactly the unpacking route from the raw
component payload.
-/
theorem poincareProofDependencies_of_components_payload_eq :
    poincareProofDependencies_of_components_payload.{u} =
      (fun payload =>
        by
          rcases payload with ⟨smoothability, surgery, topology⟩
          exact
            ({ smoothability := smoothability
               surgery := surgery
               topology := topology } : PoincareProofDependencies.{u})) := by
  apply Subsingleton.elim

/--
Projecting the component payload from the aggregate package reconstructed from
that payload returns the original component payload.
-/
theorem poincareProofDependencies_components_payload_of_components_payload_eq
    (payload :
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u}) :
    poincareProofDependencies_components_payload
      (poincareProofDependencies_of_components_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The aggregate component constructor recovers any dependency package from its
projected component payload.
-/
theorem poincareProofDependencies_of_components_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincareProofDependencies_of_components_payload
      (poincareProofDependencies_components_payload dependencies) =
      dependencies := by
  apply Subsingleton.elim

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
The strengthened aggregate package exposes exactly its smoothability package,
boundary-carrying surgery package family, and topology extraction package.
-/
theorem poincareProofDependenciesWithEquationBoundary_components_payload
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _smoothability : SmoothabilityPackage.{u},
    ∃ _surgery :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty
            (Σ n : ℕ∞ω,
              FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
      ExtinctionTopologyExtractionPackage.{u} := by
  exact ⟨dependencies.smoothability, dependencies.surgery, dependencies.topology⟩

/--
The strengthened aggregate component payload is the tuple of its three stored
dependency fields.
-/
theorem poincareProofDependenciesWithEquationBoundary_components_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincareProofDependenciesWithEquationBoundary_components_payload
        dependencies =
      ⟨dependencies.smoothability, dependencies.surgery,
        dependencies.topology⟩ := by
  apply Subsingleton.elim

/--
Project the smoothability obligation from the strengthened aggregate dependency
package.
-/
theorem smoothabilityPackage_of_poincareProofDependenciesWithEquationBoundary
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    SmoothabilityPackage.{u} :=
  dependencies.smoothability

/--
The strengthened aggregate smoothability projection is the stored smoothability
field.
-/
theorem smoothabilityPackage_of_poincareProofDependenciesWithEquationBoundary_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    smoothabilityPackage_of_poincareProofDependenciesWithEquationBoundary
        dependencies =
      dependencies.smoothability := by
  apply Subsingleton.elim

/--
Project the universal boundary-carrying surgery package family from the
strengthened aggregate dependency package.
-/
theorem boundarySurgeryPackages_of_poincareProofDependenciesWithEquationBoundary
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty
          (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :=
  dependencies.surgery

/--
The strengthened aggregate boundary-surgery projection is the stored surgery
family field.
-/
theorem boundarySurgeryPackages_of_poincareProofDependenciesWithEquationBoundary_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    boundarySurgeryPackages_of_poincareProofDependenciesWithEquationBoundary
        dependencies =
      dependencies.surgery := by
  apply Subsingleton.elim

/--
Project the topology extraction obligation from the strengthened aggregate
dependency package.
-/
theorem topologyExtractionPackage_of_poincareProofDependenciesWithEquationBoundary
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ExtinctionTopologyExtractionPackage.{u} :=
  dependencies.topology

/--
The strengthened aggregate topology-extraction projection is the stored
topology field.
-/
theorem topologyExtractionPackage_of_poincareProofDependenciesWithEquationBoundary_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topologyExtractionPackage_of_poincareProofDependenciesWithEquationBoundary
        dependencies =
      dependencies.topology := by
  apply Subsingleton.elim

/--
The strengthened aggregate component payload is the tuple of the named
dependency projections.
-/
theorem poincareProofDependenciesWithEquationBoundary_components_payload_to_named_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincareProofDependenciesWithEquationBoundary_components_payload
        dependencies =
      ⟨smoothabilityPackage_of_poincareProofDependenciesWithEquationBoundary
          dependencies,
        boundarySurgeryPackages_of_poincareProofDependenciesWithEquationBoundary
          dependencies,
        topologyExtractionPackage_of_poincareProofDependenciesWithEquationBoundary
          dependencies⟩ := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package is equivalent to exactly its
three component inputs.
-/
theorem poincareProofDependenciesWithEquationBoundary_iff_components :
    PoincareProofDependenciesWithEquationBoundary.{u} ↔
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty
              (Σ n : ℕ∞ω,
                FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
        ExtinctionTopologyExtractionPackage.{u} := by
  constructor
  · exact poincareProofDependenciesWithEquationBoundary_components_payload
  · rintro ⟨smoothability, surgery, topology⟩
    exact ⟨smoothability, surgery, topology⟩

/--
The strengthened raw component payload reconstructs the strengthened aggregate
dependency package.
-/
theorem poincareProofDependenciesWithEquationBoundary_of_components_payload :
    (∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty
              (Σ n : ℕ∞ω,
                FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
        ExtinctionTopologyExtractionPackage.{u}) →
      PoincareProofDependenciesWithEquationBoundary.{u} := by
  rintro ⟨smoothability, surgery, topology⟩
  exact ⟨smoothability, surgery, topology⟩

/--
The strengthened reverse component constructor is exactly the unpacking route
from the raw component payload.
-/
theorem poincareProofDependenciesWithEquationBoundary_of_components_payload_eq :
    poincareProofDependenciesWithEquationBoundary_of_components_payload.{u} =
      (fun payload =>
        by
          rcases payload with ⟨smoothability, surgery, topology⟩
          exact
            ({ smoothability := smoothability
               surgery := surgery
               topology := topology } :
              PoincareProofDependenciesWithEquationBoundary.{u})) := by
  apply Subsingleton.elim

/--
Projecting the component payload from the strengthened package reconstructed
from that payload returns the original strengthened component payload.
-/
theorem poincareProofDependenciesWithEquationBoundary_components_payload_of_components_payload_eq
    (payload :
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty
              (Σ n : ℕ∞ω,
                FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
        ExtinctionTopologyExtractionPackage.{u}) :
    poincareProofDependenciesWithEquationBoundary_components_payload
      (poincareProofDependenciesWithEquationBoundary_of_components_payload
        payload) =
      payload := by
  apply Subsingleton.elim

/--
The strengthened component constructor recovers any strengthened dependency
package from its projected component payload.
-/
theorem poincareProofDependenciesWithEquationBoundary_of_components_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincareProofDependenciesWithEquationBoundary_of_components_payload
      (poincareProofDependenciesWithEquationBoundary_components_payload
        dependencies) =
      dependencies := by
  apply Subsingleton.elim

/--
The strengthened raw component equivalence is exactly the named forward payload
projection paired with the named reverse constructor.
-/
theorem poincareProofDependenciesWithEquationBoundary_iff_components_eq :
    poincareProofDependenciesWithEquationBoundary_iff_components.{u} =
      ⟨poincareProofDependenciesWithEquationBoundary_components_payload,
        poincareProofDependenciesWithEquationBoundary_of_components_payload⟩ := by
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
The aggregate assembly-input payload also factors through the named aggregate
dependency projections.
-/
theorem poincare_assembly_inputs_payload_of_aggregate_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_assembly_inputs_payload_of_aggregate_dependencies dependencies =
      (by
        rcases
            poincare_assembly_inputs_payload_of_surgery_and_topology_packages
              (smoothabilityPackage_of_poincareProofDependencies dependencies)
              (surgeryPackages_of_poincareProofDependencies dependencies)
              (topologyExtractionPackage_of_poincareProofDependencies
                dependencies) with
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
The certified aggregate assembly-input payload also factors through the named
aggregate dependency projections.
-/
theorem poincare_assembly_inputs_payload_of_aggregate_extraction_derivation_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_assembly_inputs_payload_of_aggregate_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation
              (smoothabilityPackage_of_poincareProofDependencies dependencies)
              (surgeryPackages_of_poincareProofDependencies dependencies)
              (topologyExtractionPackage_of_poincareProofDependencies
                dependencies) with
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
The certified aggregate target payload also factors directly through the
finite-extinction endpoint and the extractor/derivation certificate carried by
the topology package.
-/
theorem poincare_target_payload_of_aggregate_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_surgery_packages
            dependencies.smoothability dependencies.surgery
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨finiteExtinction, extractSphere, derivation, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the boundary-carrying
surgery family together with the ordinary final assembly inputs, target
statement, and universe-indexed completion criterion.
-/
theorem poincare_target_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty
            (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_aggregate_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) with
    ⟨finiteExtinction, extractSphere, target, criterion⟩
  exact
    ⟨dependencies.surgery, finiteExtinction, extractSphere, target, criterion⟩

/--
The strengthened aggregate target payload keeps the stored boundary-carrying
surgery family and selects the remaining fields from the ordinary forgetful
aggregate target payload.
-/
theorem poincare_target_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependencies dependencies =
      (by
        rcases
            poincare_target_payload_of_aggregate_dependencies
              (dependencies_of_equation_boundary_dependencies dependencies) with
          ⟨finiteExtinction, extractSphere, target, criterion⟩
        exact
          ⟨dependencies.surgery, finiteExtinction, extractSphere, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened aggregate target payload also factors directly through the
boundary finite-extinction endpoint and the topology package's final extractor.
-/
theorem poincare_target_payload_of_equation_boundary_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependencies dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        let target :=
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extractSphere
        let criterion :=
          fun witness =>
            completionCriterionAtUniverse_of_poincareConjectureStatement
              witness target
        exact
          ⟨dependencies.surgery, finiteExtinction, extractSphere, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
Ordinary aggregate dependencies plus explicit equation verifications for their
surgery packages expose the strengthened boundary-carrying target payload.
-/
theorem poincare_target_payload_of_dependencies_and_verification_family
    (dependencies : PoincareProofDependencies.{u})
    (verificationFamily :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M]
        (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package payload.2))) :
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty
            (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_target_payload_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The ordinary-dependencies-plus-verification-family target route delegates
through the strengthened aggregate dependency lift.
-/
theorem poincare_target_payload_of_dependencies_and_verification_family_eq
    (dependencies : PoincareProofDependencies.{u})
    (verificationFamily :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M]
        (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package payload.2))) :
    poincare_target_payload_of_dependencies_and_verification_family
      dependencies verificationFamily =
      poincare_target_payload_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the boundary-carrying surgery family in the strengthened target
payload recovers the ordinary aggregate target payload.
-/
theorem poincare_target_payload_of_equation_boundary_dependencies_to_forgetful_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_equation_boundary_dependencies
      dependencies with
    ⟨_surgeryPackages, finiteExtinction, extractSphere, target, criterion⟩
  exact ⟨finiteExtinction, extractSphere, target, criterion⟩

/--
The forgetful projection of the strengthened target payload is the ordinary
aggregate target payload of the forgetful dependency package.
-/
theorem poincare_target_payload_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependencies_to_forgetful_dependencies
        dependencies =
      poincare_target_payload_of_aggregate_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the boundary-carrying
surgery family together with the certified extraction-derivation assembly
inputs, target statement, and completion criterion.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty
            (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
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
  rcases
      poincare_target_payload_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) with
    ⟨finiteExtinction, extractSphere, derivation, target, criterion⟩
  exact
    ⟨dependencies.surgery, finiteExtinction, extractSphere, derivation, target,
      criterion⟩

/--
The strengthened certified target payload keeps the stored boundary-carrying
surgery family and selects the remaining fields from the ordinary forgetful
certified aggregate target payload.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            poincare_target_payload_of_aggregate_extraction_derivation_dependencies
              (dependencies_of_equation_boundary_dependencies dependencies) with
          ⟨finiteExtinction, extractSphere, derivation, target, criterion⟩
        exact
          ⟨dependencies.surgery, finiteExtinction, extractSphere, derivation,
            target, criterion⟩) := by
  apply Subsingleton.elim

/--
Forgetting the boundary-carrying surgery family in the strengthened certified
target payload recovers the ordinary certified aggregate target payload.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
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
  rcases
      poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨_surgeryPackages, finiteExtinction, extractSphere, derivation, target,
      criterion⟩
  exact ⟨finiteExtinction, extractSphere, derivation, target, criterion⟩

/--
The forgetful projection of the strengthened certified target payload is the
ordinary certified aggregate target payload of the forgetful dependency package.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies
        dependencies =
      poincare_target_payload_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified target payload agrees with the direct
boundary-package certified extraction-derivation route.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        let target :=
          poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
            dependencies.smoothability dependencies.surgery dependencies.topology
        exact
          ⟨dependencies.surgery,
            finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery,
            extractSphere, derivation, target,
            fun witness =>
              completionCriterionAtUniverse_of_poincareConjectureStatement
                witness target⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified target payload also factors directly through the
boundary finite-extinction endpoint and the extractor/derivation certificate
carried by the topology package.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨dependencies.surgery, finiteExtinction, extractSphere, derivation,
            target, criterion⟩) := by
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
The certified aggregate full-assembly payload also factors directly through
the finite-extinction endpoint and the extractor/derivation certificate carried
by the topology package.
-/
theorem poincare_full_assembly_payload_of_aggregate_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_surgery_packages
            dependencies.smoothability dependencies.surgery
        exact ⟨dependencies.smoothability, dependencies.surgery,
          dependencies.topology, finiteExtinction, extractSphere, derivation,
          poincare_statement_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation⟩) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the explicit end-to-end
assembly inputs and target statement while retaining the boundary-carrying
surgery family.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _smoothabilityPackage : SmoothabilityPackage.{u},
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty
            (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
    ∃ _topologyPackage : ExtinctionTopologyExtractionPackage.{u},
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
      PoincareConjectureStatement.{u} := by
  rcases poincare_target_payload_of_equation_boundary_dependencies
      dependencies with
    ⟨surgeryPackages, finiteExtinction, extractSphere, target, _criterion⟩
  exact
    ⟨dependencies.smoothability, surgeryPackages, dependencies.topology,
      finiteExtinction, extractSphere, target⟩

/--
The strengthened aggregate full-assembly payload is selected from the named
strengthened aggregate target payload and the stored dependency fields.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_dependencies
        dependencies =
      (by
        rcases poincare_target_payload_of_equation_boundary_dependencies
            dependencies with
          ⟨surgeryPackages, finiteExtinction, extractSphere, target,
            _criterion⟩
        exact
          ⟨dependencies.smoothability, surgeryPackages, dependencies.topology,
            finiteExtinction, extractSphere, target⟩) := by
  apply Subsingleton.elim

/--
Forgetting the boundary-carrying surgery family in the strengthened full
assembly payload recovers the ordinary aggregate full assembly payload shape.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_dependencies_to_forgetful_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
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
  rcases poincare_full_assembly_payload_of_equation_boundary_dependencies
      dependencies with
    ⟨_smoothabilityPackage, _boundarySurgeryPackages, _topologyPackage,
      finiteExtinction, extractSphere, target⟩
  exact
    ⟨(dependencies_of_equation_boundary_dependencies dependencies).smoothability,
      (dependencies_of_equation_boundary_dependencies dependencies).surgery,
      (dependencies_of_equation_boundary_dependencies dependencies).topology,
      finiteExtinction, extractSphere, target⟩

/--
The forgetful projection of the strengthened full assembly payload is the
ordinary aggregate full assembly payload of the forgetful dependency package.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_dependencies_to_forgetful_dependencies
        dependencies =
      poincare_full_assembly_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The forgetful projection of the strengthened full assembly payload agrees with
the direct boundary-package route after forgetting the boundary-carrying
surgery family in the payload fields.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_dependencies_to_forgetful_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_dependencies_to_forgetful_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_extraction_statement
            (extinction_topology_extraction_statement_of_topology_package
              dependencies.topology)
        exact
          ⟨dependencies.smoothability,
            (dependencies_of_equation_boundary_dependencies dependencies).surgery,
            dependencies.topology, finiteExtinction, extractSphere,
            poincare_statement_of_boundary_surgery_and_topology_packages
              dependencies.smoothability dependencies.surgery
              dependencies.topology⟩) := by
  apply Subsingleton.elim

/--
The strengthened aggregate full-assembly payload agrees with the direct
boundary-package route exposed by the full assembly layer.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_extraction_statement
            (extinction_topology_extraction_statement_of_topology_package
              dependencies.topology)
        exact
          ⟨dependencies.smoothability, dependencies.surgery,
            dependencies.topology, finiteExtinction, extractSphere,
            poincare_statement_of_boundary_surgery_and_topology_packages
              dependencies.smoothability dependencies.surgery
              dependencies.topology⟩) := by
  apply Subsingleton.elim

/--
The strengthened aggregate full-assembly payload also factors directly through
the boundary finite-extinction endpoint and the topology package's final
extractor.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          ⟨dependencies.smoothability, dependencies.surgery,
            dependencies.topology, finiteExtinction, extractSphere,
            poincare_statement_of_extinction_and_extraction
              finiteExtinction extractSphere⟩) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the explicit end-to-end
certified extraction-derivation assembly inputs and target statement while
retaining the boundary-carrying surgery family.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _smoothabilityPackage : SmoothabilityPackage.{u},
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty
            (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M)),
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
      poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨surgeryPackages, finiteExtinction, extractSphere, derivation, target,
      _criterion⟩
  exact
    ⟨dependencies.smoothability, surgeryPackages, dependencies.topology,
      finiteExtinction, extractSphere, derivation, target⟩

/--
The strengthened certified aggregate full-assembly payload is selected from the
named strengthened certified aggregate target payload and the stored dependency
fields.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
              dependencies with
          ⟨surgeryPackages, finiteExtinction, extractSphere, derivation, target,
            _criterion⟩
        exact
          ⟨dependencies.smoothability, surgeryPackages, dependencies.topology,
            finiteExtinction, extractSphere, derivation, target⟩) := by
  apply Subsingleton.elim

/--
Forgetting the boundary-carrying surgery family in the strengthened certified
full assembly payload recovers the ordinary certified aggregate full assembly
payload shape.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
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
      poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨_smoothabilityPackage, _boundarySurgeryPackages, _topologyPackage,
      finiteExtinction, extractSphere, derivation, target⟩
  exact
    ⟨(dependencies_of_equation_boundary_dependencies dependencies).smoothability,
      (dependencies_of_equation_boundary_dependencies dependencies).surgery,
      (dependencies_of_equation_boundary_dependencies dependencies).topology,
      finiteExtinction, extractSphere, derivation, target⟩

/--
The forgetful projection of the strengthened certified full assembly payload is
the ordinary certified aggregate full assembly payload of the forgetful
dependency package.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies
        dependencies =
      poincare_full_assembly_payload_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The forgetful projection of the strengthened certified full assembly payload
agrees with the direct boundary-package certified route after forgetting the
boundary-carrying surgery family in the payload fields.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          ⟨dependencies.smoothability,
            (dependencies_of_equation_boundary_dependencies dependencies).surgery,
            dependencies.topology,
            finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery,
            extractSphere, derivation,
            poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
              dependencies.smoothability dependencies.surgery
              dependencies.topology⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified full-assembly payload agrees with the direct
boundary-package certified extraction-derivation route.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          ⟨dependencies.smoothability, dependencies.surgery,
            dependencies.topology,
            finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery,
            extractSphere, derivation,
            poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
              dependencies.smoothability dependencies.surgery
              dependencies.topology⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified full-assembly payload also factors directly through
the finite-extinction endpoint and the extractor/derivation certificate carried
by the topology package.
-/
theorem poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_full_assembly_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        exact
          ⟨dependencies.smoothability, dependencies.surgery,
            dependencies.topology, finiteExtinction, extractSphere, derivation,
            poincare_statement_of_finite_extinction_and_extraction_derivation
              finiteExtinction extractSphere derivation⟩) := by
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
The aggregate dependency package exposes the reserved conditional endpoint and
completion criterion by first projecting the final finite-extinction/extraction
inputs, then using the reserved endpoint payload route.
-/
theorem poincare_conjecture_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_assembly_inputs_payload_of_aggregate_dependencies
      dependencies with
    ⟨finiteExtinction, extractSphere⟩
  exact
    poincare_conjecture_payload_of_extinction_and_extraction
      finiteExtinction extractSphere

/--
The aggregate reserved-endpoint payload factors through the named aggregate
assembly-input projection and the reserved extinction/extraction endpoint
payload.
-/
theorem poincare_conjecture_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_conjecture_payload_of_dependencies dependencies =
      (by
        rcases poincare_assembly_inputs_payload_of_aggregate_dependencies
            dependencies with
          ⟨finiteExtinction, extractSphere⟩
        exact
          poincare_conjecture_payload_of_extinction_and_extraction
            finiteExtinction extractSphere) := by
  apply Subsingleton.elim

/--
The aggregate dependency package is sufficient for the reserved conditional
endpoint. This theorem still requires the full aggregate dependency package; it
does not provide an unconditional `poincare_conjecture`.
-/
theorem poincare_conjecture_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_conjecture_payload_of_dependencies dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The aggregate reserved endpoint is selected from the named aggregate
reserved-endpoint payload.
-/
theorem poincare_conjecture_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_conjecture_of_dependencies dependencies =
      (by
        rcases poincare_conjecture_payload_of_dependencies dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the local target and the
universe-indexed completion criterion by forgetting the explicit equation
boundaries and using the existing final assembly route.
-/
theorem poincare_completion_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened aggregate completion payload is the ordinary aggregate payload
of the forgetful projection.
-/
theorem poincare_completion_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependencies dependencies =
      poincare_completion_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) :=
  rfl

/--
The strengthened aggregate completion payload agrees with the ordinary
aggregate completion payload after forgetting equation-boundary data.
-/
theorem poincare_completion_payload_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependencies dependencies =
      poincare_completion_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) :=
  rfl

/--
The strengthened aggregate completion payload agrees with projecting the target
and criterion from the direct boundary-package full-assembly route.
-/
theorem poincare_completion_payload_of_equation_boundary_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependencies
        dependencies =
      ⟨poincare_statement_of_boundary_surgery_and_topology_packages
        dependencies.smoothability dependencies.surgery dependencies.topology,
        fun witness =>
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_boundary_surgery_and_topology_packages
              dependencies.smoothability dependencies.surgery
              dependencies.topology)⟩ := by
  apply Subsingleton.elim

/--
The strengthened aggregate completion payload also factors directly through
the boundary finite-extinction endpoint and the topology package's final
extractor.
-/
theorem poincare_completion_payload_of_equation_boundary_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        let target :=
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extractSphere
        exact
          ⟨target,
            fun witness =>
              completionCriterionAtUniverse_of_poincareConjectureStatement
                witness target⟩) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the reserved conditional
endpoint and completion criterion by forgetting equation-boundary data and using
the ordinary aggregate reserved-endpoint route.
-/
theorem poincare_conjecture_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_conjecture_payload_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened reserved-endpoint payload is the ordinary aggregate
reserved-endpoint payload of the forgetful projection.
-/
theorem poincare_conjecture_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_payload_of_equation_boundary_dependencies dependencies =
      poincare_conjecture_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) :=
  rfl

/--
The strengthened aggregate reserved-endpoint payload also factors directly
through the boundary finite-extinction endpoint and the topology package's
final extractor.
-/
theorem poincare_conjecture_payload_of_equation_boundary_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_payload_of_equation_boundary_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          poincare_conjecture_payload_of_extinction_and_extraction
            finiteExtinction extractSphere) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package is sufficient for the reserved
conditional endpoint after forgetting equation-boundary data.
-/
theorem poincare_conjecture_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_conjecture_payload_of_equation_boundary_dependencies
      dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The strengthened aggregate reserved endpoint is selected from the named
strengthened reserved-endpoint payload.
-/
theorem poincare_conjecture_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_of_equation_boundary_dependencies dependencies =
      (by
        rcases poincare_conjecture_payload_of_equation_boundary_dependencies
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened aggregate reserved endpoint agrees with the ordinary aggregate
reserved endpoint after forgetting equation-boundary data.
-/
theorem poincare_conjecture_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_of_equation_boundary_dependencies dependencies =
      poincare_conjecture_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened aggregate reserved endpoint factors directly through the
boundary finite-extinction endpoint and the topology package's final extractor.
-/
theorem poincare_conjecture_of_equation_boundary_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_of_equation_boundary_dependencies dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          poincare_conjecture_of_extinction_and_extraction
            finiteExtinction extractSphere) := by
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
The certified aggregate completion payload also factors directly through the
finite-extinction endpoint and the extractor/derivation certificate carried by
the topology package.
-/
theorem poincare_completion_payload_of_aggregate_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_input_of_smoothability_and_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the local target and
completion criterion through the certified extraction-derivation route while
retaining explicit equation-boundary data.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨_surgeryPackages, _finiteExtinction, _extractSphere, _derivation, target,
      criterion⟩
  exact ⟨target, criterion⟩

/--
The strengthened certified completion payload is selected from the named
strengthened certified target payload.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            poincare_target_payload_of_equation_boundary_extraction_derivation_dependencies
              dependencies with
          ⟨_surgeryPackages, _finiteExtinction, _extractSphere, _derivation,
            target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified completion payload agrees with the certified
aggregate completion payload after forgetting equation-boundary data.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified completion payload agrees with projecting the target
and criterion from the direct boundary-package certified route.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      ⟨poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology,
        fun witness =>
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
              dependencies.smoothability dependencies.surgery
              dependencies.topology)⟩ := by
  apply Subsingleton.elim

/--
The strengthened certified completion payload also factors directly through
the finite-extinction endpoint and the extractor/derivation certificate carried
by the topology package.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified aggregate dependency package exposes the reserved conditional
endpoint and completion criterion through the finite-extinction endpoint and
the topology package's certified extractor.
-/
theorem poincare_conjecture_payload_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases topology_extraction_derivation_payload_of_topology_package
      dependencies.topology with
    ⟨extractSphere, _derivation⟩
  exact
    poincare_conjecture_payload_of_extinction_and_extraction
      (finite_extinction_input_of_smoothability_and_surgery_packages
        dependencies.smoothability dependencies.surgery)
      extractSphere

/--
The certified aggregate reserved-endpoint payload factors through the
finite-extinction endpoint and the certified extractor carried by the topology
package.
-/
theorem poincare_conjecture_payload_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_conjecture_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, _derivation⟩
        exact
          poincare_conjecture_payload_of_extinction_and_extraction
            (finite_extinction_input_of_smoothability_and_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate dependency package exposes the reserved
conditional endpoint and completion criterion through the boundary
finite-extinction endpoint and the topology package's certified extractor.
-/
theorem poincare_conjecture_payload_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases topology_extraction_derivation_payload_of_topology_package
      dependencies.topology with
    ⟨extractSphere, _derivation⟩
  exact
    poincare_conjecture_payload_of_extinction_and_extraction
      (finite_extinction_input_of_smoothability_and_boundary_surgery_packages
        dependencies.smoothability dependencies.surgery)
      extractSphere

/--
The strengthened certified reserved-endpoint payload factors through the
boundary finite-extinction endpoint and the certified extractor carried by the
topology package.
-/
theorem poincare_conjecture_payload_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, _derivation⟩
        exact
          poincare_conjecture_payload_of_extinction_and_extraction
            (finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere) := by
  apply Subsingleton.elim

/--
The strengthened certified reserved-endpoint payload agrees with the ordinary
certified aggregate reserved-endpoint payload after forgetting equation-boundary
data.
-/
theorem poincare_conjecture_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      poincare_conjecture_payload_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The certified aggregate dependency package is sufficient for the reserved
conditional endpoint.
-/
theorem poincare_conjecture_of_aggregate_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_conjecture_payload_of_aggregate_extraction_derivation_dependencies
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The certified aggregate reserved endpoint is selected from the named certified
aggregate reserved-endpoint payload.
-/
theorem poincare_conjecture_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_conjecture_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            poincare_conjecture_payload_of_aggregate_extraction_derivation_dependencies
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The certified aggregate reserved endpoint factors directly through finite
extinction and the certified extractor carried by the topology package.
-/
theorem poincare_conjecture_of_aggregate_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_conjecture_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, _derivation⟩
        exact
          poincare_conjecture_of_extinction_and_extraction
            (finite_extinction_input_of_smoothability_and_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate dependency package is sufficient for the
reserved conditional endpoint.
-/
theorem poincare_conjecture_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_conjecture_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The strengthened certified aggregate reserved endpoint is selected from the
named strengthened certified reserved-endpoint payload.
-/
theorem poincare_conjecture_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            poincare_conjecture_payload_of_equation_boundary_extraction_derivation_dependencies
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate reserved endpoint agrees with the ordinary
certified aggregate reserved endpoint after forgetting equation-boundary data.
-/
theorem poincare_conjecture_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      poincare_conjecture_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate reserved endpoint factors directly
through the boundary finite-extinction endpoint and the certified extractor
carried by the topology package.
-/
theorem poincare_conjecture_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_conjecture_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, _derivation⟩
        exact
          poincare_conjecture_of_extinction_and_extraction
            (finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere) := by
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
The strengthened aggregate dependency package is sufficient for the target
Poincare statement.
-/
theorem poincare_statement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_completion_payload_of_equation_boundary_dependencies
      dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The strengthened aggregate Poincare statement is selected from the named
strengthened aggregate completion payload.
-/
theorem poincare_statement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependencies dependencies =
      (by
        rcases poincare_completion_payload_of_equation_boundary_dependencies
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened aggregate Poincare statement agrees with the ordinary
aggregate Poincare statement after forgetting equation-boundary data.
-/
theorem poincare_statement_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependencies dependencies =
      poincare_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened aggregate Poincare statement agrees with the direct
boundary-package statement route from the full assembly layer.
-/
theorem poincare_statement_of_equation_boundary_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependencies dependencies =
      poincare_statement_of_boundary_surgery_and_topology_packages
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The strengthened aggregate Poincare statement also factors directly through
the boundary finite-extinction endpoint and the topology package's final
extractor.
-/
theorem poincare_statement_of_equation_boundary_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependencies dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extractSphere) := by
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
The certified aggregate Poincare statement also factors directly through the
finite-extinction endpoint and the extractor/derivation certificate carried by
the topology package.
-/
theorem poincare_statement_of_aggregate_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_input_of_smoothability_and_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package is sufficient for the target
Poincare statement through the certified extraction-derivation route while
retaining explicit equation-boundary data.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The strengthened certified aggregate Poincare statement is selected from the
named strengthened certified aggregate completion payload.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate Poincare statement agrees with the
certified aggregate Poincare statement after forgetting equation-boundary data.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      poincare_statement_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate Poincare statement agrees with the direct
boundary-package certified extraction-derivation statement route.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate Poincare statement also factors directly
through the finite-extinction endpoint and the extractor/derivation certificate
carried by the topology package.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery)
            extractSphere derivation) := by
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
The strengthened aggregate dependency package exposes the canonical
mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_equation_boundary_dependencies dependencies)

/--
The strengthened aggregate canonical topological sphere statement is the
canonical bridge applied to the named strengthened aggregate Poincare statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependencies
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_equation_boundary_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The strengthened aggregate canonical topological statement agrees with the
ordinary aggregate canonical topological statement after forgetting
equation-boundary data.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependencies
        dependencies =
      canonical_three_sphere_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened aggregate canonical topological statement agrees with the
direct boundary-package canonical statement route from the full assembly layer.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependencies
        dependencies =
      canonical_three_sphere_statement_of_boundary_surgery_and_topology_packages
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The strengthened aggregate canonical topological statement also factors
directly through the boundary finite-extinction endpoint and the topology
package's final extractor.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_extinction_and_extraction
              finiteExtinction extractSphere)) := by
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
The certified aggregate canonical topological statement also factors directly
through the finite-extinction endpoint and the extractor/derivation certificate
carried by the topology package.
-/
theorem canonical_three_sphere_statement_of_aggregate_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_input_of_smoothability_and_surgery_packages
                dependencies.smoothability dependencies.surgery)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package exposes the canonical
mathlib-shaped topological 3-sphere statement through the certified
extraction-derivation route while retaining explicit equation-boundary data.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_equation_boundary_extraction_derivation_dependencies
      dependencies)

/--
The strengthened certified aggregate canonical topological sphere statement is
the canonical bridge applied to the named strengthened certified aggregate
Poincare statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_equation_boundary_extraction_derivation_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate canonical topological statement agrees
with the certified aggregate canonical topological statement after forgetting
equation-boundary data.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      canonical_three_sphere_statement_of_aggregate_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate canonical topological statement agrees
with the direct boundary-package certified extraction-derivation canonical
route.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      canonical_three_sphere_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate canonical topological statement also
factors directly through the finite-extinction endpoint and the
extractor/derivation certificate carried by the topology package.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_input_of_smoothability_and_boundary_surgery_packages
                dependencies.smoothability dependencies.surgery)
              extractSphere derivation)) := by
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
The strengthened aggregate dependency package also discharges the project's
explicit completion criterion at the same universe.
-/
theorem completion_criterion_of_equation_boundary_dependencies
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases poincare_completion_payload_of_equation_boundary_dependencies
      dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The strengthened aggregate completion criterion is selected from the named
strengthened aggregate completion payload.
-/
theorem completion_criterion_of_equation_boundary_dependencies_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependencies
        witness dependencies =
      (by
        rcases poincare_completion_payload_of_equation_boundary_dependencies
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The strengthened aggregate completion criterion agrees with the ordinary
aggregate completion criterion after forgetting equation-boundary data.
-/
theorem completion_criterion_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependencies
        witness dependencies =
      completion_criterion_of_dependencies
        witness (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened aggregate completion criterion agrees with the direct
boundary-package Poincare statement route.
-/
theorem completion_criterion_of_equation_boundary_dependencies_to_boundary_route_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependencies
        witness dependencies =
      completionCriterionAtUniverse_of_poincareConjectureStatement
        witness
        (poincare_statement_of_boundary_surgery_and_topology_packages
          dependencies.smoothability dependencies.surgery dependencies.topology) := by
  apply Subsingleton.elim

/--
The strengthened aggregate completion criterion also factors directly through
the boundary finite-extinction endpoint and the topology package's final
extractor.
-/
theorem completion_criterion_of_equation_boundary_dependencies_to_finite_extinction_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependencies
        witness dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        let extractSphere :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_extinction_and_extraction
              finiteExtinction extractSphere)) := by
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

/--
The certified aggregate completion criterion also factors directly through the
finite-extinction endpoint and the extractor/derivation certificate carried by
the topology package.
-/
theorem completion_criterion_of_aggregate_extraction_derivation_dependencies_to_finite_extinction_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_aggregate_extraction_derivation_dependencies
      witness dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_input_of_smoothability_and_surgery_packages
                dependencies.smoothability dependencies.surgery)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The strengthened aggregate dependency package discharges the project's explicit
completion criterion through the certified extraction-derivation route while
retaining explicit equation-boundary data.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependencies
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The strengthened certified aggregate completion criterion is selected from the
named strengthened certified aggregate completion payload.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependencies_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependencies
      witness dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies
              dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate completion criterion agrees with the
certified aggregate completion criterion after forgetting equation-boundary
data.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependencies
        witness dependencies =
      completion_criterion_of_aggregate_extraction_derivation_dependencies
        witness (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate completion criterion agrees with the
direct boundary-package certified extraction-derivation statement route.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependencies_to_boundary_route_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependencies
        witness dependencies =
      completionCriterionAtUniverse_of_poincareConjectureStatement
        witness
        (poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
          dependencies.smoothability dependencies.surgery dependencies.topology) := by
  apply Subsingleton.elim

/--
The strengthened certified aggregate completion criterion also factors directly
through the finite-extinction endpoint and the extractor/derivation certificate
carried by the topology package.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependencies
        witness dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_input_of_smoothability_and_boundary_surgery_packages
                dependencies.smoothability dependencies.surgery)
              extractSphere derivation)) := by
  apply Subsingleton.elim

end Poincare
