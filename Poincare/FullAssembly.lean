/-
End-to-end conditional assembly for the Poincare target statement.

This file does not prove the missing geometric or topological inputs. It checks
that the typed interfaces introduced in the lower layers compose all the way to
`PoincareConjectureStatement`.
-/

import Poincare.Assembly
import Poincare.Smoothability
import Poincare.TopologyExtraction

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The explicit smoothability and surgery package route exposes, for every target
topological 3-manifold, the smooth manifold evidence, theorem-shaped
finite-extinction statement, full sub-obligation statement route, derivation
certificate, and resulting finite-extinction witness.
-/
theorem finite_extinction_statement_payload_of_smoothability_and_surgery_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        ∃ _manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _packageStatement : FiniteExtinctionStatement n M,
        ∃ _subobligationsStatement :
          FiniteExtinctionSubobligationsStatement flow surgery control,
        ∃ _viaSubobligationsStatement : FiniteExtinctionStatement n M,
        ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
          FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _
  let manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M :=
    smoothable_of_smoothability_package smoothabilityPackage M
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := manifoldEvidence
  rcases surgeryPackages M with ⟨⟨n, package⟩⟩
  rcases finite_extinction_statement_payload_of_surgery_package
      package with
    ⟨flow, surgery, control, packageStatement, subobligationsStatement,
      viaSubobligationsStatement, derivation, finiteExtinction⟩
  exact ⟨manifoldEvidence, n, flow, surgery, control, packageStatement,
    subobligationsStatement, viaSubobligationsStatement, derivation,
    finiteExtinction⟩

/--
The explicit smoothability and surgery package route supplies the final
finite-extinction input consumed by the Poincare assembly theorem through the
named theorem-shaped finite-extinction payload.
-/
theorem finite_extinction_input_of_smoothability_and_surgery_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _
  rcases finite_extinction_statement_payload_of_smoothability_and_surgery_packages
      smoothabilityPackage surgeryPackages M with
    ⟨_manifoldEvidence, _n, _flow, _surgery, _control,
      _packageStatement, _subobligationsStatement,
      _viaSubobligationsStatement, _derivation, finiteExtinction⟩
  exact finiteExtinction

/--
The explicit package route supplies the two theorem-shaped inputs consumed by
the final finite-extinction/topology-extraction assembly theorem.
-/
theorem poincare_assembly_inputs_payload_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionImpliesSphereStatement.{u} := by
  let finiteExtinction :=
    finite_extinction_input_of_smoothability_and_surgery_packages
      smoothabilityPackage surgeryPackages
  rcases topology_extraction_payload_of_topology_package topologyPackage with
    ⟨_topologyStatement, extractSphere⟩
  exact ⟨finiteExtinction, extractSphere⟩

/--
The explicit package route also exposes the finite-extinction input together
with a final extractor and its topology derivation certificate.
-/
theorem poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  rcases topology_extraction_derivation_payload_of_topology_package
      topologyPackage with
    ⟨extractSphere, derivation⟩
  exact ⟨finite_extinction_input_of_smoothability_and_surgery_packages
      smoothabilityPackage surgeryPackages,
    extractSphere, derivation⟩

/--
The smoothability and surgery package route, together with the theorem-shaped
topology extraction statement, supplies the two direct theorem inputs needed by
the final finite-extinction/topology-extraction assembly theorem.
-/
theorem poincare_assembly_inputs_payload_of_surgery_and_topology_extraction_statement
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionTopologyExtractionStatement.{u} := by
  exact ⟨finite_extinction_input_of_smoothability_and_surgery_packages
      smoothabilityPackage surgeryPackages,
    topologyStatement⟩

/--
The theorem-shaped topology route assembly-input payload is the finite
extinction input paired with the supplied topology extraction statement.
-/
theorem poincare_assembly_inputs_payload_of_surgery_and_topology_extraction_statement_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_assembly_inputs_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement =
      ⟨finite_extinction_input_of_smoothability_and_surgery_packages
        smoothabilityPackage surgeryPackages,
        topologyStatement⟩ := by
  apply Subsingleton.elim

/--
The smoothability and surgery package route, together with the theorem-shaped
topology extraction statement, exposes the final finite-extinction input,
the topology statement, target statement, and completion criterion.
-/
theorem poincare_target_payload_of_surgery_and_topology_extraction_statement
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _topologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_assembly_inputs_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement with
    ⟨finiteExtinction, topologyStatement⟩
  rcases poincare_payload_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, topologyStatement, target, criterion⟩

/--
The theorem-shaped topology target payload is selected from its assembly-input
payload and the finite-extinction/topology-extraction assembly bridge.
-/
theorem poincare_target_payload_of_surgery_and_topology_extraction_statement_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_target_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement =
      (by
        rcases
            poincare_assembly_inputs_payload_of_surgery_and_topology_extraction_statement
              smoothabilityPackage surgeryPackages topologyStatement with
          ⟨finiteExtinction, topologyStatement⟩
        rcases poincare_payload_of_finite_extinction_and_topology_extraction_statement
            finiteExtinction topologyStatement with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, topologyStatement, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The smoothability and surgery package route, together with a final extractor
and its topology derivation certificate, supplies the finite-extinction input
and certified extraction input needed by the final assembly theorem.
-/
theorem poincare_assembly_inputs_payload_of_surgery_and_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  exact ⟨finite_extinction_input_of_smoothability_and_surgery_packages
      smoothabilityPackage surgeryPackages,
    extractSphere, derivation⟩

/--
The extractor/derivation route assembly-input payload is the finite extinction
input paired with the supplied certified extractor.
-/
theorem poincare_assembly_inputs_payload_of_surgery_and_extraction_derivation_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    poincare_assembly_inputs_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation =
      ⟨finite_extinction_input_of_smoothability_and_surgery_packages
        smoothabilityPackage surgeryPackages,
        extractSphere, derivation⟩ := by
  apply Subsingleton.elim

/--
The smoothability and surgery package route, together with a final extractor
and its topology derivation certificate, exposes the finite-extinction input,
certified extraction input, target statement, and completion criterion.
-/
theorem poincare_target_payload_of_surgery_and_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere,
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_assembly_inputs_payload_of_surgery_and_extraction_derivation
        smoothabilityPackage surgeryPackages extractSphere derivation with
    ⟨finiteExtinction, extractSphere, derivation⟩
  rcases poincare_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extractSphere, derivation, target, criterion⟩

/--
The extractor/derivation target payload is selected from its assembly-input
payload and the finite-extinction/extractor-derivation assembly bridge.
-/
theorem poincare_target_payload_of_surgery_and_extraction_derivation_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    poincare_target_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation =
      (by
        rcases
            poincare_assembly_inputs_payload_of_surgery_and_extraction_derivation
              smoothabilityPackage surgeryPackages extractSphere derivation with
          ⟨finiteExtinction, extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extractSphere, derivation, target,
          criterion⟩) := by
  apply Subsingleton.elim

/--
The explicit package route exposes the finite-extinction input, certified final
extractor, target statement, and completion criterion.
-/
theorem poincare_target_payload_of_surgery_and_topology_package_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
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
      poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation
        smoothabilityPackage surgeryPackages topologyPackage with
    ⟨_finiteExtinction, extractSphere, derivation⟩
  exact poincare_target_payload_of_surgery_and_extraction_derivation
    smoothabilityPackage surgeryPackages extractSphere derivation

/--
The explicit package route exposes the final finite-extinction input,
post-extinction topology input, target statement, and universe-indexed
completion criterion through one named payload.
-/
theorem poincare_target_payload_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_assembly_inputs_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage with
    ⟨finiteExtinction, extractSphere⟩
  rcases poincare_payload_of_extinction_and_extraction
      finiteExtinction extractSphere with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extractSphere, target, criterion⟩

/--
If every compact simply connected topological 3-manifold carries the smooth
regularity needed by the surgery interface, every such smooth 3-manifold has a
completed surgery package, and the post-extinction topology extraction package
exists, then the explicit packages, final assembly inputs, and target statement
are available.
-/
theorem poincare_full_assembly_payload_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
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
  rcases poincare_target_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage with
    ⟨finiteExtinction, extractSphere, target, _criterion⟩
  exact ⟨smoothabilityPackage, surgeryPackages, topologyPackage,
    finiteExtinction, extractSphere,
    target⟩

/--
If every compact simply connected topological 3-manifold carries the smooth
regularity needed by the surgery interface, every such smooth 3-manifold has a
completed surgery package, and the post-extinction topology extraction package
exists, then the final finite-extinction/extraction assembly inputs and target
statement are available.
-/
theorem poincare_assembly_payload_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
      PoincareConjectureStatement.{u} := by
  rcases poincare_full_assembly_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage with
    ⟨_smoothabilityPackage, _surgeryPackages, _topologyPackage,
      finiteExtinction, extractSphere, target⟩
  exact ⟨finiteExtinction, extractSphere, target⟩

/--
The explicit package route exposes the local target and the universe-indexed
completion criterion as one payload.
-/
theorem poincare_completion_payload_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage with
    ⟨_finiteExtinction, _extractSphere, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The smoothability and surgery package route, together with the theorem-shaped
topology extraction statement, exposes the target and completion criterion as
one payload.
-/
theorem poincare_completion_payload_of_surgery_and_topology_extraction_statement
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement with
    ⟨_finiteExtinction, _topologyStatement, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The theorem-shaped topology completion payload is selected from the
theorem-shaped topology target payload.
-/
theorem poincare_completion_payload_of_surgery_and_topology_extraction_statement_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_completion_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement =
      (by
        rcases
            poincare_target_payload_of_surgery_and_topology_extraction_statement
              smoothabilityPackage surgeryPackages topologyStatement with
          ⟨_finiteExtinction, _topologyStatement, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The smoothability and surgery package route, together with a final extractor
and its topology derivation certificate, exposes the target and completion
criterion as one payload.
-/
theorem poincare_completion_payload_of_surgery_and_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation with
    ⟨_finiteExtinction, _extractSphere, _derivation, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The extractor/derivation completion payload is selected from the
extractor/derivation target payload.
-/
theorem poincare_completion_payload_of_surgery_and_extraction_derivation_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    poincare_completion_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation =
      (by
        rcases poincare_target_payload_of_surgery_and_extraction_derivation
            smoothabilityPackage surgeryPackages extractSphere derivation with
          ⟨_finiteExtinction, _extractSphere, _derivation, target,
            criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The explicit package route, with the topology package unpacked into a certified
extractor, exposes the target and completion criterion as one payload.
-/
theorem poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_surgery_and_topology_package_extraction_derivation
        smoothabilityPackage surgeryPackages topologyPackage with
    ⟨_finiteExtinction, _extractSphere, _derivation, target, criterion⟩
  exact ⟨target, criterion⟩

/--
If every compact simply connected topological 3-manifold carries the smooth
regularity needed by the surgery interface, every such smooth 3-manifold has a
completed surgery package, and the post-extinction topology extraction package
exists, then the project's Poincare statement follows.
-/
theorem poincare_statement_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_completion_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage with
    ⟨target, _criterion⟩
  exact target

/--
If the smoothability and surgery package route is available and the stronger
theorem-shaped topology extraction statement is available, then the project's
Poincare statement follows.
-/
theorem poincare_statement_of_surgery_and_topology_extraction_statement
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_target_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement with
    ⟨_finiteExtinction, _topologyStatement, target, _criterion⟩
  exact target

/--
The theorem-shaped topology Poincare statement is selected from the
theorem-shaped topology target payload.
-/
theorem poincare_statement_of_surgery_and_topology_extraction_statement_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_statement_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement =
      (by
        rcases
            poincare_target_payload_of_surgery_and_topology_extraction_statement
              smoothabilityPackage surgeryPackages topologyStatement with
          ⟨_finiteExtinction, _topologyStatement, target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
If the smoothability and surgery package route is available and a final
extractor is paired with its topology derivation certificate, then the project's
Poincare statement follows.
-/
theorem poincare_statement_of_surgery_and_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_completion_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation with
    ⟨target, _criterion⟩
  exact target

/--
The extractor/derivation Poincare statement is selected from the
extractor/derivation completion payload.
-/
theorem poincare_statement_of_surgery_and_extraction_derivation_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    poincare_statement_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation =
      (by
        rcases poincare_completion_payload_of_surgery_and_extraction_derivation
            smoothabilityPackage surgeryPackages extractSphere derivation with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
If the explicit smoothability, surgery, and topology packages are available,
then unpacking the topology package into a certified extractor also proves the
project's Poincare statement.
-/
theorem poincare_statement_of_surgery_and_topology_package_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
        smoothabilityPackage surgeryPackages topologyPackage with
    ⟨target, _criterion⟩
  exact target

/--
The explicit smoothability, surgery, and topology packages also expose the
canonical mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage)

/--
The smoothability and surgery package route, together with the theorem-shaped
topology extraction statement, exposes the canonical topological 3-sphere
statement.
-/
theorem canonical_three_sphere_statement_of_surgery_and_topology_extraction_statement
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement)

/--
The theorem-shaped topology canonical statement is the canonical bridge applied
to the theorem-shaped topology Poincare statement.
-/
theorem canonical_three_sphere_statement_of_surgery_and_topology_extraction_statement_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_three_sphere_statement_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_surgery_and_topology_extraction_statement
          smoothabilityPackage surgeryPackages topologyStatement) := by
  apply Subsingleton.elim

/--
The smoothability and surgery package route, together with a final extractor
and its topology derivation certificate, exposes the canonical topological
3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_surgery_and_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation)

/--
The extractor/derivation canonical statement is the canonical bridge applied to
the extractor/derivation Poincare statement.
-/
theorem canonical_three_sphere_statement_of_surgery_and_extraction_derivation_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    canonical_three_sphere_statement_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_surgery_and_extraction_derivation
          smoothabilityPackage surgeryPackages extractSphere derivation) := by
  apply Subsingleton.elim

/--
The explicit package route, with the topology package unpacked into a certified
extractor, exposes the canonical topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_surgery_and_topology_package_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_surgery_and_topology_package_extraction_derivation
      smoothabilityPackage surgeryPackages topologyPackage)

end Poincare
