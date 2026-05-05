/-
Canonical completion target for the project.

This module intentionally does not define `poincare_conjecture`. It records the
exact proof target and the dependency package that currently blocks it.
-/

import Poincare.DependencyCrosswalk
import Poincare.DependencyProjections

universe u

open scoped Manifold ContDiff

namespace Poincare

/-- The canonical theorem name that must exist for the project to be complete. -/
def canonicalCompletionTheoremName : String :=
  "poincare_conjecture"

/-- The reserved final theorem name for the completed proof. -/
theorem canonicalCompletionTheoremName_eq :
    canonicalCompletionTheoremName = "poincare_conjecture" :=
  rfl

/-- The proposition that the canonical theorem must prove. -/
def canonicalCompletionTarget : Prop :=
  PoincareConjectureStatement.{u}

/-- The canonical completion target is exactly the project Poincare statement. -/
theorem canonicalCompletionTarget_eq :
    canonicalCompletionTarget.{u} = PoincareConjectureStatement.{u} :=
  rfl

/--
The canonical completion target is logically equivalent to the project target
statement.
-/
theorem canonicalCompletionTarget_iff_poincareConjectureStatement :
    canonicalCompletionTarget.{u} ↔ PoincareConjectureStatement.{u} :=
  Iff.rfl

/--
The canonical completion target is the same proposition as the explicit
universe-indexed completion criterion.
-/
theorem canonicalCompletionTarget_eq_completionCriterionAtUniverse
    (witness : Type u) :
    canonicalCompletionTarget.{u} = CompletionCriterionAtUniverse witness :=
  rfl

/--
The canonical completion target is logically equivalent to the explicit
universe-indexed completion criterion.
-/
theorem canonicalCompletionTarget_iff_completionCriterionAtUniverse
    (witness : Type u) :
    canonicalCompletionTarget.{u} ↔ CompletionCriterionAtUniverse witness :=
  Iff.rfl

/--
A proof of the canonical completion target supplies the theorem-shaped
post-extinction extraction interface.
-/
theorem extinction_extraction_of_canonical_completion_target
    (target : canonicalCompletionTarget.{u}) :
    ExtinctionImpliesSphereStatement.{u} :=
  extinction_extraction_of_poincare_statement target

/--
Universal finite extinction and the post-extinction extraction theorem prove
the canonical completion target.
-/
theorem canonical_completion_target_of_extinction_and_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonicalCompletionTarget.{u} :=
  poincare_statement_of_extinction_and_extraction finiteExtinction extractSphere

/--
Once universal finite extinction is available, the canonical completion target
is equivalent to the theorem-shaped post-extinction extraction interface.
-/
theorem canonicalCompletionTarget_iff_extinction_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    canonicalCompletionTarget.{u} ↔ ExtinctionImpliesSphereStatement.{u} :=
  poincare_statement_iff_extinction_extraction finiteExtinction

/-- A proof of the canonical target discharges the explicit completion criterion. -/
theorem completion_criterion_of_canonical_completion_target
    (witness : Type u) (target : canonicalCompletionTarget.{u}) :
    CompletionCriterionAtUniverse witness :=
  target

/--
A proof of the canonical completion target exposes the canonical target and the
explicit universe-indexed completion criterion as one payload.
-/
theorem canonical_completion_payload_of_canonical_completion_target
    (target : canonicalCompletionTarget.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact ⟨target, fun witness =>
    completion_criterion_of_canonical_completion_target witness target⟩

/--
A proof of the canonical completion target also exposes the project Poincare
target and explicit universe-indexed completion criterion as one payload.
-/
theorem poincare_completion_payload_of_canonical_completion_target
    (target : canonicalCompletionTarget.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact ⟨target, fun witness =>
    completion_criterion_of_canonical_completion_target witness target⟩

/--
A Poincare completion payload is already a canonical completion payload, since
the canonical target is definitionally the project Poincare statement.
-/
theorem canonical_completion_payload_of_poincare_completion_payload
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases payload with ⟨target, criterion⟩
  exact ⟨target, criterion⟩

/--
The canonical completion payload contains a proof of the canonical completion
target.
-/
theorem canonical_completion_target_of_canonical_completion_payload
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonicalCompletionTarget.{u} := by
  rcases payload with ⟨target, _criterion⟩
  exact target

/--
The project Poincare completion payload contains a proof of the canonical
completion target, since both target propositions are definitionally equal.
-/
theorem canonicalCompletionTarget_of_poincare_completion_payload
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_canonical_completion_payload
    (canonical_completion_payload_of_poincare_completion_payload payload)

/--
The canonical completion payload discharges the explicit universe-indexed
completion criterion.
-/
theorem completion_criterion_of_canonical_completion_payload
    (witness : Type u)
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    CompletionCriterionAtUniverse witness := by
  rcases payload with ⟨_target, criterion⟩
  exact criterion witness

/--
The canonical completion target is equivalent to the canonical completion
payload.
-/
theorem canonicalCompletionTarget_iff_canonical_completion_payload :
    canonicalCompletionTarget.{u} ↔
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨canonical_completion_payload_of_canonical_completion_target,
    canonical_completion_target_of_canonical_completion_payload⟩

/--
The explicit universe-indexed completion criterion is equivalent to the
canonical completion payload.
-/
theorem completionCriterionAtUniverse_iff_canonical_completion_payload
    (witness : Type u) :
    CompletionCriterionAtUniverse witness ↔
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  (canonicalCompletionTarget_iff_completionCriterionAtUniverse witness).symm.trans
    canonicalCompletionTarget_iff_canonical_completion_payload

/--
A proof of the explicit universe-indexed completion criterion exposes the
canonical completion payload directly.
-/
theorem canonical_completion_payload_of_completion_criterion
    (witness : Type u) (criterion : CompletionCriterionAtUniverse witness) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  (completionCriterionAtUniverse_iff_canonical_completion_payload witness).mp
    criterion

/--
A canonical completion payload is also a project Poincare completion payload,
since the canonical target is definitionally the project target statement.
-/
theorem poincare_completion_payload_of_canonical_completion_payload
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases payload with ⟨target, criterion⟩
  exact ⟨target, criterion⟩

/--
The canonical completion payload is equivalent to the project Poincare
completion payload.
-/
theorem canonical_completion_payload_iff_poincare_completion_payload :
    (∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness) ↔
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨poincare_completion_payload_of_canonical_completion_payload,
    canonical_completion_payload_of_poincare_completion_payload⟩

/--
The canonical completion target/project target iff is definitionally the
identity iff.
-/
theorem canonicalCompletionTarget_iff_poincareConjectureStatement_eq :
    canonicalCompletionTarget_iff_poincareConjectureStatement =
      Iff.rfl := by
  apply Subsingleton.elim

/--
The canonical completion target/completion criterion iff is definitionally the
identity iff.
-/
theorem canonicalCompletionTarget_iff_completionCriterionAtUniverse_eq
    (witness : Type u) :
    canonicalCompletionTarget_iff_completionCriterionAtUniverse witness =
      Iff.rfl := by
  apply Subsingleton.elim

/--
The post-extinction extraction interface is obtained through the named project
target route.
-/
theorem extinction_extraction_of_canonical_completion_target_eq
    (target : canonicalCompletionTarget.{u}) :
    extinction_extraction_of_canonical_completion_target target =
      extinction_extraction_of_poincare_statement target := by
  apply Subsingleton.elim

/--
The canonical completion target from finite extinction and extraction is the
named project statement assembly route.
-/
theorem canonical_completion_target_of_extinction_and_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_completion_target_of_extinction_and_extraction
      finiteExtinction extractSphere =
      poincare_statement_of_extinction_and_extraction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The canonical target/extraction iff is the named project statement/extraction
iff.
-/
theorem canonicalCompletionTarget_iff_extinction_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    canonicalCompletionTarget_iff_extinction_extraction finiteExtinction =
      poincare_statement_iff_extinction_extraction finiteExtinction := by
  apply Subsingleton.elim

/--
A canonical target proof discharges the completion criterion by identity.
-/
theorem completion_criterion_of_canonical_completion_target_eq
    (witness : Type u) (target : canonicalCompletionTarget.{u}) :
    completion_criterion_of_canonical_completion_target witness target =
      target := by
  apply Subsingleton.elim

/--
The canonical target completion payload pairs the target proof with the named
criterion projection.
-/
theorem canonical_completion_payload_of_canonical_completion_target_eq
    (target : canonicalCompletionTarget.{u}) :
    canonical_completion_payload_of_canonical_completion_target target =
      ⟨target, fun witness =>
        completion_criterion_of_canonical_completion_target
          witness target⟩ := by
  apply Subsingleton.elim

/--
The project completion payload from a canonical target proof pairs the same
target proof with the named canonical criterion projection.
-/
theorem poincare_completion_payload_of_canonical_completion_target_eq
    (target : canonicalCompletionTarget.{u}) :
    poincare_completion_payload_of_canonical_completion_target target =
      ⟨target, fun witness =>
        completion_criterion_of_canonical_completion_target
          witness target⟩ := by
  apply Subsingleton.elim

/--
The canonical completion payload bridge destructures the project completion
payload and rebuilds the same pair.
-/
theorem canonical_completion_payload_of_poincare_completion_payload_eq
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonical_completion_payload_of_poincare_completion_payload payload =
      (by
        rcases payload with ⟨target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The canonical completion payload target projection destructures the payload.
-/
theorem canonical_completion_target_of_canonical_completion_payload_eq
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonical_completion_target_of_canonical_completion_payload payload =
      (by
        rcases payload with ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The project-payload to canonical-target projection factors through the named
canonical payload conversion.
-/
theorem canonicalCompletionTarget_of_poincare_completion_payload_eq
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonicalCompletionTarget_of_poincare_completion_payload payload =
      canonical_completion_target_of_canonical_completion_payload
        (canonical_completion_payload_of_poincare_completion_payload
          payload) := by
  apply Subsingleton.elim

/--
The canonical completion payload criterion projection destructures the payload.
-/
theorem completion_criterion_of_canonical_completion_payload_eq
    (witness : Type u)
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_criterion_of_canonical_completion_payload witness payload =
      (by
        rcases payload with ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The canonical target/canonical-payload iff is the pair of the named constructor
and target projection.
-/
theorem canonicalCompletionTarget_iff_canonical_completion_payload_eq :
    canonicalCompletionTarget_iff_canonical_completion_payload =
      ⟨canonical_completion_payload_of_canonical_completion_target,
        canonical_completion_target_of_canonical_completion_payload⟩ := by
  apply Subsingleton.elim

/--
The completion criterion/canonical-payload iff factors through the canonical
target/completion criterion iff.
-/
theorem completionCriterionAtUniverse_iff_canonical_completion_payload_eq
    (witness : Type u) :
    completionCriterionAtUniverse_iff_canonical_completion_payload witness =
      (canonicalCompletionTarget_iff_completionCriterionAtUniverse
        witness).symm.trans
          canonicalCompletionTarget_iff_canonical_completion_payload := by
  apply Subsingleton.elim

/--
The direct criterion-to-canonical-payload constructor is the forward direction
of the named iff.
-/
theorem canonical_completion_payload_of_completion_criterion_eq
    (witness : Type u) (criterion : CompletionCriterionAtUniverse witness) :
    canonical_completion_payload_of_completion_criterion witness criterion =
      (completionCriterionAtUniverse_iff_canonical_completion_payload
        witness).mp criterion := by
  apply Subsingleton.elim

/--
The project completion payload bridge destructures the canonical completion
payload and rebuilds the same pair.
-/
theorem poincare_completion_payload_of_canonical_completion_payload_eq
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    poincare_completion_payload_of_canonical_completion_payload payload =
      (by
        rcases payload with ⟨target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The canonical/project completion payload iff is the pair of the named payload
conversion routes.
-/
theorem canonical_completion_payload_iff_poincare_completion_payload_eq :
    canonical_completion_payload_iff_poincare_completion_payload =
      ⟨poincare_completion_payload_of_canonical_completion_payload,
        canonical_completion_payload_of_poincare_completion_payload⟩ := by
  apply Subsingleton.elim

/--
Universal finite extinction and the post-extinction extraction theorem expose
the canonical completion target and explicit completion criterion as one
payload.
-/
theorem canonical_completion_payload_of_extinction_and_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_payload_of_extinction_and_extraction
      finiteExtinction extractSphere)

/--
Universal finite extinction and the post-extinction extraction theorem discharge
the universe-indexed completion criterion through the canonical payload.
-/
theorem canonical_completion_criterion_of_extinction_and_extraction
    (witness : Type u)
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_extinction_and_extraction
      finiteExtinction extractSphere with
    ⟨_target, criterion⟩
  exact criterion witness

/--
Universal finite extinction plus the theorem-shaped topology extraction
statement exposes the canonical completion target and explicit completion
criterion as one payload.
-/
theorem canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_payload_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement)

/--
Universal finite extinction plus the theorem-shaped topology extraction
statement proves the canonical completion target through the canonical payload.
-/
theorem canonical_completion_target_of_finite_extinction_and_topology_extraction_statement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases
      canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement
        finiteExtinction topologyStatement with
    ⟨target, _criterion⟩
  exact target

/--
Universal finite extinction plus the theorem-shaped topology extraction
statement discharges the universe-indexed completion criterion through the
canonical payload.
-/
theorem canonical_completion_criterion_of_finite_extinction_and_topology_extraction_statement
    (witness : Type u)
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement
        finiteExtinction topologyStatement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
Universal finite extinction plus a final extractor and its topology derivation
certificate exposes the canonical completion target and explicit completion
criterion as one payload.
-/
theorem canonical_completion_payload_of_finite_extinction_and_extraction_derivation
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation)

/--
Universal finite extinction plus a final extractor and its topology derivation
certificate proves the canonical completion target.
-/
theorem canonical_completion_target_of_finite_extinction_and_extraction_derivation
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation with
    ⟨target, _criterion⟩
  exact target

/--
Universal finite extinction plus a final extractor and its topology derivation
certificate discharges the universe-indexed completion criterion.
-/
theorem canonical_completion_criterion_of_finite_extinction_and_extraction_derivation
    (witness : Type u)
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation with
    ⟨_target, criterion⟩
  exact criterion witness

/-- A proof of the explicit completion criterion gives the canonical target. -/
theorem canonical_completion_target_of_completion_criterion
    (witness : Type u) (criterion : CompletionCriterionAtUniverse witness) :
    canonicalCompletionTarget.{u} :=
  criterion

/--
The extinction/extraction canonical payload is obtained through the shared
project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_extinction_and_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_completion_payload_of_extinction_and_extraction
      finiteExtinction extractSphere =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_payload_of_extinction_and_extraction
          finiteExtinction extractSphere) := by
  apply Subsingleton.elim

/--
The extinction/extraction criterion projection destructures the named canonical
payload.
-/
theorem canonical_completion_criterion_of_extinction_and_extraction_eq
    (witness : Type u)
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_completion_criterion_of_extinction_and_extraction
      witness finiteExtinction extractSphere =
      (by
        rcases canonical_completion_payload_of_extinction_and_extraction
            finiteExtinction extractSphere with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The finite-extinction/topology-statement canonical payload is obtained through
the shared project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_payload_of_finite_extinction_and_topology_extraction_statement
          finiteExtinction topologyStatement) := by
  apply Subsingleton.elim

/--
The finite-extinction/topology-statement target projection destructures the
named canonical payload.
-/
theorem canonical_completion_target_of_finite_extinction_and_topology_extraction_statement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_target_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement =
      (by
        rcases
            canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement
            finiteExtinction topologyStatement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The finite-extinction/topology-statement criterion projection destructures the
named canonical payload.
-/
theorem canonical_completion_criterion_of_finite_extinction_and_topology_extraction_statement_eq
    (witness : Type u)
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_criterion_of_finite_extinction_and_topology_extraction_statement
      witness finiteExtinction topologyStatement =
      (by
        rcases
            canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement
            finiteExtinction topologyStatement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The finite-extinction/certified-extraction canonical payload is obtained through
the shared project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_finite_extinction_and_extraction_derivation_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    canonical_completion_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_payload_of_finite_extinction_and_extraction_derivation
          finiteExtinction extractSphere derivation) := by
  apply Subsingleton.elim

/--
The finite-extinction/certified-extraction target projection destructures the
named canonical payload.
-/
theorem canonical_completion_target_of_finite_extinction_and_extraction_derivation_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    canonical_completion_target_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation =
      (by
        rcases canonical_completion_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The finite-extinction/certified-extraction criterion projection destructures
the named canonical payload.
-/
theorem canonical_completion_criterion_of_finite_extinction_and_extraction_derivation_eq
    (witness : Type u)
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u} extractSphere) :
    canonical_completion_criterion_of_finite_extinction_and_extraction_derivation
      witness finiteExtinction extractSphere derivation =
      (by
        rcases canonical_completion_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The canonical target from an explicit completion criterion is obtained by
identity.
-/
theorem canonical_completion_target_of_completion_criterion_eq
    (witness : Type u) (criterion : CompletionCriterionAtUniverse witness) :
    canonical_completion_target_of_completion_criterion witness criterion =
      criterion := by
  apply Subsingleton.elim

/--
The explicit smoothability, surgery, and topology packages also produce the
canonical completion target and explicit completion criterion payload.
-/
theorem canonical_completion_payload_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage)

/--
The explicit package route proves the canonical completion target through the
canonical completion payload.
-/
theorem canonical_completion_target_of_surgery_and_topology_packages
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage with
    ⟨target, _criterion⟩
  exact target

/--
The explicit package route discharges the universe-indexed completion criterion
through the canonical completion payload.
-/
theorem canonical_completion_criterion_of_surgery_and_topology_packages
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The smoothability and surgery package route, together with a theorem-shaped
topology extraction statement, also produces the canonical completion target
and explicit completion criterion payload.
-/
theorem canonical_completion_payload_of_surgery_and_topology_extraction_statement
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement)

/--
The theorem-shaped topology route proves the canonical completion target through
the canonical completion payload.
-/
theorem canonical_completion_target_of_surgery_and_topology_extraction_statement
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement with
    ⟨target, _criterion⟩
  exact target

/--
The theorem-shaped topology route discharges the universe-indexed completion
criterion through the canonical completion payload.
-/
theorem canonical_completion_criterion_of_surgery_and_topology_extraction_statement
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The smoothability and surgery package route, together with a final extractor
and its topology derivation certificate, produces the canonical completion
target and explicit completion criterion payload.
-/
theorem canonical_completion_payload_of_surgery_and_extraction_derivation
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
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation)

/--
The smoothability and surgery package route, together with a final extractor
and its topology derivation certificate, proves the canonical completion target.
-/
theorem canonical_completion_target_of_surgery_and_extraction_derivation
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
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation with
    ⟨target, _criterion⟩
  exact target

/--
The smoothability and surgery package route, together with a final extractor
and its topology derivation certificate, discharges the universe-indexed
completion criterion.
-/
theorem canonical_completion_criterion_of_surgery_and_extraction_derivation
    (witness : Type u)
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
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The explicit package route, with the topology package unpacked into a certified
extractor, produces the canonical completion target and explicit completion
criterion payload.
-/
theorem canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
      smoothabilityPackage surgeryPackages topologyPackage)

/--
The explicit package route, with the topology package unpacked into a certified
extractor, proves the canonical completion target.
-/
theorem canonical_completion_target_of_surgery_and_topology_package_extraction_derivation
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases
      canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation
        smoothabilityPackage surgeryPackages topologyPackage with
    ⟨target, _criterion⟩
  exact target

/--
The explicit package route, with the topology package unpacked into a certified
extractor, discharges the universe-indexed completion criterion.
-/
theorem canonical_completion_criterion_of_surgery_and_topology_package_extraction_derivation
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation
        smoothabilityPackage surgeryPackages topologyPackage with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The explicit package canonical payload is obtained through the shared
project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_surgery_and_topology_packages_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_completion_payload_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_surgery_and_topology_packages
          smoothabilityPackage surgeryPackages topologyPackage) := by
  apply Subsingleton.elim

/-- The explicit package target projection destructures the named payload. -/
theorem canonical_completion_target_of_surgery_and_topology_packages_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_completion_target_of_surgery_and_topology_packages
      smoothabilityPackage surgeryPackages topologyPackage =
      (by
        rcases canonical_completion_payload_of_surgery_and_topology_packages
            smoothabilityPackage surgeryPackages topologyPackage with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/-- The explicit package criterion projection destructures the named payload. -/
theorem canonical_completion_criterion_of_surgery_and_topology_packages_eq
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_completion_criterion_of_surgery_and_topology_packages
      witness smoothabilityPackage surgeryPackages topologyPackage =
      (by
        rcases canonical_completion_payload_of_surgery_and_topology_packages
            smoothabilityPackage surgeryPackages topologyPackage with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology route canonical payload is obtained through the
shared project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_surgery_and_topology_extraction_statement_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_payload_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_surgery_and_topology_extraction_statement
          smoothabilityPackage surgeryPackages topologyStatement) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology route target projection destructures the named
payload.
-/
theorem canonical_completion_target_of_surgery_and_topology_extraction_statement_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_target_of_surgery_and_topology_extraction_statement
      smoothabilityPackage surgeryPackages topologyStatement =
      (by
        rcases canonical_completion_payload_of_surgery_and_topology_extraction_statement
            smoothabilityPackage surgeryPackages topologyStatement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology route criterion projection destructures the named
payload.
-/
theorem canonical_completion_criterion_of_surgery_and_topology_extraction_statement_eq
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_criterion_of_surgery_and_topology_extraction_statement
      witness smoothabilityPackage surgeryPackages topologyStatement =
      (by
        rcases canonical_completion_payload_of_surgery_and_topology_extraction_statement
            smoothabilityPackage surgeryPackages topologyStatement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The surgery-plus-extractor canonical payload is obtained through the shared
project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_surgery_and_extraction_derivation_eq
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
    canonical_completion_payload_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_surgery_and_extraction_derivation
          smoothabilityPackage surgeryPackages extractSphere derivation) := by
  apply Subsingleton.elim

/--
The surgery-plus-extractor target projection destructures the named payload.
-/
theorem canonical_completion_target_of_surgery_and_extraction_derivation_eq
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
    canonical_completion_target_of_surgery_and_extraction_derivation
      smoothabilityPackage surgeryPackages extractSphere derivation =
      (by
        rcases canonical_completion_payload_of_surgery_and_extraction_derivation
            smoothabilityPackage surgeryPackages extractSphere derivation with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The surgery-plus-extractor criterion projection destructures the named payload.
-/
theorem canonical_completion_criterion_of_surgery_and_extraction_derivation_eq
    (witness : Type u)
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
    canonical_completion_criterion_of_surgery_and_extraction_derivation
      witness smoothabilityPackage surgeryPackages extractSphere derivation =
      (by
        rcases canonical_completion_payload_of_surgery_and_extraction_derivation
            smoothabilityPackage surgeryPackages extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The package-level certified extraction canonical payload is obtained through the
shared project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation
      smoothabilityPackage surgeryPackages topologyPackage =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
          smoothabilityPackage surgeryPackages topologyPackage) := by
  apply Subsingleton.elim

/--
The package-level certified extraction target projection destructures the named
payload.
-/
theorem canonical_completion_target_of_surgery_and_topology_package_extraction_derivation_eq
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_completion_target_of_surgery_and_topology_package_extraction_derivation
      smoothabilityPackage surgeryPackages topologyPackage =
      (by
        rcases
            canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation
            smoothabilityPackage surgeryPackages topologyPackage with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The package-level certified extraction criterion projection destructures the
named payload.
-/
theorem canonical_completion_criterion_of_surgery_and_topology_package_extraction_derivation_eq
    (witness : Type u)
    (smoothabilityPackage : SmoothabilityPackage.{u})
    (surgeryPackages :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_completion_criterion_of_surgery_and_topology_package_extraction_derivation
      witness smoothabilityPackage surgeryPackages topologyPackage =
      (by
        rcases
            canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation
            smoothabilityPackage surgeryPackages topologyPackage with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The three component-slot requirements also produce the project target and
explicit completion criterion payload.
-/
theorem poincare_completion_payload_of_component_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_surgery_and_topology_packages
    smoothabilityRequirement surgeryRequirement topologyRequirement

/--
The three component-slot requirements produce the canonical completion target
and explicit completion criterion payload.
-/
theorem canonical_completion_payload_of_component_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_surgery_and_topology_packages
    smoothabilityRequirement surgeryRequirement topologyRequirement

/-- The component-slot requirement route proves the canonical completion target. -/
theorem canonical_completion_target_of_component_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement with
    ⟨target, _criterion⟩
  exact target

/--
The component-slot requirement route discharges the explicit universe-indexed
completion criterion.
-/
theorem canonical_completion_criterion_of_component_requirements
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The component-slot requirement route exposes the canonical topological
3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_component_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement)

/--
The three component-slot requirements also produce the project target and
explicit completion criterion payload through the certified extraction route.
-/
theorem poincare_completion_payload_of_component_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
    smoothabilityRequirement surgeryRequirement topologyRequirement

/--
The three component-slot requirements produce the canonical completion target
and explicit completion criterion payload through the certified extraction
route.
-/
theorem canonical_completion_payload_of_component_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement)

/--
The component-slot requirement route proves the canonical completion target
through the certified extraction route.
-/
theorem canonical_completion_target_of_component_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement with
    ⟨target, _criterion⟩
  exact target

/--
The component-slot requirement route discharges the explicit universe-indexed
completion criterion through the certified extraction route.
-/
theorem canonical_completion_criterion_of_component_extraction_derivation_requirements
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The component-slot requirement route exposes the canonical topological
3-sphere statement through the certified extraction route.
-/
theorem canonical_three_sphere_statement_of_component_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement)

/--
The component-slot project payload is exactly the explicit package-route
project payload applied to the three component requirements.
-/
theorem poincare_completion_payload_of_component_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    poincare_completion_payload_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      poincare_completion_payload_of_surgery_and_topology_packages
        smoothabilityRequirement surgeryRequirement topologyRequirement := by
  apply Subsingleton.elim

/--
The component-slot canonical payload is exactly the explicit package-route
canonical payload applied to the three component requirements.
-/
theorem canonical_completion_payload_of_component_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_completion_payload_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      canonical_completion_payload_of_surgery_and_topology_packages
        smoothabilityRequirement surgeryRequirement topologyRequirement := by
  apply Subsingleton.elim

/--
The component-slot canonical target projection destructures the named component
canonical payload.
-/
theorem canonical_completion_target_of_component_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_completion_target_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_component_requirements
            smoothabilityRequirement surgeryRequirement topologyRequirement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The component-slot criterion projection destructures the named component
canonical payload.
-/
theorem canonical_completion_criterion_of_component_requirements_eq
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_completion_criterion_of_component_requirements
      witness smoothabilityRequirement surgeryRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_component_requirements
            smoothabilityRequirement surgeryRequirement topologyRequirement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/-- The component-slot canonical statement projection uses the named target. -/
theorem canonical_three_sphere_statement_of_component_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_three_sphere_statement_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_component_requirements
          smoothabilityRequirement surgeryRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The component-slot certified extraction project payload is exactly the
package-level certified extraction project payload applied to the components.
-/
theorem poincare_completion_payload_of_component_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    poincare_completion_payload_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
        smoothabilityRequirement surgeryRequirement topologyRequirement := by
  apply Subsingleton.elim

/--
The component-slot certified extraction canonical payload is obtained by passing
the named project payload through the shared project-to-canonical bridge.
-/
theorem canonical_completion_payload_of_component_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_completion_payload_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_component_extraction_derivation_requirements
          smoothabilityRequirement surgeryRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The component-slot certified extraction canonical target projection destructures
the named certified component payload.
-/
theorem canonical_completion_target_of_component_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_completion_target_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_component_extraction_derivation_requirements
            smoothabilityRequirement surgeryRequirement topologyRequirement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The component-slot certified extraction criterion projection destructures the
named certified component payload.
-/
theorem canonical_completion_criterion_of_component_extraction_derivation_requirements_eq
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_completion_criterion_of_component_extraction_derivation_requirements
      witness smoothabilityRequirement surgeryRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_component_extraction_derivation_requirements
            smoothabilityRequirement surgeryRequirement topologyRequirement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The component-slot certified extraction canonical statement projection uses the
named certified component target.
-/
theorem canonical_three_sphere_statement_of_component_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    canonical_three_sphere_statement_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_component_extraction_derivation_requirements
          smoothabilityRequirement surgeryRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The five package-layer requirements also produce the project target and
explicit completion criterion payload. The final assembly only consumes the
smoothability, finite-extinction, and topology layers directly; the analytic
and construction/Perelman layers are recorded separately by the crosswalk.
-/
theorem poincare_completion_payload_of_package_layer_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (_analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (_surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_surgery_and_topology_packages
    smoothabilityRequirement finiteExtinctionRequirement topologyRequirement

/--
The five package-layer requirements produce the canonical completion target and
explicit completion criterion payload.
-/
theorem canonical_completion_payload_of_package_layer_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement)

/-- The package-layer requirement route proves the canonical completion target. -/
theorem canonical_completion_target_of_package_layer_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement with
    ⟨target, _criterion⟩
  exact target

/--
The package-layer requirement route discharges the explicit universe-indexed
completion criterion.
-/
theorem canonical_completion_criterion_of_package_layer_requirements
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The package-layer requirement route exposes the canonical topological
3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_package_layer_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement)

/--
The five package-layer requirements also produce the project target and
explicit completion criterion payload through the certified extraction route.
The final assembly still consumes the smoothability, finite-extinction, and
topology layers directly.
-/
theorem poincare_completion_payload_of_package_layer_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (_analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (_surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
    smoothabilityRequirement finiteExtinctionRequirement topologyRequirement

/--
The five package-layer requirements produce the canonical completion target and
explicit completion criterion payload through the certified extraction route.
-/
theorem canonical_completion_payload_of_package_layer_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement)

/--
The package-layer requirement route proves the canonical completion target
through the certified extraction route.
-/
theorem canonical_completion_target_of_package_layer_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement with
    ⟨target, _criterion⟩
  exact target

/--
The package-layer requirement route discharges the explicit universe-indexed
completion criterion through the certified extraction route.
-/
theorem canonical_completion_criterion_of_package_layer_extraction_derivation_requirements
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The package-layer requirement route exposes the canonical topological
3-sphere statement through the certified extraction route.
-/
theorem canonical_three_sphere_statement_of_package_layer_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement)

/--
The package-layer project payload is exactly the explicit package-route project
payload applied to the consumed smoothability, finite-extinction, and topology
layers.
-/
theorem poincare_completion_payload_of_package_layer_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    poincare_completion_payload_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      poincare_completion_payload_of_surgery_and_topology_packages
        smoothabilityRequirement finiteExtinctionRequirement topologyRequirement := by
  apply Subsingleton.elim

/--
The package-layer canonical payload is obtained through the shared
project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_package_layer_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_completion_payload_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_package_layer_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The package-layer canonical target projection destructures the named package
layer payload.
-/
theorem canonical_completion_target_of_package_layer_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_completion_target_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_package_layer_requirements
            smoothabilityRequirement analyticRequirement surgeryRequirement
            finiteExtinctionRequirement topologyRequirement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The package-layer criterion projection destructures the named package layer
payload.
-/
theorem canonical_completion_criterion_of_package_layer_requirements_eq
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_completion_criterion_of_package_layer_requirements
      witness smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_package_layer_requirements
            smoothabilityRequirement analyticRequirement surgeryRequirement
            finiteExtinctionRequirement topologyRequirement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/-- The package-layer canonical statement projection uses the named target. -/
theorem canonical_three_sphere_statement_of_package_layer_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_three_sphere_statement_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_package_layer_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The package-layer certified extraction project payload is exactly the
package-level certified extraction project payload applied to the consumed
smoothability, finite-extinction, and topology layers.
-/
theorem poincare_completion_payload_of_package_layer_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    poincare_completion_payload_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation
        smoothabilityRequirement finiteExtinctionRequirement topologyRequirement := by
  apply Subsingleton.elim

/--
The package-layer certified extraction canonical payload is obtained through the
shared project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_package_layer_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_completion_payload_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_package_layer_extraction_derivation_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The package-layer certified extraction target projection destructures the named
certified package-layer payload.
-/
theorem canonical_completion_target_of_package_layer_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_completion_target_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_package_layer_extraction_derivation_requirements
            smoothabilityRequirement analyticRequirement surgeryRequirement
            finiteExtinctionRequirement topologyRequirement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The package-layer certified extraction criterion projection destructures the
named certified package-layer payload.
-/
theorem canonical_completion_criterion_of_package_layer_extraction_derivation_requirements_eq
    (witness : Type u)
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_completion_criterion_of_package_layer_extraction_derivation_requirements
      witness smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      (by
        rcases canonical_completion_payload_of_package_layer_extraction_derivation_requirements
            smoothabilityRequirement analyticRequirement surgeryRequirement
            finiteExtinctionRequirement topologyRequirement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The package-layer certified extraction canonical statement projection uses the
named certified package-layer target.
-/
theorem canonical_three_sphere_statement_of_package_layer_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    canonical_three_sphere_statement_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_package_layer_extraction_derivation_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The six milestone requirements also produce the project target and explicit
completion criterion payload.
-/
theorem poincare_completion_payload_of_milestone_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (_ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_component_requirements
    smoothabilityBridgeRequirement
    _finiteExtinctionRequirement
    extinctionToSphereHomeomorphismRequirement

/--
The six milestone requirements produce the canonical completion target and
explicit completion criterion payload.
-/
theorem canonical_completion_payload_of_milestone_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_milestone_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement
      _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement)

/-- The milestone-requirement route proves the canonical completion target. -/
theorem canonical_completion_target_of_milestone_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_milestone_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement
      _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement with
    ⟨target, _criterion⟩
  exact target

/--
The milestone-requirement route discharges the explicit universe-indexed
completion criterion.
-/
theorem canonical_completion_criterion_of_milestone_requirements
    (witness : Type u)
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_milestone_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement
      _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The milestone-requirement route exposes the canonical topological 3-sphere
statement.
-/
theorem canonical_three_sphere_statement_of_milestone_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_milestone_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement)

/--
The six milestone requirements also produce the project target and explicit
completion criterion payload through the certified extraction route.
-/
theorem poincare_completion_payload_of_milestone_extraction_derivation_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (_ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_component_extraction_derivation_requirements
    smoothabilityBridgeRequirement
    _finiteExtinctionRequirement
    extinctionToSphereHomeomorphismRequirement

/--
The six milestone requirements produce the canonical completion target and
explicit completion criterion payload through the certified extraction route.
-/
theorem canonical_completion_payload_of_milestone_extraction_derivation_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement
      _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement)

/--
The milestone-requirement route proves the canonical completion target through
the certified extraction route.
-/
theorem canonical_completion_target_of_milestone_extraction_derivation_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement
      _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement with
    ⟨target, _criterion⟩
  exact target

/--
The milestone-requirement route discharges the explicit universe-indexed
completion criterion through the certified extraction route.
-/
theorem canonical_completion_criterion_of_milestone_extraction_derivation_requirements
    (witness : Type u)
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement
      _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The milestone-requirement route exposes the canonical topological 3-sphere
statement through the certified extraction route.
-/
theorem canonical_three_sphere_statement_of_milestone_extraction_derivation_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (_ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (_perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (_finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      _ricciFlowWithSurgeryRequirement _perelmanSingularityControlRequirement
      _finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement)

/--
The milestone project payload is exactly the component-slot project payload
applied to the consumed smoothability, finite-extinction, and
extinction-to-sphere milestones.
-/
theorem poincare_completion_payload_of_milestone_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    poincare_completion_payload_of_milestone_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      poincare_completion_payload_of_component_requirements
        smoothabilityBridgeRequirement finiteExtinctionRequirement
        extinctionToSphereHomeomorphismRequirement := by
  apply Subsingleton.elim

/--
The milestone canonical payload is obtained through the shared
project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_milestone_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_completion_payload_of_milestone_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_milestone_requirements
          smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
          finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The milestone canonical target projection destructures the named milestone
payload.
-/
theorem canonical_completion_target_of_milestone_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_completion_target_of_milestone_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      (by
        rcases canonical_completion_payload_of_milestone_requirements
            smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
            ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
            finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/-- The milestone criterion projection destructures the named milestone payload. -/
theorem canonical_completion_criterion_of_milestone_requirements_eq
    (witness : Type u)
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_completion_criterion_of_milestone_requirements
      witness smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      (by
        rcases canonical_completion_payload_of_milestone_requirements
            smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
            ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
            finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/-- The milestone canonical statement projection uses the named milestone target. -/
theorem canonical_three_sphere_statement_of_milestone_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_three_sphere_statement_of_milestone_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_milestone_requirements
          smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
          finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The milestone certified extraction project payload is exactly the certified
component-slot project payload applied to the consumed milestones.
-/
theorem poincare_completion_payload_of_milestone_extraction_derivation_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    poincare_completion_payload_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      poincare_completion_payload_of_component_extraction_derivation_requirements
        smoothabilityBridgeRequirement finiteExtinctionRequirement
        extinctionToSphereHomeomorphismRequirement := by
  apply Subsingleton.elim

/--
The milestone certified extraction canonical payload is obtained through the
shared project-to-canonical completion payload bridge.
-/
theorem canonical_completion_payload_of_milestone_extraction_derivation_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_completion_payload_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_milestone_extraction_derivation_requirements
          smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
          finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The milestone certified extraction target projection destructures the named
certified milestone payload.
-/
theorem canonical_completion_target_of_milestone_extraction_derivation_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_completion_target_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      (by
        rcases canonical_completion_payload_of_milestone_extraction_derivation_requirements
            smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
            ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
            finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The milestone certified extraction criterion projection destructures the named
certified milestone payload.
-/
theorem canonical_completion_criterion_of_milestone_extraction_derivation_requirements_eq
    (witness : Type u)
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_completion_criterion_of_milestone_extraction_derivation_requirements
      witness smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      (by
        rcases canonical_completion_payload_of_milestone_extraction_derivation_requirements
            smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
            ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
            finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The milestone certified extraction canonical statement projection uses the named
certified milestone target.
-/
theorem canonical_three_sphere_statement_of_milestone_extraction_derivation_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    canonical_three_sphere_statement_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_milestone_extraction_derivation_requirements
          smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
          finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/-- The aggregate dependency proposition currently needed to prove the target. -/
abbrev RemainingDependencyPackage : Prop :=
  PoincareProofDependencies.{u}

/-- The remaining dependency package is exactly the aggregate proof dependency package. -/
theorem remainingDependencyPackage_eq :
    RemainingDependencyPackage.{u} = PoincareProofDependencies.{u} :=
  rfl

/--
The remaining dependency package is logically equivalent to the aggregate proof
dependency package.
-/
theorem remainingDependencyPackage_iff_poincareProofDependencies :
    RemainingDependencyPackage.{u} ↔ PoincareProofDependencies.{u} :=
  Iff.rfl

/-- The remaining dependency package supplies the smoothability package. -/
theorem smoothability_package_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    SmoothabilityPackage.{u} :=
  dependencies.smoothability

/--
The remaining dependency package supplies the theorem-shaped `C∞`
smooth-manifold statement consumed by the canonical smooth Poincare statement.
-/
theorem smoothability_smooth_manifold_statement_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    SmoothabilitySmoothManifoldStatement.{u} :=
  smoothability_smooth_manifold_statement_of_dependencies dependencies

/--
The remaining dependency package supplies the `C∞` manifold evidence consumed by
the canonical smooth Poincare statement.
-/
theorem smooth_manifold_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        IsManifold (𝓡 3) ∞ M :=
  smoothability_smooth_manifold_statement_of_remaining_dependency_package
    dependencies

/--
The remaining dependency package exposes both smoothability theorem outputs:
the C¹ surgery-model bridge and the separate `C∞` canonical smooth-manifold
statement.
-/
theorem smoothability_smooth_manifold_payload_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    SmoothabilityBridgeStatement.{u} ∧
      SmoothabilitySmoothManifoldStatement.{u} :=
  smoothability_smooth_manifold_payload_of_dependencies dependencies

/-- The remaining-dependency smoothability package projection is the stored field. -/
theorem smoothability_package_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    smoothability_package_of_remaining_dependency_package dependencies =
      dependencies.smoothability :=
  rfl

/--
The remaining-dependency `C∞` smooth-manifold statement projection is the stored
smoothability field.
-/
theorem smoothability_smooth_manifold_statement_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    smoothability_smooth_manifold_statement_of_remaining_dependency_package
      dependencies =
      dependencies.smoothability.smoothManifold :=
  rfl

/--
The remaining-dependency canonical smooth-manifold projection is the stored
smoothability field.
-/
theorem smooth_manifold_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    smooth_manifold_of_remaining_dependency_package dependencies =
      dependencies.smoothability.smoothManifold := by
  apply Subsingleton.elim

/--
The remaining-dependency smoothability payload is the pair of stored
smoothability bridge and `C∞` smooth-manifold fields.
-/
theorem smoothability_smooth_manifold_payload_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    smoothability_smooth_manifold_payload_of_remaining_dependency_package
      dependencies =
      ⟨dependencies.smoothability.bridge,
        dependencies.smoothability.smoothManifold⟩ := by
  apply Subsingleton.elim

/-- The remaining dependency package supplies the target-family surgery package. -/
theorem surgery_packages_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) :=
  dependencies.surgery

/-- The remaining dependency package supplies the topology extraction package. -/
theorem topology_package_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    ExtinctionTopologyExtractionPackage.{u} :=
  dependencies.topology

/-- The remaining-dependency surgery-package-family projection is the stored field. -/
theorem surgery_packages_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    surgery_packages_of_remaining_dependency_package dependencies =
      dependencies.surgery :=
  rfl

/-- The remaining-dependency topology extraction projection is the stored field. -/
theorem topology_package_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    topology_package_of_remaining_dependency_package dependencies =
      dependencies.topology :=
  rfl

/--
The remaining dependency package exposes the same three component inputs as the
aggregate proof dependency package.
-/
theorem remainingDependencyPackage_components_payload
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _smoothability : SmoothabilityPackage.{u},
    ∃ _surgery :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
      ExtinctionTopologyExtractionPackage.{u} := by
  exact poincareProofDependencies_components_payload dependencies

/--
The remaining-dependency component payload is the tuple of the three stored
dependency fields.
-/
theorem remainingDependencyPackage_components_payload_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_components_payload dependencies =
      ⟨dependencies.smoothability, dependencies.surgery,
        dependencies.topology⟩ := by
  apply Subsingleton.elim

/--
The remaining-dependency component payload is the aggregate dependency
component payload under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_components_payload_to_aggregate_payload_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_components_payload dependencies =
      poincareProofDependencies_components_payload dependencies := by
  apply Subsingleton.elim

/--
The remaining dependency package is equivalent to exactly the three component
inputs represented by the aggregate proof dependency package.
-/
theorem remainingDependencyPackage_iff_components :
    RemainingDependencyPackage.{u} ↔
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u} := by
  exact poincareProofDependencies_iff_components

/--
The remaining-dependency component equivalence is the aggregate component
equivalence under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_iff_components_eq :
    remainingDependencyPackage_iff_components.{u} =
      poincareProofDependencies_iff_components.{u} := by
  apply Subsingleton.elim

/--
The remaining dependency package exposes the same three component-slot
requirements as the dependency crosswalk.
-/
theorem remainingDependencyPackage_component_requirements_payload
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _smoothability :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent := by
  exact dependency_component_requirements_payload_of_dependencies dependencies

/--
The remaining-dependency component-slot payload is the aggregate dependency
component-slot payload under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_component_requirements_payload_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_component_requirements_payload dependencies =
      dependency_component_requirements_payload_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency component-slot payload is the tuple of the stored
remaining-dependency fields under the crosswalk component aliases.
-/
theorem remainingDependencyPackage_component_requirements_payload_to_fields_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_component_requirements_payload dependencies =
      ⟨dependencies.smoothability, dependencies.surgery,
        dependencies.topology⟩ := by
  apply Subsingleton.elim

/--
The remaining-dependency component-slot payload is also the tuple of the named
component-slot projections.
-/
theorem remainingDependencyPackage_component_requirements_payload_to_named_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_component_requirements_payload dependencies =
      ⟨ smoothabilityComponent_requirement_of_dependencies dependencies
      , surgeryComponent_requirement_of_dependencies dependencies
      , topologyComponent_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The remaining dependency package is equivalent to exactly the three
component-slot requirements named by the dependency crosswalk.
-/
theorem remainingDependencyPackage_iff_component_requirements :
    RemainingDependencyPackage.{u} ↔
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent := by
  exact poincareProofDependencies_iff_component_requirements

/--
The remaining-dependency component-slot equivalence is the aggregate dependency
component-slot equivalence under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_iff_component_requirements_eq :
    remainingDependencyPackage_iff_component_requirements.{u} =
      poincareProofDependencies_iff_component_requirements.{u} := by
  apply Subsingleton.elim

/--
The remaining dependency package exposes the five package-layer requirements
named by the dependency crosswalk.
-/
theorem remainingDependencyPackage_package_layer_requirements_payload
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  exact dependency_package_layer_requirements_payload_of_dependencies dependencies

/--
The remaining-dependency package-layer payload is the aggregate dependency
package-layer payload under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_package_layer_requirements_payload_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_package_layer_requirements_payload dependencies =
      dependency_package_layer_requirements_payload_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency package-layer payload is also the tuple of generic
package-layer projections in package-layer order.
-/
theorem remainingDependencyPackage_package_layer_requirements_payload_to_generic_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_package_layer_requirements_payload dependencies =
      ⟨ dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.smoothabilityPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.analyticFoundationPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.surgeryPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.finiteExtinctionPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.topologyPackage
      ⟩ := by
  apply Subsingleton.elim

/--
The remaining dependency package is equivalent to supplying the five
package-layer requirements named by the dependency crosswalk.
-/
theorem remainingDependencyPackage_iff_package_layer_requirements :
    RemainingDependencyPackage.{u} ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  exact poincareProofDependencies_iff_package_layer_requirements

/--
The remaining-dependency package-layer equivalence is the aggregate dependency
package-layer equivalence under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_iff_package_layer_requirements_eq :
    remainingDependencyPackage_iff_package_layer_requirements.{u} =
      poincareProofDependencies_iff_package_layer_requirements.{u} := by
  apply Subsingleton.elim

/--
The remaining dependency package exposes the six milestone requirements named
by the dependency crosswalk.
-/
theorem remainingDependencyPackage_milestone_requirements_payload
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _smoothabilityBridge :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
    ∃ _ricciFlowAnalyticFoundation :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation,
    ∃ _ricciFlowWithSurgery :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
    ∃ _perelmanSingularityControl :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl,
    ∃ _finiteExtinction :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism := by
  exact dependency_milestone_requirements_payload_of_dependencies dependencies

/--
The remaining-dependency milestone payload is the aggregate dependency milestone
payload under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_milestone_requirements_payload_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_milestone_requirements_payload dependencies =
      dependency_milestone_requirements_payload_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone payload is also the tuple of package-layer
projections assigned to the six ledger milestones.
-/
theorem remainingDependencyPackage_milestone_requirements_payload_to_package_layer_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remainingDependencyPackage_milestone_requirements_payload dependencies =
      ⟨ smoothabilityPackage_requirement_of_dependencies dependencies
      , analyticFoundationPackage_requirement_of_dependencies dependencies
      , surgeryPackage_requirement_of_dependencies dependencies
      , surgeryPackage_requirement_of_dependencies dependencies
      , finiteExtinctionPackage_requirement_of_dependencies dependencies
      , topologyPackage_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The remaining dependency package is equivalent to supplying all six milestone
requirements named by the dependency crosswalk.
-/
theorem remainingDependencyPackage_iff_milestone_requirements :
    RemainingDependencyPackage.{u} ↔
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism := by
  exact poincareProofDependencies_iff_milestone_requirements

/--
The remaining-dependency milestone equivalence is the aggregate dependency
milestone equivalence under the remaining-dependency abbreviation.
-/
theorem remainingDependencyPackage_iff_milestone_requirements_eq :
    remainingDependencyPackage_iff_milestone_requirements.{u} =
      poincareProofDependencies_iff_milestone_requirements.{u} := by
  apply Subsingleton.elim

/--
The remaining dependency package produces the canonical completion payload
through the crosswalk component-slot requirement route.
-/
theorem canonical_completion_payload_of_remaining_dependency_component_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases remainingDependencyPackage_component_requirements_payload dependencies with
    ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩
  exact canonical_completion_payload_of_component_requirements
    smoothabilityRequirement surgeryRequirement topologyRequirement

/--
The remaining dependency package proves the canonical completion target through
the crosswalk component-slot requirement route.
-/
theorem canonical_completion_target_of_remaining_dependency_component_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_remaining_dependency_component_requirements
      dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The remaining dependency package discharges the universe-indexed completion
criterion through the crosswalk component-slot requirement route.
-/
theorem canonical_completion_criterion_of_remaining_dependency_component_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_remaining_dependency_component_requirements
      dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The remaining dependency package exposes the canonical topological statement
through the crosswalk component-slot requirement route.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_component_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_remaining_dependency_component_requirements
      dependencies)

/--
The remaining dependency package produces the canonical completion payload
through the crosswalk component-slot requirement route with certified topology
extraction.
-/
theorem canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases remainingDependencyPackage_component_requirements_payload dependencies with
    ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩
  exact canonical_completion_payload_of_component_extraction_derivation_requirements
    smoothabilityRequirement surgeryRequirement topologyRequirement

/--
The remaining dependency package proves the canonical completion target through
the crosswalk component-slot requirement route with certified topology
extraction.
-/
theorem canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases
      canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The remaining dependency package discharges the universe-indexed completion
criterion through the crosswalk component-slot requirement route with certified
topology extraction.
-/
theorem canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The remaining dependency package exposes the canonical topological statement
through the crosswalk component-slot requirement route with certified topology
extraction.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_component_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies)

/--
The remaining-dependency component canonical payload destructures the named
component-requirements payload and applies the component-slot route.
-/
theorem canonical_completion_payload_of_remaining_dependency_component_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_remaining_dependency_component_requirements
      dependencies =
      (by
        rcases remainingDependencyPackage_component_requirements_payload
            dependencies with
          ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩
        exact canonical_completion_payload_of_component_requirements
          smoothabilityRequirement surgeryRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The remaining-dependency component target projection destructures the named
remaining-dependency component payload.
-/
theorem canonical_completion_target_of_remaining_dependency_component_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_remaining_dependency_component_requirements
      dependencies =
      (by
        rcases canonical_completion_payload_of_remaining_dependency_component_requirements
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The remaining-dependency component criterion projection destructures the named
remaining-dependency component payload.
-/
theorem canonical_completion_criterion_of_remaining_dependency_component_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_remaining_dependency_component_requirements
      witness dependencies =
      (by
        rcases canonical_completion_payload_of_remaining_dependency_component_requirements
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The remaining-dependency component canonical statement projection uses the named
remaining-dependency component target.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_component_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_three_sphere_statement_of_remaining_dependency_component_requirements
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_remaining_dependency_component_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component canonical payload destructures the
named component-requirements payload and applies the certified component route.
-/
theorem canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies =
      (by
        rcases remainingDependencyPackage_component_requirements_payload
            dependencies with
          ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩
        exact canonical_completion_payload_of_component_extraction_derivation_requirements
          smoothabilityRequirement surgeryRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component target projection destructures the
named certified remaining-dependency component payload.
-/
theorem canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies =
      (by
        rcases
            canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component criterion projection destructures
the named certified remaining-dependency component payload.
-/
theorem canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
      witness dependencies =
      (by
        rcases
            canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component canonical statement projection uses
the named certified remaining-dependency component target.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_three_sphere_statement_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining dependency package produces the canonical completion payload
through the crosswalk package-layer requirement route.
-/
theorem canonical_completion_payload_of_remaining_dependency_package_layer_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases remainingDependencyPackage_package_layer_requirements_payload dependencies with
    ⟨ smoothabilityRequirement
    , analyticRequirement
    , surgeryRequirement
    , finiteExtinctionRequirement
    , topologyRequirement
    ⟩
  exact canonical_completion_payload_of_package_layer_requirements
    smoothabilityRequirement analyticRequirement surgeryRequirement
    finiteExtinctionRequirement topologyRequirement

/--
The remaining dependency package proves the canonical completion target through
the crosswalk package-layer requirement route.
-/
theorem canonical_completion_target_of_remaining_dependency_package_layer_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_remaining_dependency_package_layer_requirements
      dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The remaining dependency package discharges the universe-indexed completion
criterion through the crosswalk package-layer requirement route.
-/
theorem canonical_completion_criterion_of_remaining_dependency_package_layer_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_remaining_dependency_package_layer_requirements
      dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The remaining dependency package exposes the canonical topological statement
through the crosswalk package-layer requirement route.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_package_layer_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_remaining_dependency_package_layer_requirements
      dependencies)

/--
The remaining dependency package produces the canonical completion payload
through the crosswalk package-layer requirement route with certified topology
extraction.
-/
theorem canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases remainingDependencyPackage_package_layer_requirements_payload dependencies with
    ⟨ smoothabilityRequirement
    , analyticRequirement
    , surgeryRequirement
    , finiteExtinctionRequirement
    , topologyRequirement
    ⟩
  exact canonical_completion_payload_of_package_layer_extraction_derivation_requirements
    smoothabilityRequirement analyticRequirement surgeryRequirement
    finiteExtinctionRequirement topologyRequirement

/--
The remaining dependency package proves the canonical completion target through
the crosswalk package-layer requirement route with certified topology
extraction.
-/
theorem canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases
      canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The remaining dependency package discharges the universe-indexed completion
criterion through the crosswalk package-layer requirement route with certified
topology extraction.
-/
theorem canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The remaining dependency package exposes the canonical topological statement
through the crosswalk package-layer requirement route with certified topology
extraction.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies)

/--
The remaining dependency package produces the canonical completion payload
through the crosswalk milestone-requirement route.
-/
theorem canonical_completion_payload_of_remaining_dependency_milestone_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases remainingDependencyPackage_milestone_requirements_payload dependencies with
    ⟨ smoothabilityBridgeRequirement
    , ricciFlowAnalyticFoundationRequirement
    , ricciFlowWithSurgeryRequirement
    , perelmanSingularityControlRequirement
    , finiteExtinctionRequirement
    , extinctionToSphereHomeomorphismRequirement
    ⟩
  exact canonical_completion_payload_of_milestone_requirements
    smoothabilityBridgeRequirement
    ricciFlowAnalyticFoundationRequirement
    ricciFlowWithSurgeryRequirement
    perelmanSingularityControlRequirement
    finiteExtinctionRequirement
    extinctionToSphereHomeomorphismRequirement

/--
The remaining dependency package proves the canonical completion target through
the crosswalk milestone-requirement route.
-/
theorem canonical_completion_target_of_remaining_dependency_milestone_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_remaining_dependency_milestone_requirements
      dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The remaining dependency package discharges the universe-indexed completion
criterion through the crosswalk milestone-requirement route.
-/
theorem canonical_completion_criterion_of_remaining_dependency_milestone_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_remaining_dependency_milestone_requirements
      dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The remaining dependency package exposes the canonical topological statement
through the crosswalk milestone-requirement route.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_milestone_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_remaining_dependency_milestone_requirements
      dependencies)

/--
The remaining dependency package produces the canonical completion payload
through the crosswalk milestone-requirement route with certified topology
extraction.
-/
theorem canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases remainingDependencyPackage_milestone_requirements_payload dependencies with
    ⟨ smoothabilityBridgeRequirement
    , ricciFlowAnalyticFoundationRequirement
    , ricciFlowWithSurgeryRequirement
    , perelmanSingularityControlRequirement
    , finiteExtinctionRequirement
    , extinctionToSphereHomeomorphismRequirement
    ⟩
  exact canonical_completion_payload_of_milestone_extraction_derivation_requirements
    smoothabilityBridgeRequirement
    ricciFlowAnalyticFoundationRequirement
    ricciFlowWithSurgeryRequirement
    perelmanSingularityControlRequirement
    finiteExtinctionRequirement
    extinctionToSphereHomeomorphismRequirement

/--
The remaining dependency package proves the canonical completion target through
the crosswalk milestone-requirement route with certified topology extraction.
-/
theorem canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases
      canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The remaining dependency package discharges the universe-indexed completion
criterion through the crosswalk milestone-requirement route with certified
topology extraction.
-/
theorem canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The remaining dependency package exposes the canonical topological statement
through the crosswalk milestone-requirement route with certified topology
extraction.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_milestone_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies)

/--
The remaining-dependency package-layer canonical payload destructures the named
package-layer requirements payload and applies the package-layer route.
-/
theorem canonical_completion_payload_of_remaining_dependency_package_layer_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_remaining_dependency_package_layer_requirements
      dependencies =
      (by
        rcases remainingDependencyPackage_package_layer_requirements_payload
            dependencies with
          ⟨ smoothabilityRequirement
          , analyticRequirement
          , surgeryRequirement
          , finiteExtinctionRequirement
          , topologyRequirement
          ⟩
        exact canonical_completion_payload_of_package_layer_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The remaining-dependency package-layer target projection destructures the named
remaining-dependency package-layer payload.
-/
theorem canonical_completion_target_of_remaining_dependency_package_layer_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_remaining_dependency_package_layer_requirements
      dependencies =
      (by
        rcases canonical_completion_payload_of_remaining_dependency_package_layer_requirements
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The remaining-dependency package-layer criterion projection destructures the
named remaining-dependency package-layer payload.
-/
theorem canonical_completion_criterion_of_remaining_dependency_package_layer_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_remaining_dependency_package_layer_requirements
      witness dependencies =
      (by
        rcases canonical_completion_payload_of_remaining_dependency_package_layer_requirements
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The remaining-dependency package-layer canonical statement projection uses the
named remaining-dependency package-layer target.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_package_layer_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_three_sphere_statement_of_remaining_dependency_package_layer_requirements
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_remaining_dependency_package_layer_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer canonical payload destructures
the named package-layer requirements payload and applies the certified route.
-/
theorem canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies =
      (by
        rcases remainingDependencyPackage_package_layer_requirements_payload
            dependencies with
          ⟨ smoothabilityRequirement
          , analyticRequirement
          , surgeryRequirement
          , finiteExtinctionRequirement
          , topologyRequirement
          ⟩
        exact canonical_completion_payload_of_package_layer_extraction_derivation_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer target projection destructures
the named certified remaining-dependency package-layer payload.
-/
theorem canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies =
      (by
        rcases
            canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer criterion projection
destructures the named certified remaining-dependency package-layer payload.
-/
theorem canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
      witness dependencies =
      (by
        rcases
            canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer canonical statement projection
uses the named certified remaining-dependency package-layer target.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_three_sphere_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone canonical payload destructures the named
milestone requirements payload and applies the milestone route.
-/
theorem canonical_completion_payload_of_remaining_dependency_milestone_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_remaining_dependency_milestone_requirements
      dependencies =
      (by
        rcases remainingDependencyPackage_milestone_requirements_payload
            dependencies with
          ⟨ smoothabilityBridgeRequirement
          , ricciFlowAnalyticFoundationRequirement
          , ricciFlowWithSurgeryRequirement
          , perelmanSingularityControlRequirement
          , finiteExtinctionRequirement
          , extinctionToSphereHomeomorphismRequirement
          ⟩
        exact canonical_completion_payload_of_milestone_requirements
          smoothabilityBridgeRequirement
          ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement
          perelmanSingularityControlRequirement
          finiteExtinctionRequirement
          extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone target projection destructures the named
remaining-dependency milestone payload.
-/
theorem canonical_completion_target_of_remaining_dependency_milestone_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_remaining_dependency_milestone_requirements
      dependencies =
      (by
        rcases canonical_completion_payload_of_remaining_dependency_milestone_requirements
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone criterion projection destructures the named
remaining-dependency milestone payload.
-/
theorem canonical_completion_criterion_of_remaining_dependency_milestone_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_remaining_dependency_milestone_requirements
      witness dependencies =
      (by
        rcases canonical_completion_payload_of_remaining_dependency_milestone_requirements
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone canonical statement projection uses the named
remaining-dependency milestone target.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_milestone_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_three_sphere_statement_of_remaining_dependency_milestone_requirements
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_remaining_dependency_milestone_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone canonical payload destructures the
named milestone requirements payload and applies the certified milestone route.
-/
theorem canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies =
      (by
        rcases remainingDependencyPackage_milestone_requirements_payload
            dependencies with
          ⟨ smoothabilityBridgeRequirement
          , ricciFlowAnalyticFoundationRequirement
          , ricciFlowWithSurgeryRequirement
          , perelmanSingularityControlRequirement
          , finiteExtinctionRequirement
          , extinctionToSphereHomeomorphismRequirement
          ⟩
        exact canonical_completion_payload_of_milestone_extraction_derivation_requirements
          smoothabilityBridgeRequirement
          ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement
          perelmanSingularityControlRequirement
          finiteExtinctionRequirement
          extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone target projection destructures the
named certified remaining-dependency milestone payload.
-/
theorem canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies =
      (by
        rcases
            canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone criterion projection destructures
the named certified remaining-dependency milestone payload.
-/
theorem canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
      witness dependencies =
      (by
        rcases
            canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone canonical statement projection
uses the named certified remaining-dependency milestone target.
-/
theorem canonical_three_sphere_statement_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_three_sphere_statement_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining dependency package exposes the project completion payload through
the crosswalk component-slot requirement route.
-/
theorem poincare_completion_payload_of_remaining_dependency_component_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_remaining_dependency_component_requirements
      dependencies)

/--
The remaining dependency package proves the project target through the
crosswalk component-slot requirement route.
-/
theorem poincare_statement_of_remaining_dependency_component_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_remaining_dependency_component_requirements
    dependencies

/--
The remaining dependency package discharges the project criterion through the
crosswalk component-slot requirement route.
-/
theorem completion_criterion_of_remaining_dependency_component_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_component_requirements
    witness dependencies

/--
The remaining dependency package exposes the project completion payload through
the certified component-slot topology-extraction route.
-/
theorem poincare_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies)

/--
The remaining dependency package proves the project target through the
certified component-slot topology-extraction route.
-/
theorem poincare_statement_of_remaining_dependency_component_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
    dependencies

/--
The remaining dependency package discharges the project criterion through the
certified component-slot topology-extraction route.
-/
theorem completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
    witness dependencies

/--
The remaining dependency package exposes the project completion payload through
the crosswalk package-layer requirement route.
-/
theorem poincare_completion_payload_of_remaining_dependency_package_layer_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_remaining_dependency_package_layer_requirements
      dependencies)

/--
The remaining dependency package proves the project target through the
crosswalk package-layer requirement route.
-/
theorem poincare_statement_of_remaining_dependency_package_layer_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_remaining_dependency_package_layer_requirements
    dependencies

/--
The remaining dependency package discharges the project criterion through the
crosswalk package-layer requirement route.
-/
theorem completion_criterion_of_remaining_dependency_package_layer_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_package_layer_requirements
    witness dependencies

/--
The remaining dependency package exposes the project completion payload through
the certified package-layer topology-extraction route.
-/
theorem poincare_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies)

/--
The remaining dependency package proves the project target through the
certified package-layer topology-extraction route.
-/
theorem poincare_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
    dependencies

/--
The remaining dependency package discharges the project criterion through the
certified package-layer topology-extraction route.
-/
theorem completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
    witness dependencies

/--
The remaining dependency package exposes the project completion payload through
the crosswalk milestone-requirement route.
-/
theorem poincare_completion_payload_of_remaining_dependency_milestone_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_remaining_dependency_milestone_requirements
      dependencies)

/--
The remaining dependency package proves the project target through the
crosswalk milestone-requirement route.
-/
theorem poincare_statement_of_remaining_dependency_milestone_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_remaining_dependency_milestone_requirements
    dependencies

/--
The remaining dependency package discharges the project criterion through the
crosswalk milestone-requirement route.
-/
theorem completion_criterion_of_remaining_dependency_milestone_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_milestone_requirements
    witness dependencies

/--
The remaining dependency package exposes the project completion payload through
the certified milestone topology-extraction route.
-/
theorem poincare_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies)

/--
The remaining dependency package proves the project target through the
certified milestone topology-extraction route.
-/
theorem poincare_statement_of_remaining_dependency_milestone_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
    dependencies

/--
The remaining dependency package discharges the project criterion through the
certified milestone topology-extraction route.
-/
theorem completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
    witness dependencies

/--
The remaining-dependency component project payload is the project payload
induced by the remaining-dependency component canonical payload.
-/
theorem poincare_completion_payload_of_remaining_dependency_component_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_completion_payload_of_remaining_dependency_component_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_remaining_dependency_component_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency component project statement is the target projected
from the remaining-dependency component canonical payload route.
-/
theorem poincare_statement_of_remaining_dependency_component_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_statement_of_remaining_dependency_component_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_component_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency component project criterion is the criterion projected
from the remaining-dependency component canonical payload route.
-/
theorem completion_criterion_of_remaining_dependency_component_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    completion_criterion_of_remaining_dependency_component_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_component_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component project payload is the project
payload induced by the certified component canonical payload.
-/
theorem poincare_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component project statement is the target
projected from the certified component canonical payload route.
-/
theorem poincare_statement_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_statement_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component project criterion is the criterion
projected from the certified component canonical payload route.
-/
theorem completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency package-layer project payload is the project payload
induced by the package-layer canonical payload.
-/
theorem poincare_completion_payload_of_remaining_dependency_package_layer_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_completion_payload_of_remaining_dependency_package_layer_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_remaining_dependency_package_layer_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency package-layer project statement is the target
projected from the package-layer canonical payload route.
-/
theorem poincare_statement_of_remaining_dependency_package_layer_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_statement_of_remaining_dependency_package_layer_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_package_layer_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency package-layer project criterion is the criterion
projected from the package-layer canonical payload route.
-/
theorem completion_criterion_of_remaining_dependency_package_layer_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    completion_criterion_of_remaining_dependency_package_layer_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_package_layer_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer project payload is the project
payload induced by the certified package-layer canonical payload.
-/
theorem poincare_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer project statement is the
target projected from the certified package-layer canonical payload route.
-/
theorem poincare_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer project criterion is the
criterion projected from the certified package-layer canonical payload route.
-/
theorem completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone project payload is the project payload
induced by the milestone canonical payload.
-/
theorem poincare_completion_payload_of_remaining_dependency_milestone_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_completion_payload_of_remaining_dependency_milestone_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_remaining_dependency_milestone_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone project statement is the target projected
from the milestone canonical payload route.
-/
theorem poincare_statement_of_remaining_dependency_milestone_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_statement_of_remaining_dependency_milestone_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_milestone_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency milestone project criterion is the criterion projected
from the milestone canonical payload route.
-/
theorem completion_criterion_of_remaining_dependency_milestone_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    completion_criterion_of_remaining_dependency_milestone_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_milestone_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone project payload is the project
payload induced by the certified milestone canonical payload.
-/
theorem poincare_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone project statement is the target
projected from the certified milestone canonical payload route.
-/
theorem poincare_statement_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_statement_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone project criterion is the criterion
projected from the certified milestone canonical payload route.
-/
theorem completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The aggregate proof dependency package exposes the canonical topological
statement through the crosswalk component-slot requirement route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_component_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_remaining_dependency_component_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical topological
statement through the crosswalk component-slot requirement route with certified
topology extraction.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_component_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_remaining_dependency_component_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical topological
statement through the crosswalk package-layer requirement route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_remaining_dependency_package_layer_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical topological
statement through the crosswalk package-layer requirement route with certified
topology extraction.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical topological
statement through the crosswalk milestone-requirement route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_milestone_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_remaining_dependency_milestone_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical topological
statement through the crosswalk milestone-requirement route with certified
topology extraction.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_remaining_dependency_milestone_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical completion payload
through the crosswalk component-slot requirement route.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_component_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_remaining_dependency_component_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package proves the canonical completion target
through the crosswalk component-slot requirement route.
-/
theorem canonical_completion_target_of_poincareProofDependencies_component_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_remaining_dependency_component_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package discharges the universe-indexed
completion criterion through the crosswalk component-slot requirement route.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_component_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_component_requirements
    witness
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical completion payload
through the certified component-slot topology-extraction route.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package proves the canonical completion target
through the certified component-slot topology-extraction route.
-/
theorem canonical_completion_target_of_poincareProofDependencies_component_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package discharges the universe-indexed
completion criterion through the certified component-slot topology-extraction
route.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
    witness
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate component canonical statement route converts to the remaining
dependency package and then applies the remaining-dependency component route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_component_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_poincareProofDependencies_component_requirements
      dependencies =
      canonical_three_sphere_statement_of_remaining_dependency_component_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component canonical statement route converts to the
remaining dependency package and then applies the certified component route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      canonical_three_sphere_statement_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate component canonical payload route converts to the remaining
dependency package and then applies the remaining-dependency component payload.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_component_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_payload_of_poincareProofDependencies_component_requirements
      dependencies =
      canonical_completion_payload_of_remaining_dependency_component_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate component canonical target route converts to the remaining
dependency package and then applies the remaining-dependency component target.
-/
theorem canonical_completion_target_of_poincareProofDependencies_component_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_target_of_poincareProofDependencies_component_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_component_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate component canonical criterion route converts to the remaining
dependency package and then applies the remaining-dependency component
criterion.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_component_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_criterion_of_poincareProofDependencies_component_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_component_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component canonical payload route converts to the
remaining dependency package and then applies the certified component payload.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component canonical target route converts to the
remaining dependency package and then applies the certified component target.
-/
theorem canonical_completion_target_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_target_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component canonical criterion route converts to the
remaining dependency package and then applies the certified component criterion.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate proof dependency package exposes the canonical completion payload
through the crosswalk package-layer requirement route.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_package_layer_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_remaining_dependency_package_layer_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package proves the canonical completion target
through the crosswalk package-layer requirement route.
-/
theorem canonical_completion_target_of_poincareProofDependencies_package_layer_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_remaining_dependency_package_layer_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package discharges the universe-indexed
completion criterion through the crosswalk package-layer requirement route.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_package_layer_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_package_layer_requirements
    witness
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical completion payload
through the certified package-layer topology-extraction route.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package proves the canonical completion target
through the certified package-layer topology-extraction route.
-/
theorem canonical_completion_target_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package discharges the universe-indexed
completion criterion through the certified package-layer topology-extraction
route.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
    witness
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical completion payload
through the crosswalk milestone-requirement route.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_milestone_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_remaining_dependency_milestone_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package proves the canonical completion target
through the crosswalk milestone-requirement route.
-/
theorem canonical_completion_target_of_poincareProofDependencies_milestone_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_remaining_dependency_milestone_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package discharges the universe-indexed
completion criterion through the crosswalk milestone-requirement route.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_milestone_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_milestone_requirements
    witness
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package exposes the canonical completion payload
through the certified milestone topology-extraction route.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package proves the canonical completion target
through the certified milestone topology-extraction route.
-/
theorem canonical_completion_target_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate proof dependency package discharges the universe-indexed
completion criterion through the certified milestone topology-extraction route.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
    witness
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The aggregate package-layer canonical statement route converts to the remaining
dependency package and then applies the remaining-dependency package-layer route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      canonical_three_sphere_statement_of_remaining_dependency_package_layer_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer canonical statement route converts to the
remaining dependency package and then applies the certified package-layer route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      canonical_three_sphere_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate package-layer canonical payload route converts to the remaining
dependency package and then applies the remaining-dependency package-layer
payload.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_package_layer_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_payload_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      canonical_completion_payload_of_remaining_dependency_package_layer_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate package-layer canonical target route converts to the remaining
dependency package and then applies the remaining-dependency package-layer
target.
-/
theorem canonical_completion_target_of_poincareProofDependencies_package_layer_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_target_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_package_layer_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate package-layer canonical criterion route converts to the remaining
dependency package and then applies the remaining-dependency package-layer
criterion.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_package_layer_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_criterion_of_poincareProofDependencies_package_layer_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_package_layer_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer canonical payload route converts to the
remaining dependency package and then applies the certified package-layer
payload.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer canonical target route converts to the
remaining dependency package and then applies the certified package-layer target.
-/
theorem canonical_completion_target_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_target_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer canonical criterion route converts to the
remaining dependency package and then applies the certified package-layer
criterion.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone canonical statement route converts to the remaining
dependency package and then applies the remaining-dependency milestone route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_milestone_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_poincareProofDependencies_milestone_requirements
      dependencies =
      canonical_three_sphere_statement_of_remaining_dependency_milestone_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone canonical statement route converts to the
remaining dependency package and then applies the certified milestone route.
-/
theorem canonical_three_sphere_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      canonical_three_sphere_statement_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone canonical payload route converts to the remaining
dependency package and then applies the remaining-dependency milestone payload.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_milestone_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_payload_of_poincareProofDependencies_milestone_requirements
      dependencies =
      canonical_completion_payload_of_remaining_dependency_milestone_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone canonical target route converts to the remaining
dependency package and then applies the remaining-dependency milestone target.
-/
theorem canonical_completion_target_of_poincareProofDependencies_milestone_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_target_of_poincareProofDependencies_milestone_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_milestone_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone canonical criterion route converts to the remaining
dependency package and then applies the remaining-dependency milestone criterion.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_milestone_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_criterion_of_poincareProofDependencies_milestone_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_milestone_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone canonical payload route converts to the
remaining dependency package and then applies the certified milestone payload.
-/
theorem canonical_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone canonical target route converts to the
remaining dependency package and then applies the certified milestone target.
-/
theorem canonical_completion_target_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_target_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone canonical criterion route converts to the
remaining dependency package and then applies the certified milestone criterion.
-/
theorem canonical_completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    canonical_completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate proof dependency package exposes the project completion payload
through the crosswalk component-slot requirement route.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_component_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_poincareProofDependencies_component_requirements
      dependencies)

/--
The aggregate proof dependency package proves the project target through the
crosswalk component-slot requirement route.
-/
theorem poincare_statement_of_poincareProofDependencies_component_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_poincareProofDependencies_component_requirements
    dependencies

/--
The aggregate proof dependency package discharges the project criterion through
the crosswalk component-slot requirement route.
-/
theorem completion_criterion_of_poincareProofDependencies_component_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_poincareProofDependencies_component_requirements
    witness dependencies

/--
The aggregate proof dependency package exposes the project completion payload
through the certified component-slot topology-extraction route.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies)

/--
The aggregate proof dependency package proves the project target through the
certified component-slot topology-extraction route.
-/
theorem poincare_statement_of_poincareProofDependencies_component_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_poincareProofDependencies_component_extraction_derivation_requirements
    dependencies

/--
The aggregate proof dependency package discharges the project criterion through
the certified component-slot topology-extraction route.
-/
theorem completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements
    witness dependencies

/--
The aggregate proof dependency package exposes the project completion payload
through the crosswalk package-layer requirement route.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_package_layer_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_poincareProofDependencies_package_layer_requirements
      dependencies)

/--
The aggregate proof dependency package proves the project target through the
crosswalk package-layer requirement route.
-/
theorem poincare_statement_of_poincareProofDependencies_package_layer_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_poincareProofDependencies_package_layer_requirements
    dependencies

/--
The aggregate proof dependency package discharges the project criterion through
the crosswalk package-layer requirement route.
-/
theorem completion_criterion_of_poincareProofDependencies_package_layer_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_poincareProofDependencies_package_layer_requirements
    witness dependencies

/--
The aggregate proof dependency package exposes the project completion payload
through the certified package-layer topology-extraction route.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies)

/--
The aggregate proof dependency package proves the project target through the
certified package-layer topology-extraction route.
-/
theorem poincare_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    dependencies

/--
The aggregate proof dependency package discharges the project criterion through
the certified package-layer topology-extraction route.
-/
theorem completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    witness dependencies

/--
The aggregate proof dependency package exposes the project completion payload
through the crosswalk milestone-requirement route.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_milestone_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_poincareProofDependencies_milestone_requirements
      dependencies)

/--
The aggregate proof dependency package proves the project target through the
crosswalk milestone-requirement route.
-/
theorem poincare_statement_of_poincareProofDependencies_milestone_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_poincareProofDependencies_milestone_requirements
    dependencies

/--
The aggregate proof dependency package discharges the project criterion through
the crosswalk milestone-requirement route.
-/
theorem completion_criterion_of_poincareProofDependencies_milestone_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_poincareProofDependencies_milestone_requirements
    witness dependencies

/--
The aggregate proof dependency package exposes the project completion payload
through the certified milestone topology-extraction route.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_canonical_completion_payload
    (canonical_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies)

/--
The aggregate proof dependency package proves the project target through the
certified milestone topology-extraction route.
-/
theorem poincare_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    dependencies

/--
The aggregate proof dependency package discharges the project criterion through
the certified milestone topology-extraction route.
-/
theorem completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    witness dependencies

/--
The aggregate component project payload is the project payload induced by the
aggregate component canonical payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_component_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_component_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_poincareProofDependencies_component_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate component project statement is the target projected from the
aggregate component canonical payload route.
-/
theorem poincare_statement_of_poincareProofDependencies_component_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_component_requirements
      dependencies =
      canonical_completion_target_of_poincareProofDependencies_component_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The aggregate component project criterion is the criterion projected from the
aggregate component canonical payload route.
-/
theorem completion_criterion_of_poincareProofDependencies_component_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_component_requirements
      witness dependencies =
      canonical_completion_criterion_of_poincareProofDependencies_component_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The aggregate certified component project payload is the project payload
induced by the aggregate certified component canonical payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component project statement is the target projected
from the aggregate certified component canonical payload route.
-/
theorem poincare_statement_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_poincareProofDependencies_component_extraction_derivation_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The aggregate certified component project criterion is the criterion projected
from the aggregate certified component canonical payload route.
-/
theorem completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The aggregate package-layer project payload is the project payload induced by
the aggregate package-layer canonical payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_package_layer_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_poincareProofDependencies_package_layer_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate package-layer project statement is the target projected from the
aggregate package-layer canonical payload route.
-/
theorem poincare_statement_of_poincareProofDependencies_package_layer_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      canonical_completion_target_of_poincareProofDependencies_package_layer_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The aggregate package-layer project criterion is the criterion projected from
the aggregate package-layer canonical payload route.
-/
theorem completion_criterion_of_poincareProofDependencies_package_layer_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_package_layer_requirements
      witness dependencies =
      canonical_completion_criterion_of_poincareProofDependencies_package_layer_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer project payload is the project payload
induced by the aggregate certified package-layer canonical payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer project statement is the target projected
from the aggregate certified package-layer canonical payload route.
-/
theorem poincare_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer project criterion is the criterion
projected from the aggregate certified package-layer canonical payload route.
-/
theorem completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The aggregate milestone project payload is the project payload induced by the
aggregate milestone canonical payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_milestone_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_milestone_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_poincareProofDependencies_milestone_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone project statement is the target projected from the
aggregate milestone canonical payload route.
-/
theorem poincare_statement_of_poincareProofDependencies_milestone_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_milestone_requirements
      dependencies =
      canonical_completion_target_of_poincareProofDependencies_milestone_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The aggregate milestone project criterion is the criterion projected from the
aggregate milestone canonical payload route.
-/
theorem completion_criterion_of_poincareProofDependencies_milestone_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_milestone_requirements
      witness dependencies =
      canonical_completion_criterion_of_poincareProofDependencies_milestone_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The aggregate certified milestone project payload is the project payload
induced by the aggregate certified milestone canonical payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_canonical_completion_payload
        (canonical_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone project statement is the target projected
from the aggregate certified milestone canonical payload route.
-/
theorem poincare_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      canonical_completion_target_of_poincareProofDependencies_milestone_extraction_derivation_requirements
        dependencies := by
  apply Subsingleton.elim

/--
The aggregate certified milestone project criterion is the criterion projected
from the aggregate certified milestone canonical payload route.
-/
theorem completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      witness dependencies =
      canonical_completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements
        witness dependencies := by
  apply Subsingleton.elim

/--
The aggregate component project payload converts to the remaining-dependency
component project payload through the aggregate/remaining package equivalence.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_component_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_component_requirements
      dependencies =
      poincare_completion_payload_of_remaining_dependency_component_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate component project statement converts to the remaining-dependency
component project statement through the aggregate/remaining package equivalence.
-/
theorem poincare_statement_of_poincareProofDependencies_component_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_component_requirements
      dependencies =
      poincare_statement_of_remaining_dependency_component_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate component project criterion converts to the remaining-dependency
component project criterion through the aggregate/remaining package equivalence.
-/
theorem completion_criterion_of_poincareProofDependencies_component_requirements_to_remaining_dependency_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_component_requirements
      witness dependencies =
      completion_criterion_of_remaining_dependency_component_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component project payload converts to the certified
remaining-dependency component project payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component project statement converts to the certified
remaining-dependency component project statement.
-/
theorem poincare_statement_of_poincareProofDependencies_component_extraction_derivation_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      poincare_statement_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component project criterion converts to the certified
remaining-dependency component project criterion.
-/
theorem completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements_to_remaining_dependency_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_component_extraction_derivation_requirements
      witness dependencies =
      completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate package-layer project payload converts to the remaining-dependency
package-layer project payload through the aggregate/remaining package equivalence.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_package_layer_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      poincare_completion_payload_of_remaining_dependency_package_layer_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate package-layer project statement converts to the remaining-dependency
package-layer project statement through the aggregate/remaining package equivalence.
-/
theorem poincare_statement_of_poincareProofDependencies_package_layer_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      poincare_statement_of_remaining_dependency_package_layer_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate package-layer project criterion converts to the remaining-dependency
package-layer project criterion through the aggregate/remaining package equivalence.
-/
theorem completion_criterion_of_poincareProofDependencies_package_layer_requirements_to_remaining_dependency_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_package_layer_requirements
      witness dependencies =
      completion_criterion_of_remaining_dependency_package_layer_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer project payload converts to the certified
remaining-dependency package-layer project payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer project statement converts to the
certified remaining-dependency package-layer project statement.
-/
theorem poincare_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      poincare_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer project criterion converts to the
certified remaining-dependency package-layer project criterion.
-/
theorem completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_to_remaining_dependency_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      witness dependencies =
      completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone project payload converts to the remaining-dependency
milestone project payload through the aggregate/remaining package equivalence.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_milestone_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_milestone_requirements
      dependencies =
      poincare_completion_payload_of_remaining_dependency_milestone_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone project statement converts to the remaining-dependency
milestone project statement through the aggregate/remaining package equivalence.
-/
theorem poincare_statement_of_poincareProofDependencies_milestone_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_milestone_requirements
      dependencies =
      poincare_statement_of_remaining_dependency_milestone_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate milestone project criterion converts to the remaining-dependency
milestone project criterion through the aggregate/remaining package equivalence.
-/
theorem completion_criterion_of_poincareProofDependencies_milestone_requirements_to_remaining_dependency_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_milestone_requirements
      witness dependencies =
      completion_criterion_of_remaining_dependency_milestone_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone project payload converts to the certified
remaining-dependency milestone project payload.
-/
theorem poincare_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      poincare_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone project statement converts to the certified
remaining-dependency milestone project statement.
-/
theorem poincare_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements_to_remaining_dependency_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      poincare_statement_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone project criterion converts to the certified
remaining-dependency milestone project criterion.
-/
theorem completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements_to_remaining_dependency_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      witness dependencies =
      completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements
        witness
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining dependency package exposes the project target and explicit
completion criterion before the canonical-completion bridge is applied.
-/
theorem poincare_completion_payload_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_dependencies dependencies

/--
The remaining dependency package project-completion payload is the aggregate
dependency completion payload.
-/
theorem poincare_completion_payload_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    poincare_completion_payload_of_remaining_dependency_package dependencies =
      poincare_completion_payload_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The aggregate dependency package produces the canonical completion target and
explicit completion criterion payload, but the package itself is not
constructed in this project.
-/
theorem canonical_completion_payload_of_dependencies
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_remaining_dependency_package dependencies)

/--
The aggregate dependency canonical payload is obtained by applying the canonical
payload bridge to the named remaining-dependency project payload.
-/
theorem canonical_completion_payload_of_dependencies_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_dependencies dependencies =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_remaining_dependency_package
          dependencies) := by
  apply Subsingleton.elim

/--
The dependency package is sufficient for the canonical completion target,
extracted from the aggregate canonical-completion payload.
-/
theorem canonical_completion_target_of_dependencies
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_dependencies dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The aggregate dependency canonical target projection is extracted from the
named aggregate canonical payload.
-/
theorem canonical_completion_target_of_dependencies_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_dependencies dependencies =
      (by
        rcases canonical_completion_payload_of_dependencies dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The dependency package discharges the universe-indexed completion criterion
through the aggregate canonical-completion payload.
-/
theorem canonical_completion_criterion_of_dependencies
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_dependencies dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The aggregate dependency completion criterion projection is extracted from the
named aggregate canonical payload.
-/
theorem canonical_completion_criterion_of_dependencies_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_dependencies witness dependencies =
      (by
        rcases canonical_completion_payload_of_dependencies dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The aggregate dependency package also produces the canonical completion target
and explicit completion criterion through the certified extraction-derivation
route.
-/
theorem canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
      dependencies)

/--
The certified aggregate canonical payload is obtained by applying the canonical
payload bridge to the named certified aggregate project payload.
-/
theorem canonical_completion_payload_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
      dependencies =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_aggregate_extraction_derivation_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate dependency package proves the canonical completion target through
the certified extraction-derivation route.
-/
theorem canonical_completion_target_of_aggregate_extraction_derivation_dependencies
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases
      canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The certified aggregate canonical target projection is extracted from the named
certified aggregate canonical payload.
-/
theorem canonical_completion_target_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The aggregate dependency package discharges the universe-indexed completion
criterion through the certified extraction-derivation route.
-/
theorem canonical_completion_criterion_of_aggregate_extraction_derivation_dependencies
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The certified aggregate completion criterion projection is extracted from the
named certified aggregate canonical payload.
-/
theorem canonical_completion_criterion_of_aggregate_extraction_derivation_dependencies_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_aggregate_extraction_derivation_dependencies
      witness dependencies =
      (by
        rcases
            canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
              dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The projection-based dependency assembly route also proves the canonical
completion target.
-/
theorem canonical_completion_payload_of_dependency_projections
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_dependency_projections dependencies)

/--
The projection-route canonical payload is obtained by applying the canonical
payload bridge to the named projection-route project payload.
-/
theorem canonical_completion_payload_of_dependency_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_dependency_projections dependencies =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_dependency_projections dependencies) := by
  apply Subsingleton.elim

/--
The projection-based dependency assembly route also proves the canonical
completion target, extracted from the final canonical-completion payload.
-/
theorem canonical_completion_target_of_dependency_projections
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_dependency_projections dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The projection-route canonical target projection is extracted from the named
projection-route canonical payload.
-/
theorem canonical_completion_target_of_dependency_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_dependency_projections dependencies =
      (by
        rcases canonical_completion_payload_of_dependency_projections
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The projection-based dependency assembly route also discharges the explicit
universe-indexed completion criterion through the final canonical-completion
payload.
-/
theorem canonical_completion_criterion_of_dependency_projections
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_dependency_projections dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The projection-route completion criterion projection is extracted from the
named projection-route canonical payload.
-/
theorem canonical_completion_criterion_of_dependency_projections_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_dependency_projections
      witness dependencies =
      (by
        rcases canonical_completion_payload_of_dependency_projections
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The certified extraction-derivation projection route also proves the canonical
completion target.
-/
theorem canonical_completion_payload_of_extraction_derivation_dependency_projections
    (dependencies : RemainingDependencyPackage.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact canonical_completion_payload_of_poincare_completion_payload
    (poincare_completion_payload_of_extraction_derivation_dependency_projections
      dependencies)

/--
The certified projection-route canonical payload is obtained by applying the
canonical payload bridge to the named certified projection-route project
payload.
-/
theorem canonical_completion_payload_of_extraction_derivation_dependency_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_payload_of_extraction_derivation_dependency_projections
      dependencies =
      canonical_completion_payload_of_poincare_completion_payload
        (poincare_completion_payload_of_extraction_derivation_dependency_projections
          dependencies) := by
  apply Subsingleton.elim

/--
The certified extraction-derivation projection route also proves the canonical
completion target, extracted from its canonical-completion payload.
-/
theorem canonical_completion_target_of_extraction_derivation_dependency_projections
    (dependencies : RemainingDependencyPackage.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases
      canonical_completion_payload_of_extraction_derivation_dependency_projections
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The certified projection-route canonical target projection is extracted from
the named certified projection-route canonical payload.
-/
theorem canonical_completion_target_of_extraction_derivation_dependency_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_target_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            canonical_completion_payload_of_extraction_derivation_dependency_projections
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The certified extraction-derivation projection route also discharges the
explicit universe-indexed completion criterion through its canonical-completion
payload.
-/
theorem canonical_completion_criterion_of_extraction_derivation_dependency_projections
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      canonical_completion_payload_of_extraction_derivation_dependency_projections
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The certified projection-route completion criterion projection is extracted
from the named certified projection-route canonical payload.
-/
theorem canonical_completion_criterion_of_extraction_derivation_dependency_projections_eq
    (witness : Type u) (dependencies : RemainingDependencyPackage.{u}) :
    canonical_completion_criterion_of_extraction_derivation_dependency_projections
      witness dependencies =
      (by
        rcases
            canonical_completion_payload_of_extraction_derivation_dependency_projections
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
A checked Prop-valued certificate shape for a completed Poincare formalization
artifact.

The certificate records the reserved theorem name, the remaining dependency
package, the canonical target, and the universe-indexed completion criterion.
It is not itself a constructor for the missing theorem: proving this proposition
still requires `RemainingDependencyPackage`, which the local project deliberately
does not provide.
-/
def PoincareCompletionCertificate : Prop :=
  ∃ theoremName : String,
    theoremName = canonicalCompletionTheoremName ∧
    RemainingDependencyPackage.{u} ∧
    canonicalCompletionTarget.{u} ∧
    ∀ witness : Type u, CompletionCriterionAtUniverse witness

/-- A completion certificate uses the reserved theorem name `poincare_conjecture`. -/
theorem poincareCompletionCertificate_theoremName_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ theoremName : String,
      theoremName = "poincare_conjecture" := by
  rcases certificate with
    ⟨theoremName, theoremName_eq, _dependencies, _target, _criterion⟩
  exact ⟨theoremName, theoremName_eq.trans canonicalCompletionTheoremName_eq⟩

/--
The reserved theorem-name payload is selected directly from the checked
certificate record and the canonical theorem-name literal.
-/
theorem poincareCompletionCertificate_theoremName_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_theoremName_payload certificate =
      (by
        rcases certificate with
          ⟨theoremName, theoremName_eq, _dependencies, _target, _criterion⟩
        exact
          ⟨theoremName,
            theoremName_eq.trans canonicalCompletionTheoremName_eq⟩) := by
  apply Subsingleton.elim

/--
A completion certificate exposes the full artifact payload using the literal
reserved theorem name.
-/
theorem poincareCompletionCertificate_literal_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ theoremName : String,
      theoremName = "poincare_conjecture" ∧
      RemainingDependencyPackage.{u} ∧
      canonicalCompletionTarget.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases certificate with
    ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
  exact ⟨theoremName, theoremName_eq.trans canonicalCompletionTheoremName_eq,
    dependencies, target, criterion⟩

/--
The literal certificate payload is selected directly from the checked
certificate record and the canonical theorem-name literal.
-/
theorem poincareCompletionCertificate_literal_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_literal_payload certificate =
      (by
        rcases certificate with
          ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
        exact
          ⟨theoremName,
            theoremName_eq.trans canonicalCompletionTheoremName_eq,
            dependencies, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The literal full artifact payload reconstructs the checked completion
certificate.
-/
theorem completion_certificate_of_literal_payload
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        RemainingDependencyPackage.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
  exact ⟨theoremName, theoremName_eq.trans canonicalCompletionTheoremName_eq.symm,
    dependencies, target, criterion⟩

/--
The literal-payload certificate constructor rewrites only the literal reserved
name back to the canonical theorem name.
-/
theorem completion_certificate_of_literal_payload_eq
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        RemainingDependencyPackage.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_certificate_of_literal_payload payload =
      (by
        rcases payload with
          ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
        exact
          ⟨theoremName,
            theoremName_eq.trans canonicalCompletionTheoremName_eq.symm,
            dependencies, target, criterion⟩) := by
  apply Subsingleton.elim

/--
Projecting the literal payload from the literal-payload certificate constructor
recovers the supplied payload.
-/
theorem poincareCompletionCertificate_literal_payload_of_completion_certificate_of_literal_payload_eq
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        RemainingDependencyPackage.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    poincareCompletionCertificate_literal_payload
      (completion_certificate_of_literal_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to its literal reserved-name
artifact payload.
-/
theorem poincareCompletionCertificate_iff_literal_payload :
    PoincareCompletionCertificate.{u} ↔
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        RemainingDependencyPackage.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨poincareCompletionCertificate_literal_payload,
    completion_certificate_of_literal_payload⟩

/--
The literal-payload equivalence is the pair of the named projection and named
constructor.
-/
theorem poincareCompletionCertificate_iff_literal_payload_eq :
    poincareCompletionCertificate_iff_literal_payload =
      ⟨poincareCompletionCertificate_literal_payload,
        completion_certificate_of_literal_payload⟩ := by
  apply Subsingleton.elim

/--
A completion certificate exposes the canonical target and explicit completion
criterion as one payload.
-/
theorem canonical_completion_payload_of_completion_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases certificate with
    ⟨_theoremName, _theoremName_eq, _dependencies, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The canonical completion payload projection is selected directly from the
checked certificate record.
-/
theorem canonical_completion_payload_of_completion_certificate_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    canonical_completion_payload_of_completion_certificate certificate =
      (by
        rcases certificate with
          ⟨_theoremName, _theoremName_eq, _dependencies, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
A completion certificate exposes the project Poincare target and explicit
completion criterion as one payload.
-/
theorem poincare_completion_payload_of_completion_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_completion_certificate certificate with
    ⟨target, criterion⟩
  exact ⟨target, criterion⟩

/--
The project completion payload projection is extracted from the named canonical
completion payload carried by the certificate.
-/
theorem poincare_completion_payload_of_completion_certificate_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincare_completion_payload_of_completion_certificate certificate =
      (by
        rcases canonical_completion_payload_of_completion_certificate
            certificate with
          ⟨target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/-- A completion certificate proves the canonical completion target. -/
theorem canonical_completion_target_of_completion_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    canonicalCompletionTarget.{u} := by
  rcases canonical_completion_payload_of_completion_certificate certificate with
    ⟨target, _criterion⟩
  exact target

/--
The canonical target projection is extracted from the named canonical payload
carried by the certificate.
-/
theorem canonical_completion_target_of_completion_certificate_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    canonical_completion_target_of_completion_certificate certificate =
      (by
        rcases canonical_completion_payload_of_completion_certificate
            certificate with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/-- A completion certificate proves the project Poincare target statement. -/
theorem target_statement_of_completion_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    PoincareConjectureStatement.{u} :=
  canonical_completion_target_of_completion_certificate certificate

/--
The project target-statement projection is the canonical target projection
viewed at the project target proposition.
-/
theorem target_statement_of_completion_certificate_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    target_statement_of_completion_certificate certificate =
      canonical_completion_target_of_completion_certificate certificate := by
  apply Subsingleton.elim

/--
A completion certificate discharges the explicit universe-indexed completion
criterion.
-/
theorem completion_criterion_of_completion_certificate
    (witness : Type u) (certificate : PoincareCompletionCertificate.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases canonical_completion_payload_of_completion_certificate certificate with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The completion-criterion projection is extracted from the named canonical
payload carried by the certificate.
-/
theorem completion_criterion_of_completion_certificate_eq
    (witness : Type u) (certificate : PoincareCompletionCertificate.{u}) :
    completion_criterion_of_completion_certificate witness certificate =
      (by
        rcases canonical_completion_payload_of_completion_certificate
            certificate with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
A completion certificate explicitly contains the remaining-dependency package
needed to construct it.
-/
theorem remaining_dependency_package_of_completion_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    RemainingDependencyPackage.{u} := by
  rcases certificate with
    ⟨_theoremName, _theoremName_eq, dependencies, _target, _criterion⟩
  exact dependencies

/--
The remaining-dependency projection is selected directly from the checked
certificate record.
-/
theorem remaining_dependency_package_of_completion_certificate_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    remaining_dependency_package_of_completion_certificate certificate =
      (by
        rcases certificate with
          ⟨_theoremName, _theoremName_eq, dependencies, _target, _criterion⟩
        exact dependencies) := by
  apply Subsingleton.elim

/--
A remaining-dependency package and an explicit project completion payload
reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_remaining_dependency_and_poincare_payload
    (dependencies : RemainingDependencyPackage.{u})
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with ⟨target, criterion⟩
  exact ⟨canonicalCompletionTheoremName, rfl, dependencies, target, criterion⟩

/--
The project-payload certificate constructor stores the canonical reserved name,
the supplied remaining dependency package, and the supplied project payload.
-/
theorem completion_certificate_of_remaining_dependency_and_poincare_payload_eq
    (dependencies : RemainingDependencyPackage.{u})
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_certificate_of_remaining_dependency_and_poincare_payload
      dependencies payload =
      (by
        rcases payload with ⟨target, criterion⟩
        exact
          ⟨canonicalCompletionTheoremName, rfl, dependencies, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to a remaining-dependency
package together with the project completion payload.
-/
theorem poincareCompletionCertificate_iff_remainingDependencyPackage_and_poincare_payload :
    PoincareCompletionCertificate.{u} ↔
      RemainingDependencyPackage.{u} ∧
        ∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  constructor
  · intro certificate
    exact ⟨remaining_dependency_package_of_completion_certificate certificate,
      poincare_completion_payload_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, payload⟩
    exact completion_certificate_of_remaining_dependency_and_poincare_payload
      dependencies payload

/--
A remaining-dependency package and an explicit canonical completion payload
reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_remaining_dependency_and_canonical_payload
    (dependencies : RemainingDependencyPackage.{u})
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_poincare_payload
    dependencies
    (poincare_completion_payload_of_canonical_completion_payload payload)

/--
The canonical-payload certificate constructor delegates through the named
project-payload bridge.
-/
theorem completion_certificate_of_remaining_dependency_and_canonical_payload_eq
    (dependencies : RemainingDependencyPackage.{u})
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_certificate_of_remaining_dependency_and_canonical_payload
      dependencies payload =
      completion_certificate_of_remaining_dependency_and_poincare_payload
        dependencies
        (poincare_completion_payload_of_canonical_completion_payload
          payload) := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to a remaining-dependency
package together with the canonical completion payload.
-/
theorem poincareCompletionCertificate_iff_remainingDependencyPackage_and_canonical_payload :
    PoincareCompletionCertificate.{u} ↔
      RemainingDependencyPackage.{u} ∧
        ∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  constructor
  · intro certificate
    exact ⟨remaining_dependency_package_of_completion_certificate certificate,
      canonical_completion_payload_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, payload⟩
    exact completion_certificate_of_remaining_dependency_and_canonical_payload
      dependencies payload

/--
A remaining-dependency package and a proof of the project target statement
reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_remaining_dependency_and_target_statement
    (dependencies : RemainingDependencyPackage.{u})
    (target : PoincareConjectureStatement.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_poincare_payload
    dependencies
    (poincare_completion_payload_of_poincareConjectureStatement target)

/--
The target-statement certificate constructor delegates through the named
project-payload bridge for a supplied project target.
-/
theorem completion_certificate_of_remaining_dependency_and_target_statement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (target : PoincareConjectureStatement.{u}) :
    completion_certificate_of_remaining_dependency_and_target_statement
      dependencies target =
      completion_certificate_of_remaining_dependency_and_poincare_payload
        dependencies
        (poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to a remaining-dependency
package together with the project target statement.
-/
theorem poincareCompletionCertificate_iff_remainingDependencyPackage_and_target_statement :
    PoincareCompletionCertificate.{u} ↔
      RemainingDependencyPackage.{u} ∧ PoincareConjectureStatement.{u} := by
  constructor
  · intro certificate
    exact ⟨remaining_dependency_package_of_completion_certificate certificate,
      target_statement_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, target⟩
    exact completion_certificate_of_remaining_dependency_and_target_statement
      dependencies target

/--
A remaining-dependency package and a proof of the canonical completion target
reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_remaining_dependency_and_canonical_target
    (dependencies : RemainingDependencyPackage.{u})
    (target : canonicalCompletionTarget.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    dependencies
    (canonical_completion_payload_of_canonical_completion_target target)

/--
The canonical-target certificate constructor delegates through the named
canonical-payload bridge for a supplied canonical target.
-/
theorem completion_certificate_of_remaining_dependency_and_canonical_target_eq
    (dependencies : RemainingDependencyPackage.{u})
    (target : canonicalCompletionTarget.{u}) :
    completion_certificate_of_remaining_dependency_and_canonical_target
      dependencies target =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies
        (canonical_completion_payload_of_canonical_completion_target
          target) := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to a remaining-dependency
package together with the canonical completion target.
-/
theorem poincareCompletionCertificate_iff_remainingDependencyPackage_and_canonical_target :
    PoincareCompletionCertificate.{u} ↔
      RemainingDependencyPackage.{u} ∧ canonicalCompletionTarget.{u} := by
  constructor
  · intro certificate
    exact ⟨remaining_dependency_package_of_completion_certificate certificate,
      canonical_completion_target_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, target⟩
    exact completion_certificate_of_remaining_dependency_and_canonical_target
      dependencies target

/--
A remaining-dependency package and a proof of the explicit universe-indexed
completion criterion reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_remaining_dependency_and_completion_criterion
    (dependencies : RemainingDependencyPackage.{u}) (witness : Type u)
    (criterion : CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_target
    dependencies
    (canonical_completion_target_of_completion_criterion witness criterion)

/--
The completion-criterion certificate constructor delegates through the named
canonical-target bridge for the supplied universe-indexed criterion.
-/
theorem completion_certificate_of_remaining_dependency_and_completion_criterion_eq
    (dependencies : RemainingDependencyPackage.{u}) (witness : Type u)
    (criterion : CompletionCriterionAtUniverse witness) :
    completion_certificate_of_remaining_dependency_and_completion_criterion
      dependencies witness criterion =
      completion_certificate_of_remaining_dependency_and_canonical_target
        dependencies
        (canonical_completion_target_of_completion_criterion witness
          criterion) := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to a remaining-dependency
package together with the explicit universe-indexed completion criterion.
-/
theorem poincareCompletionCertificate_iff_remainingDependencyPackage_and_completion_criterion
    (witness : Type u) :
    PoincareCompletionCertificate.{u} ↔
      RemainingDependencyPackage.{u} ∧ CompletionCriterionAtUniverse witness := by
  constructor
  · intro certificate
    exact ⟨remaining_dependency_package_of_completion_certificate certificate,
      completion_criterion_of_completion_certificate witness certificate⟩
  · rintro ⟨dependencies, criterion⟩
    exact completion_certificate_of_remaining_dependency_and_completion_criterion
      dependencies witness criterion

/--
A completion certificate also exposes the aggregate proof dependency package
named by the lower-level dependency spine.
-/
theorem poincareProofDependencies_of_completion_certificate
    (certificate : PoincareCompletionCertificate.{u}) :
    PoincareProofDependencies.{u} :=
  remainingDependencyPackage_iff_poincareProofDependencies.mp
    (remaining_dependency_package_of_completion_certificate certificate)

/--
The aggregate dependency projection from a certificate is the remaining
dependency projection followed by the remaining/aggregate equivalence.
-/
theorem poincareProofDependencies_of_completion_certificate_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareProofDependencies_of_completion_certificate certificate =
      remainingDependencyPackage_iff_poincareProofDependencies.mp
        (remaining_dependency_package_of_completion_certificate
          certificate) := by
  apply Subsingleton.elim

/--
A completed remaining-dependency package produces a completion certificate
through the aggregate dependency route.
-/
theorem completion_certificate_of_remaining_dependency_package
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} := by
  rcases canonical_completion_payload_of_dependencies dependencies with
    ⟨target, criterion⟩
  exact ⟨canonicalCompletionTheoremName, rfl, dependencies, target, criterion⟩

/--
The remaining-dependency certificate constructor extracts the target and
criterion from the named aggregate canonical-completion payload.
-/
theorem completion_certificate_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_remaining_dependency_package dependencies =
      (by
        rcases canonical_completion_payload_of_dependencies dependencies with
          ⟨target, criterion⟩
        exact
          ⟨canonicalCompletionTheoremName, rfl, dependencies, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
Projecting the remaining-dependency package from the project-payload certificate
constructor recovers the supplied package.
-/
theorem remaining_dependency_package_of_completion_certificate_of_remaining_dependency_and_poincare_payload_eq
    (dependencies : RemainingDependencyPackage.{u})
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    remaining_dependency_package_of_completion_certificate
      (completion_certificate_of_remaining_dependency_and_poincare_payload
        dependencies payload) =
      dependencies := by
  apply Subsingleton.elim

/--
Projecting the project completion payload from the project-payload certificate
constructor recovers the supplied payload.
-/
theorem poincare_completion_payload_of_completion_certificate_of_remaining_dependency_and_poincare_payload_eq
    (dependencies : RemainingDependencyPackage.{u})
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    poincare_completion_payload_of_completion_certificate
      (completion_certificate_of_remaining_dependency_and_poincare_payload
        dependencies payload) =
      payload := by
  apply Subsingleton.elim

/--
Projecting the canonical completion payload from the canonical-payload
certificate constructor recovers the supplied payload.
-/
theorem canonical_completion_payload_of_completion_certificate_of_remaining_dependency_and_canonical_payload_eq
    (dependencies : RemainingDependencyPackage.{u})
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonical_completion_payload_of_completion_certificate
      (completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies payload) =
      payload := by
  apply Subsingleton.elim

/--
Projecting the project target from the target-statement certificate constructor
recovers the supplied target.
-/
theorem target_statement_of_completion_certificate_of_remaining_dependency_and_target_statement_eq
    (dependencies : RemainingDependencyPackage.{u})
    (target : PoincareConjectureStatement.{u}) :
    target_statement_of_completion_certificate
      (completion_certificate_of_remaining_dependency_and_target_statement
        dependencies target) =
      target := by
  apply Subsingleton.elim

/--
Projecting the canonical target from the canonical-target certificate constructor
recovers the supplied target.
-/
theorem canonical_completion_target_of_completion_certificate_of_remaining_dependency_and_canonical_target_eq
    (dependencies : RemainingDependencyPackage.{u})
    (target : canonicalCompletionTarget.{u}) :
    canonical_completion_target_of_completion_certificate
      (completion_certificate_of_remaining_dependency_and_canonical_target
        dependencies target) =
      target := by
  apply Subsingleton.elim

/--
Projecting the universe-indexed completion criterion from the criterion
certificate constructor recovers the supplied criterion at the same witness.
-/
theorem completion_criterion_of_completion_certificate_of_remaining_dependency_and_completion_criterion_eq
    (dependencies : RemainingDependencyPackage.{u}) (witness : Type u)
    (criterion : CompletionCriterionAtUniverse witness) :
    completion_criterion_of_completion_certificate witness
      (completion_certificate_of_remaining_dependency_and_completion_criterion
        dependencies witness criterion) =
      criterion := by
  apply Subsingleton.elim

/--
Projecting the remaining-dependency package from the aggregate remaining-package
certificate constructor recovers the supplied package.
-/
theorem remaining_dependency_package_of_completion_certificate_of_remaining_dependency_package_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    remaining_dependency_package_of_completion_certificate
      (completion_certificate_of_remaining_dependency_package dependencies) =
      dependencies := by
  apply Subsingleton.elim

/--
The completion certificate is equivalent to the remaining dependency package.
It adds checked artifact accounting, not an additional mathematical assumption.
-/
theorem poincareCompletionCertificate_iff_remainingDependencyPackage :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_remaining_dependency_package⟩

/--
The remaining-dependency equivalence is the pair of the named certificate
projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_remainingDependencyPackage_eq :
    poincareCompletionCertificate_iff_remainingDependencyPackage =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_remaining_dependency_package⟩ := by
  apply Subsingleton.elim

/--
The completion certificate is equivalent to the aggregate proof dependency
package itself.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  poincareCompletionCertificate_iff_remainingDependencyPackage.trans
    remainingDependencyPackage_iff_poincareProofDependencies

/--
The aggregate-dependency equivalence is the remaining-dependency equivalence
composed with the remaining/aggregate dependency equivalence.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies =
      poincareCompletionCertificate_iff_remainingDependencyPackage.trans
        remainingDependencyPackage_iff_poincareProofDependencies := by
  apply Subsingleton.elim

/--
The aggregate proof dependency package produces the checked completion
certificate.
-/
theorem completion_certificate_of_poincareProofDependencies
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  poincareCompletionCertificate_iff_poincareProofDependencies.mpr dependencies

/--
The aggregate dependency certificate constructor is the reverse direction of
the named aggregate-dependency equivalence.
-/
theorem completion_certificate_of_poincareProofDependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies dependencies =
      poincareCompletionCertificate_iff_poincareProofDependencies.mpr
        dependencies := by
  apply Subsingleton.elim

/--
The aggregate proof dependency package and an explicit project completion payload
reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_poincareProofDependencies_and_poincare_payload
    (dependencies : PoincareProofDependencies.{u})
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_poincare_payload
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)
    payload

/--
The checked completion certificate is equivalent to the aggregate proof
dependency package together with the project completion payload.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_poincare_payload :
    PoincareCompletionCertificate.{u} ↔
      PoincareProofDependencies.{u} ∧
        ∃ _target : PoincareConjectureStatement.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  constructor
  · intro certificate
    exact ⟨poincareProofDependencies_of_completion_certificate certificate,
      poincare_completion_payload_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, payload⟩
    exact completion_certificate_of_poincareProofDependencies_and_poincare_payload
      dependencies payload

/--
The aggregate proof dependency package and an explicit canonical completion
payload reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_poincareProofDependencies_and_canonical_payload
    (dependencies : PoincareProofDependencies.{u})
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)
    payload

/--
The checked completion certificate is equivalent to the aggregate proof
dependency package together with the canonical completion payload.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_payload :
    PoincareCompletionCertificate.{u} ↔
      PoincareProofDependencies.{u} ∧
        ∃ _target : canonicalCompletionTarget.{u},
          ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  constructor
  · intro certificate
    exact ⟨poincareProofDependencies_of_completion_certificate certificate,
      canonical_completion_payload_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, payload⟩
    exact completion_certificate_of_poincareProofDependencies_and_canonical_payload
      dependencies payload

/--
The aggregate proof dependency package and a proof of the project target
statement reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_poincareProofDependencies_and_target_statement
    (dependencies : PoincareProofDependencies.{u})
    (target : PoincareConjectureStatement.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_target_statement
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)
    target

/--
The checked completion certificate is equivalent to the aggregate proof
dependency package together with the project target statement.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_target_statement :
    PoincareCompletionCertificate.{u} ↔
      PoincareProofDependencies.{u} ∧ PoincareConjectureStatement.{u} := by
  constructor
  · intro certificate
    exact ⟨poincareProofDependencies_of_completion_certificate certificate,
      target_statement_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, target⟩
    exact completion_certificate_of_poincareProofDependencies_and_target_statement
      dependencies target

/--
The aggregate proof dependency package and a proof of the canonical completion
target reconstruct the checked completion certificate.
-/
theorem completion_certificate_of_poincareProofDependencies_and_canonical_target
    (dependencies : PoincareProofDependencies.{u})
    (target : canonicalCompletionTarget.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_target
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)
    target

/--
The checked completion certificate is equivalent to the aggregate proof
dependency package together with the canonical completion target.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_target :
    PoincareCompletionCertificate.{u} ↔
      PoincareProofDependencies.{u} ∧ canonicalCompletionTarget.{u} := by
  constructor
  · intro certificate
    exact ⟨poincareProofDependencies_of_completion_certificate certificate,
      canonical_completion_target_of_completion_certificate certificate⟩
  · rintro ⟨dependencies, target⟩
    exact completion_certificate_of_poincareProofDependencies_and_canonical_target
      dependencies target

/--
The aggregate proof dependency package and a proof of the explicit
universe-indexed completion criterion reconstruct the checked completion
certificate.
-/
theorem completion_certificate_of_poincareProofDependencies_and_completion_criterion
    (dependencies : PoincareProofDependencies.{u}) (witness : Type u)
    (criterion : CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_completion_criterion
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)
    witness criterion

/--
The checked completion certificate is equivalent to the aggregate proof
dependency package together with the explicit universe-indexed completion
criterion.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_completion_criterion
    (witness : Type u) :
    PoincareCompletionCertificate.{u} ↔
      PoincareProofDependencies.{u} ∧ CompletionCriterionAtUniverse witness := by
  constructor
  · intro certificate
    exact ⟨poincareProofDependencies_of_completion_certificate certificate,
      completion_criterion_of_completion_certificate witness certificate⟩
  · rintro ⟨dependencies, criterion⟩
    exact completion_certificate_of_poincareProofDependencies_and_completion_criterion
      dependencies witness criterion

/--
The aggregate proof dependency plus project-payload certificate constructor
delegates to the corresponding remaining-dependency constructor after the
aggregate/remaining dependency conversion.
-/
theorem completion_certificate_of_poincareProofDependencies_and_poincare_payload_eq
    (dependencies : PoincareProofDependencies.{u})
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_certificate_of_poincareProofDependencies_and_poincare_payload
      dependencies payload =
      completion_certificate_of_remaining_dependency_and_poincare_payload
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies)
        payload := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus project-payload certificate equivalence is
the pair of the named certificate projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_poincare_payload_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_and_poincare_payload =
      (by
        constructor
        · intro certificate
          exact ⟨poincareProofDependencies_of_completion_certificate certificate,
            poincare_completion_payload_of_completion_certificate certificate⟩
        · rintro ⟨dependencies, payload⟩
          exact completion_certificate_of_poincareProofDependencies_and_poincare_payload
            dependencies payload) := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus canonical-payload certificate constructor
delegates to the corresponding remaining-dependency constructor after the
aggregate/remaining dependency conversion.
-/
theorem completion_certificate_of_poincareProofDependencies_and_canonical_payload_eq
    (dependencies : PoincareProofDependencies.{u})
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_certificate_of_poincareProofDependencies_and_canonical_payload
      dependencies payload =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies)
        payload := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus canonical-payload certificate equivalence
is the pair of the named certificate projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_payload_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_payload =
      (by
        constructor
        · intro certificate
          exact ⟨poincareProofDependencies_of_completion_certificate certificate,
            canonical_completion_payload_of_completion_certificate certificate⟩
        · rintro ⟨dependencies, payload⟩
          exact completion_certificate_of_poincareProofDependencies_and_canonical_payload
            dependencies payload) := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus project-target certificate constructor
delegates to the corresponding remaining-dependency constructor after the
aggregate/remaining dependency conversion.
-/
theorem completion_certificate_of_poincareProofDependencies_and_target_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (target : PoincareConjectureStatement.{u}) :
    completion_certificate_of_poincareProofDependencies_and_target_statement
      dependencies target =
      completion_certificate_of_remaining_dependency_and_target_statement
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies)
        target := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus project-target certificate equivalence is
the pair of the named certificate projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_target_statement_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_and_target_statement =
      (by
        constructor
        · intro certificate
          exact ⟨poincareProofDependencies_of_completion_certificate certificate,
            target_statement_of_completion_certificate certificate⟩
        · rintro ⟨dependencies, target⟩
          exact completion_certificate_of_poincareProofDependencies_and_target_statement
            dependencies target) := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus canonical-target certificate constructor
delegates to the corresponding remaining-dependency constructor after the
aggregate/remaining dependency conversion.
-/
theorem completion_certificate_of_poincareProofDependencies_and_canonical_target_eq
    (dependencies : PoincareProofDependencies.{u})
    (target : canonicalCompletionTarget.{u}) :
    completion_certificate_of_poincareProofDependencies_and_canonical_target
      dependencies target =
      completion_certificate_of_remaining_dependency_and_canonical_target
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies)
        target := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus canonical-target certificate equivalence is
the pair of the named certificate projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_target_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_target =
      (by
        constructor
        · intro certificate
          exact ⟨poincareProofDependencies_of_completion_certificate certificate,
            canonical_completion_target_of_completion_certificate certificate⟩
        · rintro ⟨dependencies, target⟩
          exact completion_certificate_of_poincareProofDependencies_and_canonical_target
            dependencies target) := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus criterion certificate constructor delegates
to the corresponding remaining-dependency constructor after the
aggregate/remaining dependency conversion.
-/
theorem completion_certificate_of_poincareProofDependencies_and_completion_criterion_eq
    (dependencies : PoincareProofDependencies.{u}) (witness : Type u)
    (criterion : CompletionCriterionAtUniverse witness) :
    completion_certificate_of_poincareProofDependencies_and_completion_criterion
      dependencies witness criterion =
      completion_certificate_of_remaining_dependency_and_completion_criterion
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies)
        witness criterion := by
  apply Subsingleton.elim

/--
Projecting aggregate dependencies from the aggregate dependency certificate
constructor recovers the supplied aggregate package.
-/
theorem poincareProofDependencies_of_completion_certificate_of_poincareProofDependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincareProofDependencies_of_completion_certificate
      (completion_certificate_of_poincareProofDependencies dependencies) =
      dependencies := by
  apply Subsingleton.elim

/--
Projecting the project completion payload from the aggregate project-payload
certificate constructor recovers the supplied payload.
-/
theorem poincare_completion_payload_of_completion_certificate_of_poincareProofDependencies_and_poincare_payload_eq
    (dependencies : PoincareProofDependencies.{u})
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    poincare_completion_payload_of_completion_certificate
      (completion_certificate_of_poincareProofDependencies_and_poincare_payload
        dependencies payload) =
      payload := by
  apply Subsingleton.elim

/--
Projecting the canonical completion payload from the aggregate canonical-payload
certificate constructor recovers the supplied payload.
-/
theorem canonical_completion_payload_of_completion_certificate_of_poincareProofDependencies_and_canonical_payload_eq
    (dependencies : PoincareProofDependencies.{u})
    (payload :
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonical_completion_payload_of_completion_certificate
      (completion_certificate_of_poincareProofDependencies_and_canonical_payload
        dependencies payload) =
      payload := by
  apply Subsingleton.elim

/--
Projecting the project target from the aggregate target-statement certificate
constructor recovers the supplied target.
-/
theorem target_statement_of_completion_certificate_of_poincareProofDependencies_and_target_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (target : PoincareConjectureStatement.{u}) :
    target_statement_of_completion_certificate
      (completion_certificate_of_poincareProofDependencies_and_target_statement
        dependencies target) =
      target := by
  apply Subsingleton.elim

/--
Projecting the canonical target from the aggregate canonical-target certificate
constructor recovers the supplied target.
-/
theorem canonical_completion_target_of_completion_certificate_of_poincareProofDependencies_and_canonical_target_eq
    (dependencies : PoincareProofDependencies.{u})
    (target : canonicalCompletionTarget.{u}) :
    canonical_completion_target_of_completion_certificate
      (completion_certificate_of_poincareProofDependencies_and_canonical_target
        dependencies target) =
      target := by
  apply Subsingleton.elim

/--
Projecting the universe-indexed criterion from the aggregate criterion
certificate constructor recovers the supplied criterion at the same witness.
-/
theorem completion_criterion_of_completion_certificate_of_poincareProofDependencies_and_completion_criterion_eq
    (dependencies : PoincareProofDependencies.{u}) (witness : Type u)
    (criterion : CompletionCriterionAtUniverse witness) :
    completion_criterion_of_completion_certificate witness
      (completion_certificate_of_poincareProofDependencies_and_completion_criterion
        dependencies witness criterion) =
      criterion := by
  apply Subsingleton.elim

/--
The aggregate proof dependency plus criterion certificate equivalence is the
pair of the named certificate projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_and_completion_criterion_eq
    (witness : Type u) :
    poincareCompletionCertificate_iff_poincareProofDependencies_and_completion_criterion
      witness =
      (by
        constructor
        · intro certificate
          exact ⟨poincareProofDependencies_of_completion_certificate certificate,
            completion_criterion_of_completion_certificate witness certificate⟩
        · rintro ⟨dependencies, criterion⟩
          exact completion_certificate_of_poincareProofDependencies_and_completion_criterion
            dependencies witness criterion) := by
  apply Subsingleton.elim

/--
A completion certificate exposes the full artifact payload with the aggregate
proof dependency package named directly.
-/
theorem poincareCompletionCertificate_aggregate_dependency_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ theoremName : String,
      theoremName = "poincare_conjecture" ∧
      PoincareProofDependencies.{u} ∧
      canonicalCompletionTarget.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases certificate with
    ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
  exact ⟨theoremName, theoremName_eq.trans canonicalCompletionTheoremName_eq,
    remainingDependencyPackage_iff_poincareProofDependencies.mp dependencies,
    target, criterion⟩

/--
The aggregate-dependency artifact payload is selected from the checked
certificate record and the remaining/aggregate dependency equivalence.
-/
theorem poincareCompletionCertificate_aggregate_dependency_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_aggregate_dependency_payload certificate =
      (by
        rcases certificate with
          ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
        exact
          ⟨theoremName,
            theoremName_eq.trans canonicalCompletionTheoremName_eq,
            remainingDependencyPackage_iff_poincareProofDependencies.mp
              dependencies,
            target, criterion⟩) := by
  apply Subsingleton.elim

/--
The aggregate-dependency full artifact payload reconstructs the checked
completion certificate.
-/
theorem completion_certificate_of_aggregate_dependency_payload
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
  exact ⟨theoremName, theoremName_eq.trans canonicalCompletionTheoremName_eq.symm,
    remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies,
    target, criterion⟩

/--
The aggregate-dependency payload constructor rewrites the reserved name and
the aggregate dependency package back to the checked certificate record.
-/
theorem completion_certificate_of_aggregate_dependency_payload_eq
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_certificate_of_aggregate_dependency_payload payload =
      (by
        rcases payload with
          ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
        exact
          ⟨theoremName,
            theoremName_eq.trans canonicalCompletionTheoremName_eq.symm,
            remainingDependencyPackage_iff_poincareProofDependencies.mpr
              dependencies,
            target, criterion⟩) := by
  apply Subsingleton.elim

/--
Projecting the aggregate dependency payload from the aggregate-payload
certificate constructor recovers the supplied payload.
-/
theorem poincareCompletionCertificate_aggregate_dependency_payload_of_completion_certificate_of_aggregate_dependency_payload_eq
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    poincareCompletionCertificate_aggregate_dependency_payload
      (completion_certificate_of_aggregate_dependency_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to the full artifact payload
whose dependency field is the aggregate proof dependency package.
-/
theorem poincareCompletionCertificate_iff_aggregate_dependency_payload :
    PoincareCompletionCertificate.{u} ↔
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        canonicalCompletionTarget.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨poincareCompletionCertificate_aggregate_dependency_payload,
    completion_certificate_of_aggregate_dependency_payload⟩

/--
The aggregate-dependency payload equivalence is the pair of the named
aggregate payload projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_aggregate_dependency_payload_eq :
    poincareCompletionCertificate_iff_aggregate_dependency_payload =
      ⟨poincareCompletionCertificate_aggregate_dependency_payload,
        completion_certificate_of_aggregate_dependency_payload⟩ := by
  apply Subsingleton.elim

/--
A completion certificate exposes the full artifact payload with the project
Poincare statement named directly.
-/
theorem poincareCompletionCertificate_project_statement_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ theoremName : String,
      theoremName = "poincare_conjecture" ∧
      PoincareProofDependencies.{u} ∧
      PoincareConjectureStatement.{u} ∧
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases certificate with
    ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
  exact ⟨theoremName, theoremName_eq.trans canonicalCompletionTheoremName_eq,
    remainingDependencyPackage_iff_poincareProofDependencies.mp dependencies,
    target, criterion⟩

/--
The project-statement artifact payload is selected from the checked certificate
record and the remaining/aggregate dependency equivalence.
-/
theorem poincareCompletionCertificate_project_statement_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_project_statement_payload certificate =
      (by
        rcases certificate with
          ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
        exact
          ⟨theoremName,
            theoremName_eq.trans canonicalCompletionTheoremName_eq,
            remainingDependencyPackage_iff_poincareProofDependencies.mp
              dependencies,
            target, criterion⟩) := by
  apply Subsingleton.elim

/--
The project-statement full artifact payload reconstructs the checked completion
certificate.
-/
theorem completion_certificate_of_project_statement_payload
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        PoincareConjectureStatement.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
  exact ⟨theoremName, theoremName_eq.trans canonicalCompletionTheoremName_eq.symm,
    remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies,
    target, criterion⟩

/--
The project-statement payload constructor rewrites the reserved name and the
aggregate dependency package back to the checked certificate record.
-/
theorem completion_certificate_of_project_statement_payload_eq
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        PoincareConjectureStatement.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completion_certificate_of_project_statement_payload payload =
      (by
        rcases payload with
          ⟨theoremName, theoremName_eq, dependencies, target, criterion⟩
        exact
          ⟨theoremName,
            theoremName_eq.trans canonicalCompletionTheoremName_eq.symm,
            remainingDependencyPackage_iff_poincareProofDependencies.mpr
              dependencies,
            target, criterion⟩) := by
  apply Subsingleton.elim

/--
Projecting the project-statement payload from the project-payload certificate
constructor recovers the supplied payload.
-/
theorem poincareCompletionCertificate_project_statement_payload_of_completion_certificate_of_project_statement_payload_eq
    (payload :
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        PoincareConjectureStatement.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    poincareCompletionCertificate_project_statement_payload
      (completion_certificate_of_project_statement_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The checked completion certificate is equivalent to the full artifact payload
whose target field is the project Poincare statement.
-/
theorem poincareCompletionCertificate_iff_project_statement_payload :
    PoincareCompletionCertificate.{u} ↔
      ∃ theoremName : String,
        theoremName = "poincare_conjecture" ∧
        PoincareProofDependencies.{u} ∧
        PoincareConjectureStatement.{u} ∧
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨poincareCompletionCertificate_project_statement_payload,
    completion_certificate_of_project_statement_payload⟩

/--
The project-statement payload equivalence is the pair of the named project
payload projection and named constructor.
-/
theorem poincareCompletionCertificate_iff_project_statement_payload_eq :
    poincareCompletionCertificate_iff_project_statement_payload =
      ⟨poincareCompletionCertificate_project_statement_payload,
        completion_certificate_of_project_statement_payload⟩ := by
  apply Subsingleton.elim

/--
The completion certificate is equivalent to the three component inputs in the
aggregate dependency package.
-/
theorem poincareCompletionCertificate_iff_components :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u} :=
  poincareCompletionCertificate_iff_remainingDependencyPackage.trans
    remainingDependencyPackage_iff_components

/--
The raw-component certificate equivalence is the remaining-dependency
certificate equivalence followed by the remaining-dependency component
presentation.
-/
theorem poincareCompletionCertificate_iff_components_eq :
    poincareCompletionCertificate_iff_components =
      poincareCompletionCertificate_iff_remainingDependencyPackage.trans
        remainingDependencyPackage_iff_components := by
  apply Subsingleton.elim

/--
The completion certificate is equivalent to the three component-slot
requirements named by the dependency crosswalk.
-/
theorem poincareCompletionCertificate_iff_component_requirements :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent :=
  poincareCompletionCertificate_iff_remainingDependencyPackage.trans
    remainingDependencyPackage_iff_component_requirements

/--
The component-slot certificate equivalence is the remaining-dependency
certificate equivalence followed by the remaining-dependency component-slot
presentation.
-/
theorem poincareCompletionCertificate_iff_component_requirements_eq :
    poincareCompletionCertificate_iff_component_requirements =
      poincareCompletionCertificate_iff_remainingDependencyPackage.trans
        remainingDependencyPackage_iff_component_requirements := by
  apply Subsingleton.elim

/--
The completion certificate is equivalent to the five package-layer requirements
named by the dependency crosswalk.
-/
theorem poincareCompletionCertificate_iff_package_layer_requirements :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage :=
  poincareCompletionCertificate_iff_remainingDependencyPackage.trans
    remainingDependencyPackage_iff_package_layer_requirements

/--
The package-layer certificate equivalence is the remaining-dependency
certificate equivalence followed by the remaining-dependency package-layer
presentation.
-/
theorem poincareCompletionCertificate_iff_package_layer_requirements_eq :
    poincareCompletionCertificate_iff_package_layer_requirements =
      poincareCompletionCertificate_iff_remainingDependencyPackage.trans
        remainingDependencyPackage_iff_package_layer_requirements := by
  apply Subsingleton.elim

/--
The completion certificate is equivalent to all six milestone requirements
named by the dependency crosswalk.
-/
theorem poincareCompletionCertificate_iff_milestone_requirements :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism :=
  poincareCompletionCertificate_iff_remainingDependencyPackage.trans
    remainingDependencyPackage_iff_milestone_requirements

/--
The milestone certificate equivalence is the remaining-dependency certificate
equivalence followed by the remaining-dependency milestone presentation.
-/
theorem poincareCompletionCertificate_iff_milestone_requirements_eq :
    poincareCompletionCertificate_iff_milestone_requirements =
      poincareCompletionCertificate_iff_remainingDependencyPackage.trans
        remainingDependencyPackage_iff_milestone_requirements := by
  apply Subsingleton.elim

/--
A completion certificate exposes the three raw aggregate components represented
by the remaining dependency package.
-/
theorem poincareCompletionCertificate_components_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ _smoothability : SmoothabilityPackage.{u},
    ∃ _surgery :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
      ExtinctionTopologyExtractionPackage.{u} :=
  poincareCompletionCertificate_iff_components.mp certificate

/--
The raw-component certificate payload projection is the forward direction of
the named raw-component certificate equivalence.
-/
theorem poincareCompletionCertificate_components_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_components_payload certificate =
      poincareCompletionCertificate_iff_components.mp certificate := by
  apply Subsingleton.elim

/--
The raw-component certificate payload is the remaining-dependency component
payload projected from the certificate.
-/
theorem poincareCompletionCertificate_components_payload_to_remaining_dependency_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_components_payload certificate =
      remainingDependencyPackage_components_payload
        (remaining_dependency_package_of_completion_certificate
          certificate) := by
  apply Subsingleton.elim

/--
The raw-component certificate payload is the tuple of stored fields from the
certificate's remaining-dependency package.
-/
theorem poincareCompletionCertificate_components_payload_to_fields_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_components_payload certificate =
      ⟨ (remaining_dependency_package_of_completion_certificate
            certificate).smoothability
      , (remaining_dependency_package_of_completion_certificate
            certificate).surgery
      , (remaining_dependency_package_of_completion_certificate
            certificate).topology
      ⟩ := by
  apply Subsingleton.elim

/--
A completion certificate exposes the three component-slot requirements named by
the dependency crosswalk.
-/
theorem poincareCompletionCertificate_component_requirements_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ _smoothability :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent :=
  poincareCompletionCertificate_iff_component_requirements.mp certificate

/--
The component-slot certificate payload projection is the forward direction of
the named component-slot certificate equivalence.
-/
theorem poincareCompletionCertificate_component_requirements_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_component_requirements_payload certificate =
      poincareCompletionCertificate_iff_component_requirements.mp
        certificate := by
  apply Subsingleton.elim

/--
The component-slot certificate payload is the remaining-dependency component
payload projected from the certificate.
-/
theorem poincareCompletionCertificate_component_requirements_payload_to_remaining_dependency_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_component_requirements_payload certificate =
      remainingDependencyPackage_component_requirements_payload
        (remaining_dependency_package_of_completion_certificate
          certificate) := by
  apply Subsingleton.elim

/--
The component-slot certificate payload is also the tuple of named component
projections from the certificate's remaining-dependency package.
-/
theorem poincareCompletionCertificate_component_requirements_payload_to_named_projections_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_component_requirements_payload certificate =
      ⟨ smoothabilityComponent_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      , surgeryComponent_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      , topologyComponent_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      ⟩ := by
  apply Subsingleton.elim

/--
A completion certificate exposes the five package-layer requirements named by
the dependency crosswalk.
-/
theorem poincareCompletionCertificate_package_layer_requirements_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage :=
  poincareCompletionCertificate_iff_package_layer_requirements.mp certificate

/--
The package-layer certificate payload projection is the forward direction of
the named package-layer certificate equivalence.
-/
theorem poincareCompletionCertificate_package_layer_requirements_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_package_layer_requirements_payload
      certificate =
      poincareCompletionCertificate_iff_package_layer_requirements.mp
        certificate := by
  apply Subsingleton.elim

/--
The package-layer certificate payload is the remaining-dependency package-layer
payload projected from the certificate.
-/
theorem poincareCompletionCertificate_package_layer_requirements_payload_to_remaining_dependency_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_package_layer_requirements_payload
      certificate =
      remainingDependencyPackage_package_layer_requirements_payload
        (remaining_dependency_package_of_completion_certificate
          certificate) := by
  apply Subsingleton.elim

/--
The package-layer certificate payload is also the tuple of generic
package-layer projections from the certificate's remaining-dependency package.
-/
theorem poincareCompletionCertificate_package_layer_requirements_payload_to_generic_projections_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_package_layer_requirements_payload
      certificate =
      ⟨ dependencyPackageLayerRequirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
          DependencyPackageLayer.smoothabilityPackage
      , dependencyPackageLayerRequirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
          DependencyPackageLayer.analyticFoundationPackage
      , dependencyPackageLayerRequirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
          DependencyPackageLayer.surgeryPackage
      , dependencyPackageLayerRequirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
          DependencyPackageLayer.finiteExtinctionPackage
      , dependencyPackageLayerRequirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
          DependencyPackageLayer.topologyPackage
      ⟩ := by
  apply Subsingleton.elim

/--
A completion certificate exposes all six milestone requirements named by the
dependency crosswalk.
-/
theorem poincareCompletionCertificate_milestone_requirements_payload
    (certificate : PoincareCompletionCertificate.{u}) :
    ∃ _smoothabilityBridge :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
    ∃ _ricciFlowAnalyticFoundation :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation,
    ∃ _ricciFlowWithSurgery :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
    ∃ _perelmanSingularityControl :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl,
    ∃ _finiteExtinction :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism :=
  poincareCompletionCertificate_iff_milestone_requirements.mp certificate

/--
The milestone certificate payload projection is the forward direction of the
named milestone certificate equivalence.
-/
theorem poincareCompletionCertificate_milestone_requirements_payload_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_milestone_requirements_payload certificate =
      poincareCompletionCertificate_iff_milestone_requirements.mp
        certificate := by
  apply Subsingleton.elim

/--
The milestone certificate payload is the remaining-dependency milestone payload
projected from the certificate.
-/
theorem poincareCompletionCertificate_milestone_requirements_payload_to_remaining_dependency_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_milestone_requirements_payload certificate =
      remainingDependencyPackage_milestone_requirements_payload
        (remaining_dependency_package_of_completion_certificate
          certificate) := by
  apply Subsingleton.elim

/--
The milestone certificate payload is also the tuple of package-layer
projections assigned to the six ledger milestones for the certificate's
remaining-dependency package.
-/
theorem poincareCompletionCertificate_milestone_requirements_payload_to_package_layer_projections_eq
    (certificate : PoincareCompletionCertificate.{u}) :
    poincareCompletionCertificate_milestone_requirements_payload certificate =
      ⟨ smoothabilityPackage_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      , analyticFoundationPackage_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      , surgeryPackage_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      , surgeryPackage_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      , finiteExtinctionPackage_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      , topologyPackage_requirement_of_dependencies
          (remaining_dependency_package_of_completion_certificate certificate)
      ⟩ := by
  apply Subsingleton.elim

/--
The three raw aggregate components produce the checked completion certificate.
-/
theorem completion_certificate_of_components
    (smoothability : SmoothabilityPackage.{u})
    (surgery :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topology : ExtinctionTopologyExtractionPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  poincareCompletionCertificate_iff_components.mpr
    ⟨smoothability, surgery, topology⟩

/--
The raw-component certificate constructor is the reverse direction of the named
raw-component certificate equivalence.
-/
theorem completion_certificate_of_components_eq
    (smoothability : SmoothabilityPackage.{u})
    (surgery :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topology : ExtinctionTopologyExtractionPackage.{u}) :
    completion_certificate_of_components smoothability surgery topology =
      poincareCompletionCertificate_iff_components.mpr
        ⟨smoothability, surgery, topology⟩ := by
  apply Subsingleton.elim

/--
The raw-component certificate constructor is the remaining-dependency
certificate constructor applied to the corresponding component package.
-/
theorem completion_certificate_of_components_to_remaining_dependency_eq
    (smoothability : SmoothabilityPackage.{u})
    (surgery :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topology : ExtinctionTopologyExtractionPackage.{u}) :
    completion_certificate_of_components smoothability surgery topology =
      completion_certificate_of_remaining_dependency_package
        ⟨smoothability, surgery, topology⟩ := by
  apply Subsingleton.elim

/--
Projecting the raw-component payload from the certificate built out of raw
components returns the original raw-component payload.
-/
theorem poincareCompletionCertificate_components_payload_of_completion_certificate_of_components_eq
    (smoothability : SmoothabilityPackage.{u})
    (surgery :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M))
    (topology : ExtinctionTopologyExtractionPackage.{u}) :
    poincareCompletionCertificate_components_payload
      (completion_certificate_of_components smoothability surgery topology) =
      ⟨smoothability, surgery, topology⟩ := by
  apply Subsingleton.elim

/--
The three dependency component-slot requirements produce the checked
completion certificate.
-/
theorem completion_certificate_of_component_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    PoincareCompletionCertificate.{u} :=
  poincareCompletionCertificate_iff_component_requirements.mpr
    ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩

/--
The component-slot certificate constructor is the reverse direction of the
named component-slot certificate equivalence.
-/
theorem completion_certificate_of_component_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      poincareCompletionCertificate_iff_component_requirements.mpr
        ⟨smoothabilityRequirement, surgeryRequirement,
          topologyRequirement⟩ := by
  apply Subsingleton.elim

/--
The component-slot certificate constructor is the remaining-dependency
certificate constructor applied to the package reconstructed from the slots.
-/
theorem completion_certificate_of_component_requirements_to_remaining_dependency_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_iff_component_requirements.mpr
          ⟨smoothabilityRequirement, surgeryRequirement,
            topologyRequirement⟩) := by
  apply Subsingleton.elim

/--
Projecting the component-slot payload from the certificate built out of
component-slot requirements returns the original component-slot payload.
-/
theorem poincareCompletionCertificate_component_requirements_payload_of_completion_certificate_of_component_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    poincareCompletionCertificate_component_requirements_payload
      (completion_certificate_of_component_requirements
        smoothabilityRequirement surgeryRequirement topologyRequirement) =
      ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩ := by
  apply Subsingleton.elim

/--
The five dependency package-layer requirements produce the checked completion
certificate.
-/
theorem completion_certificate_of_package_layer_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    PoincareCompletionCertificate.{u} :=
  poincareCompletionCertificate_iff_package_layer_requirements.mpr
    ⟨smoothabilityRequirement, analyticRequirement, surgeryRequirement,
      finiteExtinctionRequirement, topologyRequirement⟩

/--
The package-layer certificate constructor is the reverse direction of the named
package-layer certificate equivalence.
-/
theorem completion_certificate_of_package_layer_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      poincareCompletionCertificate_iff_package_layer_requirements.mpr
        ⟨smoothabilityRequirement, analyticRequirement, surgeryRequirement,
          finiteExtinctionRequirement, topologyRequirement⟩ := by
  apply Subsingleton.elim

/--
The package-layer certificate constructor is the remaining-dependency
certificate constructor applied to the package reconstructed from the layers.
-/
theorem completion_certificate_of_package_layer_requirements_to_remaining_dependency_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_iff_package_layer_requirements.mpr
          ⟨smoothabilityRequirement, analyticRequirement, surgeryRequirement,
            finiteExtinctionRequirement, topologyRequirement⟩) := by
  apply Subsingleton.elim

/--
Projecting the package-layer payload from the certificate built out of
package-layer requirements returns the original package-layer payload.
-/
theorem poincareCompletionCertificate_package_layer_requirements_payload_of_completion_certificate_of_package_layer_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    poincareCompletionCertificate_package_layer_requirements_payload
      (completion_certificate_of_package_layer_requirements
        smoothabilityRequirement analyticRequirement surgeryRequirement
        finiteExtinctionRequirement topologyRequirement) =
      ⟨smoothabilityRequirement, analyticRequirement, surgeryRequirement,
        finiteExtinctionRequirement, topologyRequirement⟩ := by
  apply Subsingleton.elim

/--
The six dependency milestone requirements produce the checked completion
certificate.
-/
theorem completion_certificate_of_milestone_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    PoincareCompletionCertificate.{u} :=
  poincareCompletionCertificate_iff_milestone_requirements.mpr
    ⟨smoothabilityBridgeRequirement, ricciFlowAnalyticFoundationRequirement,
      ricciFlowWithSurgeryRequirement, perelmanSingularityControlRequirement,
      finiteExtinctionRequirement, extinctionToSphereHomeomorphismRequirement⟩

/--
The milestone certificate constructor is the reverse direction of the named
milestone certificate equivalence.
-/
theorem completion_certificate_of_milestone_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      poincareCompletionCertificate_iff_milestone_requirements.mpr
        ⟨smoothabilityBridgeRequirement, ricciFlowAnalyticFoundationRequirement,
          ricciFlowWithSurgeryRequirement, perelmanSingularityControlRequirement,
          finiteExtinctionRequirement,
          extinctionToSphereHomeomorphismRequirement⟩ := by
  apply Subsingleton.elim

/--
The milestone certificate constructor is the remaining-dependency certificate
constructor applied to the package reconstructed from the milestone payload.
-/
theorem completion_certificate_of_milestone_requirements_to_remaining_dependency_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_iff_milestone_requirements.mpr
          ⟨smoothabilityBridgeRequirement, ricciFlowAnalyticFoundationRequirement,
            ricciFlowWithSurgeryRequirement, perelmanSingularityControlRequirement,
            finiteExtinctionRequirement,
            extinctionToSphereHomeomorphismRequirement⟩) := by
  apply Subsingleton.elim

/--
Projecting the milestone payload from the certificate built out of milestone
requirements returns the original milestone payload.
-/
theorem poincareCompletionCertificate_milestone_requirements_payload_of_completion_certificate_of_milestone_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    poincareCompletionCertificate_milestone_requirements_payload
      (completion_certificate_of_milestone_requirements
        smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
        ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
        finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement) =
      ⟨smoothabilityBridgeRequirement, ricciFlowAnalyticFoundationRequirement,
        ricciFlowWithSurgeryRequirement, perelmanSingularityControlRequirement,
        finiteExtinctionRequirement,
        extinctionToSphereHomeomorphismRequirement⟩ := by
  apply Subsingleton.elim

/--
The raw aggregate component payload reconstructs the checked completion
certificate.
-/
theorem completion_certificate_of_components_payload
    (payload :
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u}) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with ⟨smoothability, surgery, topology⟩
  exact completion_certificate_of_components smoothability surgery topology

/--
The raw-component payload constructor destructures the named payload and
delegates to the raw-component certificate constructor.
-/
theorem completion_certificate_of_components_payload_eq
    (payload :
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u}) :
    completion_certificate_of_components_payload payload =
      (by
        rcases payload with ⟨smoothability, surgery, topology⟩
        exact completion_certificate_of_components
          smoothability surgery topology) := by
  apply Subsingleton.elim

/--
The raw-component payload certificate constructor is the remaining-dependency
certificate constructor applied to the package reconstructed from the payload.
-/
theorem completion_certificate_of_components_payload_to_remaining_dependency_eq
    (payload :
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u}) :
    completion_certificate_of_components_payload payload =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_iff_components.mpr payload) := by
  apply Subsingleton.elim

/--
Projecting the raw-component payload from a certificate reconstructed from a
raw-component payload returns that payload.
-/
theorem poincareCompletionCertificate_components_payload_of_completion_certificate_of_components_payload_eq
    (payload :
      ∃ _smoothability : SmoothabilityPackage.{u},
      ∃ _surgery :
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
        ExtinctionTopologyExtractionPackage.{u}) :
    poincareCompletionCertificate_components_payload
      (completion_certificate_of_components_payload payload) = payload := by
  apply Subsingleton.elim

/--
The component-slot requirement payload reconstructs the checked completion
certificate.
-/
theorem completion_certificate_of_component_requirements_payload
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩
  exact completion_certificate_of_component_requirements
    smoothabilityRequirement surgeryRequirement topologyRequirement

/--
The component-slot payload constructor destructures the named payload and
delegates to the component-slot certificate constructor.
-/
theorem completion_certificate_of_component_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_requirements_payload payload =
      (by
        rcases payload with
          ⟨smoothabilityRequirement, surgeryRequirement,
            topologyRequirement⟩
        exact completion_certificate_of_component_requirements
          smoothabilityRequirement surgeryRequirement
          topologyRequirement) := by
  apply Subsingleton.elim

/--
The component-slot payload certificate constructor is the remaining-dependency
certificate constructor applied to the package reconstructed from the payload.
-/
theorem completion_certificate_of_component_requirements_payload_to_remaining_dependency_eq
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_requirements_payload payload =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_iff_component_requirements.mpr
          payload) := by
  apply Subsingleton.elim

/--
Projecting the component-slot payload from a certificate reconstructed from a
component-slot payload returns that payload.
-/
theorem poincareCompletionCertificate_component_requirements_payload_of_completion_certificate_of_component_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    poincareCompletionCertificate_component_requirements_payload
      (completion_certificate_of_component_requirements_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The package-layer requirement payload reconstructs the checked completion
certificate.
-/
theorem completion_certificate_of_package_layer_requirements_payload
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨ smoothabilityRequirement
    , analyticRequirement
    , surgeryRequirement
    , finiteExtinctionRequirement
    , topologyRequirement
    ⟩
  exact completion_certificate_of_package_layer_requirements
    smoothabilityRequirement analyticRequirement surgeryRequirement
    finiteExtinctionRequirement topologyRequirement

/--
The package-layer payload constructor destructures the named payload and
delegates to the package-layer certificate constructor.
-/
theorem completion_certificate_of_package_layer_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_requirements_payload payload =
      (by
        rcases payload with
          ⟨ smoothabilityRequirement
          , analyticRequirement
          , surgeryRequirement
          , finiteExtinctionRequirement
          , topologyRequirement
          ⟩
        exact completion_certificate_of_package_layer_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The package-layer payload certificate constructor is the remaining-dependency
certificate constructor applied to the package reconstructed from the payload.
-/
theorem completion_certificate_of_package_layer_requirements_payload_to_remaining_dependency_eq
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_requirements_payload payload =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_iff_package_layer_requirements.mpr
          payload) := by
  apply Subsingleton.elim

/--
Projecting the package-layer payload from a certificate reconstructed from a
package-layer payload returns that payload.
-/
theorem poincareCompletionCertificate_package_layer_requirements_payload_of_completion_certificate_of_package_layer_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    poincareCompletionCertificate_package_layer_requirements_payload
      (completion_certificate_of_package_layer_requirements_payload
        payload) = payload := by
  apply Subsingleton.elim

/--
The milestone-requirement payload reconstructs the checked completion
certificate.
-/
theorem completion_certificate_of_milestone_requirements_payload
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨ smoothabilityBridgeRequirement
    , ricciFlowAnalyticFoundationRequirement
    , ricciFlowWithSurgeryRequirement
    , perelmanSingularityControlRequirement
    , finiteExtinctionRequirement
    , extinctionToSphereHomeomorphismRequirement
    ⟩
  exact completion_certificate_of_milestone_requirements
    smoothabilityBridgeRequirement
    ricciFlowAnalyticFoundationRequirement
    ricciFlowWithSurgeryRequirement
    perelmanSingularityControlRequirement
    finiteExtinctionRequirement
    extinctionToSphereHomeomorphismRequirement

/--
The milestone payload constructor destructures the named payload and delegates
to the milestone certificate constructor.
-/
theorem completion_certificate_of_milestone_requirements_payload_eq
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_requirements_payload payload =
      (by
        rcases payload with
          ⟨ smoothabilityBridgeRequirement
          , ricciFlowAnalyticFoundationRequirement
          , ricciFlowWithSurgeryRequirement
          , perelmanSingularityControlRequirement
          , finiteExtinctionRequirement
          , extinctionToSphereHomeomorphismRequirement
          ⟩
        exact completion_certificate_of_milestone_requirements
          smoothabilityBridgeRequirement
          ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement
          perelmanSingularityControlRequirement
          finiteExtinctionRequirement
          extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The milestone payload certificate constructor is the remaining-dependency
certificate constructor applied to the package reconstructed from the payload.
-/
theorem completion_certificate_of_milestone_requirements_payload_to_remaining_dependency_eq
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_requirements_payload payload =
      completion_certificate_of_remaining_dependency_package
        (remainingDependencyPackage_iff_milestone_requirements.mpr payload) := by
  apply Subsingleton.elim

/--
Projecting the milestone payload from a certificate reconstructed from a
milestone payload returns that payload.
-/
theorem poincareCompletionCertificate_milestone_requirements_payload_of_completion_certificate_of_milestone_requirements_payload_eq
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    poincareCompletionCertificate_milestone_requirements_payload
      (completion_certificate_of_milestone_requirements_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The certified component-slot requirement route produces the checked completion
certificate.
-/
theorem completion_certificate_of_component_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    (remainingDependencyPackage_iff_component_requirements.mpr
      ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩)
    (canonical_completion_payload_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement)

/--
The certified component-slot requirement payload reconstructs the checked
completion certificate through the extraction-derivation route.
-/
theorem completion_certificate_of_component_extraction_derivation_requirements_payload
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩
  exact completion_certificate_of_component_extraction_derivation_requirements
    smoothabilityRequirement surgeryRequirement topologyRequirement

/--
The completion certificate is equivalent to the three component-slot
requirements when reconstructed through the certified extraction-derivation
route.
-/
theorem poincareCompletionCertificate_iff_component_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent := by
  constructor
  · intro certificate
    exact poincareCompletionCertificate_iff_component_requirements.mp certificate
  · intro payload
    exact
      completion_certificate_of_component_extraction_derivation_requirements_payload
        payload

/--
The certified package-layer requirement route produces the checked completion
certificate.
-/
theorem completion_certificate_of_package_layer_extraction_derivation_requirements
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    (remainingDependencyPackage_iff_package_layer_requirements.mpr
      ⟨smoothabilityRequirement, analyticRequirement, surgeryRequirement,
        finiteExtinctionRequirement, topologyRequirement⟩)
    (canonical_completion_payload_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement)

/--
The certified package-layer requirement payload reconstructs the checked
completion certificate through the extraction-derivation route.
-/
theorem completion_certificate_of_package_layer_extraction_derivation_requirements_payload
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨ smoothabilityRequirement
    , analyticRequirement
    , surgeryRequirement
    , finiteExtinctionRequirement
    , topologyRequirement
    ⟩
  exact completion_certificate_of_package_layer_extraction_derivation_requirements
    smoothabilityRequirement analyticRequirement surgeryRequirement
    finiteExtinctionRequirement topologyRequirement

/--
The completion certificate is equivalent to the five package-layer requirements
when reconstructed through the certified extraction-derivation route.
-/
theorem poincareCompletionCertificate_iff_package_layer_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · intro certificate
    exact poincareCompletionCertificate_iff_package_layer_requirements.mp
      certificate
  · intro payload
    exact
      completion_certificate_of_package_layer_extraction_derivation_requirements_payload
        payload

/--
The certified milestone-requirement route produces the checked completion
certificate.
-/
theorem completion_certificate_of_milestone_extraction_derivation_requirements
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    (remainingDependencyPackage_iff_milestone_requirements.mpr
      ⟨smoothabilityBridgeRequirement, ricciFlowAnalyticFoundationRequirement,
        ricciFlowWithSurgeryRequirement, perelmanSingularityControlRequirement,
        finiteExtinctionRequirement, extinctionToSphereHomeomorphismRequirement⟩)
    (canonical_completion_payload_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement
      perelmanSingularityControlRequirement
      finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement)

/--
The certified milestone-requirement payload reconstructs the checked completion
certificate through the extraction-derivation route.
-/
theorem completion_certificate_of_milestone_extraction_derivation_requirements_payload
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    PoincareCompletionCertificate.{u} := by
  rcases payload with
    ⟨ smoothabilityBridgeRequirement
    , ricciFlowAnalyticFoundationRequirement
    , ricciFlowWithSurgeryRequirement
    , perelmanSingularityControlRequirement
    , finiteExtinctionRequirement
    , extinctionToSphereHomeomorphismRequirement
    ⟩
  exact completion_certificate_of_milestone_extraction_derivation_requirements
    smoothabilityBridgeRequirement
    ricciFlowAnalyticFoundationRequirement
    ricciFlowWithSurgeryRequirement
    perelmanSingularityControlRequirement
    finiteExtinctionRequirement
    extinctionToSphereHomeomorphismRequirement

/--
The completion certificate is equivalent to the six milestone requirements when
reconstructed through the certified extraction-derivation route.
-/
theorem poincareCompletionCertificate_iff_milestone_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism := by
  constructor
  · intro certificate
    exact poincareCompletionCertificate_iff_milestone_requirements.mp certificate
  · intro payload
    exact
      completion_certificate_of_milestone_extraction_derivation_requirements_payload
        payload

/--
The certified component-slot certificate constructor is exactly the route that
packages the named component-slot requirements and then uses the canonical
extraction-derivation payload.
-/
theorem completion_certificate_of_component_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        (remainingDependencyPackage_iff_component_requirements.mpr
          ⟨smoothabilityRequirement, surgeryRequirement, topologyRequirement⟩)
        (canonical_completion_payload_of_component_extraction_derivation_requirements
          smoothabilityRequirement surgeryRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The certified component-slot payload constructor destructures the named payload
and delegates to the certified component-slot certificate constructor.
-/
theorem completion_certificate_of_component_extraction_derivation_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_extraction_derivation_requirements_payload
      payload =
      (by
        rcases payload with
          ⟨smoothabilityRequirement, surgeryRequirement,
            topologyRequirement⟩
        exact
          completion_certificate_of_component_extraction_derivation_requirements
            smoothabilityRequirement surgeryRequirement
            topologyRequirement) := by
  apply Subsingleton.elim

/--
The certified component-slot equivalence is the raw component-slot projection
paired with the certified extraction-derivation payload constructor.
-/
theorem poincareCompletionCertificate_iff_component_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_component_extraction_derivation_requirements =
      ⟨poincareCompletionCertificate_iff_component_requirements.mp,
        completion_certificate_of_component_extraction_derivation_requirements_payload⟩ := by
  apply Subsingleton.elim

/--
The certified package-layer certificate constructor is exactly the route that
packages the named package-layer requirements and then uses the canonical
extraction-derivation payload.
-/
theorem completion_certificate_of_package_layer_extraction_derivation_requirements_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        (remainingDependencyPackage_iff_package_layer_requirements.mpr
          ⟨smoothabilityRequirement, analyticRequirement, surgeryRequirement,
            finiteExtinctionRequirement, topologyRequirement⟩)
        (canonical_completion_payload_of_package_layer_extraction_derivation_requirements
          smoothabilityRequirement analyticRequirement surgeryRequirement
          finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The certified package-layer payload constructor destructures the named payload
and delegates to the certified package-layer certificate constructor.
-/
theorem completion_certificate_of_package_layer_extraction_derivation_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_extraction_derivation_requirements_payload
      payload =
      (by
        rcases payload with
          ⟨ smoothabilityRequirement
          , analyticRequirement
          , surgeryRequirement
          , finiteExtinctionRequirement
          , topologyRequirement
          ⟩
        exact
          completion_certificate_of_package_layer_extraction_derivation_requirements
            smoothabilityRequirement analyticRequirement surgeryRequirement
            finiteExtinctionRequirement topologyRequirement) := by
  apply Subsingleton.elim

/--
The certified package-layer equivalence is the raw package-layer projection
paired with the certified extraction-derivation payload constructor.
-/
theorem poincareCompletionCertificate_iff_package_layer_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_package_layer_extraction_derivation_requirements =
      ⟨poincareCompletionCertificate_iff_package_layer_requirements.mp,
        completion_certificate_of_package_layer_extraction_derivation_requirements_payload⟩ := by
  apply Subsingleton.elim

/--
The certified milestone certificate constructor is exactly the route that
packages the named milestone requirements and then uses the canonical
extraction-derivation payload.
-/
theorem completion_certificate_of_milestone_extraction_derivation_requirements_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement
      ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement
      perelmanSingularityControlRequirement
      finiteExtinctionRequirement
      extinctionToSphereHomeomorphismRequirement =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        (remainingDependencyPackage_iff_milestone_requirements.mpr
          ⟨smoothabilityBridgeRequirement,
            ricciFlowAnalyticFoundationRequirement,
            ricciFlowWithSurgeryRequirement,
            perelmanSingularityControlRequirement,
            finiteExtinctionRequirement,
            extinctionToSphereHomeomorphismRequirement⟩)
        (canonical_completion_payload_of_milestone_extraction_derivation_requirements
          smoothabilityBridgeRequirement
          ricciFlowAnalyticFoundationRequirement
          ricciFlowWithSurgeryRequirement
          perelmanSingularityControlRequirement
          finiteExtinctionRequirement
          extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The certified milestone payload constructor destructures the named payload and
delegates to the certified milestone certificate constructor.
-/
theorem completion_certificate_of_milestone_extraction_derivation_requirements_payload_eq
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_extraction_derivation_requirements_payload
      payload =
      (by
        rcases payload with
          ⟨ smoothabilityBridgeRequirement
          , ricciFlowAnalyticFoundationRequirement
          , ricciFlowWithSurgeryRequirement
          , perelmanSingularityControlRequirement
          , finiteExtinctionRequirement
          , extinctionToSphereHomeomorphismRequirement
          ⟩
        exact
          completion_certificate_of_milestone_extraction_derivation_requirements
            smoothabilityBridgeRequirement
            ricciFlowAnalyticFoundationRequirement
            ricciFlowWithSurgeryRequirement
            perelmanSingularityControlRequirement
            finiteExtinctionRequirement
            extinctionToSphereHomeomorphismRequirement) := by
  apply Subsingleton.elim

/--
The certified milestone equivalence is the raw milestone projection paired with
the certified extraction-derivation payload constructor.
-/
theorem poincareCompletionCertificate_iff_milestone_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_milestone_extraction_derivation_requirements =
      ⟨poincareCompletionCertificate_iff_milestone_requirements.mp,
        completion_certificate_of_milestone_extraction_derivation_requirements_payload⟩ := by
  apply Subsingleton.elim

/--
The remaining dependency package produces a checked completion certificate
through the raw component-slot requirement route.
-/
theorem completion_certificate_of_remaining_dependency_component_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    dependencies
    (canonical_completion_payload_of_remaining_dependency_component_requirements
      dependencies)

/--
The completion certificate is equivalent to the remaining dependency package
through the raw component-slot requirement route.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_component_requirements :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_remaining_dependency_component_requirements⟩

/--
The remaining dependency package produces a checked completion certificate
through the raw package-layer requirement route.
-/
theorem completion_certificate_of_remaining_dependency_package_layer_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    dependencies
    (canonical_completion_payload_of_remaining_dependency_package_layer_requirements
      dependencies)

/--
The completion certificate is equivalent to the remaining dependency package
through the raw package-layer requirement route.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_package_layer_requirements :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_remaining_dependency_package_layer_requirements⟩

/--
The remaining dependency package produces a checked completion certificate
through the raw milestone-requirement route.
-/
theorem completion_certificate_of_remaining_dependency_milestone_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    dependencies
    (canonical_completion_payload_of_remaining_dependency_milestone_requirements
      dependencies)

/--
The completion certificate is equivalent to the remaining dependency package
through the raw milestone-requirement route.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_milestone_requirements :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_remaining_dependency_milestone_requirements⟩

/--
The aggregate proof dependency package produces a checked completion
certificate through the raw component-slot requirement route.
-/
theorem completion_certificate_of_poincareProofDependencies_component_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_component_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the raw component-slot requirement route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_component_requirements :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_component_requirements⟩

/--
The aggregate proof dependency package produces a checked completion
certificate through the raw package-layer requirement route.
-/
theorem completion_certificate_of_poincareProofDependencies_package_layer_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_package_layer_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the raw package-layer requirement route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_package_layer_requirements :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_package_layer_requirements⟩

/--
The aggregate proof dependency package produces a checked completion
certificate through the raw milestone-requirement route.
-/
theorem completion_certificate_of_poincareProofDependencies_milestone_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_milestone_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the raw milestone-requirement route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_milestone_requirements :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_milestone_requirements⟩

/--
The remaining dependency package produces a checked completion certificate
through the certified component-slot route.
-/
theorem completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    dependencies
    (canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies)

/--
The completion certificate is equivalent to the remaining dependency package
through the certified component-slot route.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_component_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements⟩

/--
The remaining dependency package produces a checked completion certificate
through the certified package-layer route.
-/
theorem completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    dependencies
    (canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies)

/--
The completion certificate is equivalent to the remaining dependency package
through the certified package-layer route.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_package_layer_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements⟩

/--
The remaining dependency package produces a checked completion certificate
through the certified milestone route.
-/
theorem completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_canonical_payload
    dependencies
    (canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies)

/--
The completion certificate is equivalent to the remaining dependency package
through the certified milestone route.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_milestone_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements⟩

/--
The aggregate proof dependency package produces a checked completion
certificate through the certified component-slot requirement route.
-/
theorem completion_certificate_of_poincareProofDependencies_component_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the certified component-slot requirement route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_component_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_component_extraction_derivation_requirements⟩

/--
The aggregate proof dependency package produces a checked completion
certificate through the certified package-layer requirement route.
-/
theorem completion_certificate_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the certified package-layer requirement route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_package_layer_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_package_layer_extraction_derivation_requirements⟩

/--
The aggregate proof dependency package produces a checked completion
certificate through the certified milestone-requirement route.
-/
theorem completion_certificate_of_poincareProofDependencies_milestone_extraction_derivation_requirements
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the certified milestone-requirement route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_milestone_extraction_derivation_requirements :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_milestone_extraction_derivation_requirements⟩

/--
A completed remaining-dependency package also produces a completion certificate
through the certified extraction-derivation aggregate route.
-/
theorem completion_certificate_of_aggregate_extraction_derivation_dependencies
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} := by
  rcases canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
      dependencies with
    ⟨target, criterion⟩
  exact ⟨canonicalCompletionTheoremName, rfl, dependencies, target, criterion⟩

/--
A completed remaining-dependency package produces a completion certificate
through the certified extraction-derivation projection route.
-/
theorem completion_certificate_of_extraction_derivation_dependency_projections
    (dependencies : RemainingDependencyPackage.{u}) :
    PoincareCompletionCertificate.{u} := by
  rcases canonical_completion_payload_of_extraction_derivation_dependency_projections
      dependencies with
    ⟨target, criterion⟩
  exact ⟨canonicalCompletionTheoremName, rfl, dependencies, target, criterion⟩

/--
The completion certificate is equivalent to the remaining dependency package when
the certificate is reconstructed through the certified extraction-derivation
aggregate route.
-/
theorem poincareCompletionCertificate_iff_aggregate_extraction_derivation_dependencies :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_aggregate_extraction_derivation_dependencies⟩

/--
The completion certificate is equivalent to the remaining dependency package when
the certificate is reconstructed through the certified extraction-derivation
projection route.
-/
theorem poincareCompletionCertificate_iff_extraction_derivation_dependency_projections :
    PoincareCompletionCertificate.{u} ↔ RemainingDependencyPackage.{u} :=
  ⟨remaining_dependency_package_of_completion_certificate,
    completion_certificate_of_extraction_derivation_dependency_projections⟩

/--
The aggregate proof dependency package produces the checked completion
certificate through the certified extraction-derivation aggregate route.
-/
theorem completion_certificate_of_poincareProofDependencies_aggregate_extraction_derivation
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_aggregate_extraction_derivation_dependencies
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the certified extraction-derivation aggregate route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_aggregate_extraction_derivation :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_aggregate_extraction_derivation⟩

/--
The aggregate proof dependency package produces the checked completion
certificate through the certified extraction-derivation projection route.
-/
theorem completion_certificate_of_poincareProofDependencies_extraction_derivation_projections
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_extraction_derivation_dependency_projections
    (remainingDependencyPackage_iff_poincareProofDependencies.mpr dependencies)

/--
The completion certificate is equivalent to the aggregate proof dependency
package through the certified extraction-derivation projection route.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_extraction_derivation_projections :
    PoincareCompletionCertificate.{u} ↔ PoincareProofDependencies.{u} :=
  ⟨poincareProofDependencies_of_completion_certificate,
    completion_certificate_of_poincareProofDependencies_extraction_derivation_projections⟩

/--
The remaining-dependency raw component certificate constructor is exactly the
canonical-payload certificate route for the component-slot requirements.
-/
theorem completion_certificate_of_remaining_dependency_component_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_remaining_dependency_component_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies
        (canonical_completion_payload_of_remaining_dependency_component_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency raw component equivalence is the certificate
projection paired with the component-slot certificate constructor.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_component_requirements_eq :
    poincareCompletionCertificate_iff_remaining_dependency_component_requirements =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_remaining_dependency_component_requirements⟩ := by
  apply Subsingleton.elim

/--
The remaining-dependency raw package-layer certificate constructor is exactly
the canonical-payload certificate route for the package-layer requirements.
-/
theorem completion_certificate_of_remaining_dependency_package_layer_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_remaining_dependency_package_layer_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies
        (canonical_completion_payload_of_remaining_dependency_package_layer_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency raw package-layer equivalence is the certificate
projection paired with the package-layer certificate constructor.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_package_layer_requirements_eq :
    poincareCompletionCertificate_iff_remaining_dependency_package_layer_requirements =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_remaining_dependency_package_layer_requirements⟩ := by
  apply Subsingleton.elim

/--
The remaining-dependency raw milestone certificate constructor is exactly the
canonical-payload certificate route for the milestone requirements.
-/
theorem completion_certificate_of_remaining_dependency_milestone_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_remaining_dependency_milestone_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies
        (canonical_completion_payload_of_remaining_dependency_milestone_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency raw milestone equivalence is the certificate
projection paired with the milestone certificate constructor.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_milestone_requirements_eq :
    poincareCompletionCertificate_iff_remaining_dependency_milestone_requirements =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_remaining_dependency_milestone_requirements⟩ := by
  apply Subsingleton.elim

/--
The aggregate raw component certificate constructor is exactly the
remaining-dependency component constructor after converting aggregate
dependencies to the remaining-dependency package.
-/
theorem completion_certificate_of_poincareProofDependencies_component_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_component_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_component_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate raw component equivalence is the aggregate dependency projection
paired with the aggregate component certificate constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_component_requirements_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_component_requirements =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_component_requirements⟩ := by
  apply Subsingleton.elim

/--
The aggregate raw package-layer certificate constructor is exactly the
remaining-dependency package-layer constructor after converting aggregate
dependencies to the remaining-dependency package.
-/
theorem completion_certificate_of_poincareProofDependencies_package_layer_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_package_layer_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_package_layer_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate raw package-layer equivalence is the aggregate dependency
projection paired with the aggregate package-layer certificate constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_package_layer_requirements_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_package_layer_requirements =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_package_layer_requirements⟩ := by
  apply Subsingleton.elim

/--
The aggregate raw milestone certificate constructor is exactly the
remaining-dependency milestone constructor after converting aggregate
dependencies to the remaining-dependency package.
-/
theorem completion_certificate_of_poincareProofDependencies_milestone_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_milestone_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_milestone_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate raw milestone equivalence is the aggregate dependency projection
paired with the aggregate milestone certificate constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_milestone_requirements_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_milestone_requirements =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_milestone_requirements⟩ := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component certificate constructor is exactly
the canonical-payload certificate route for the certified component-slot
requirements.
-/
theorem completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies
        (canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified component equivalence is the certificate
projection paired with the certified component certificate constructor.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_component_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_remaining_dependency_component_extraction_derivation_requirements =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements⟩ := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer certificate constructor is
exactly the canonical-payload certificate route for the certified package-layer
requirements.
-/
theorem completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies
        (canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified package-layer equivalence is the certificate
projection paired with the certified package-layer certificate constructor.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_package_layer_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_remaining_dependency_package_layer_extraction_derivation_requirements =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements⟩ := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone certificate constructor is exactly
the canonical-payload certificate route for the certified milestone
requirements.
-/
theorem completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_and_canonical_payload
        dependencies
        (canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements
          dependencies) := by
  apply Subsingleton.elim

/--
The remaining-dependency certified milestone equivalence is the certificate
projection paired with the certified milestone certificate constructor.
-/
theorem poincareCompletionCertificate_iff_remaining_dependency_milestone_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_remaining_dependency_milestone_extraction_derivation_requirements =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements⟩ := by
  apply Subsingleton.elim

/--
The certified component-slot constructor is the remaining-dependency certified
component constructor applied to the package reconstructed from the slots.
-/
theorem completion_certificate_of_component_extraction_derivation_requirements_to_remaining_dependency_eq
    (smoothabilityRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent)
    (surgeryRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent)
    (topologyRequirement :
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_extraction_derivation_requirements
      smoothabilityRequirement surgeryRequirement topologyRequirement =
      completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_component_requirements.mpr
          ⟨smoothabilityRequirement, surgeryRequirement,
            topologyRequirement⟩) := by
  apply Subsingleton.elim

/--
The certified component-slot payload constructor is the remaining-dependency
certified component constructor applied to the package reconstructed from the
payload.
-/
theorem completion_certificate_of_component_extraction_derivation_requirements_payload_to_remaining_dependency_eq
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    completion_certificate_of_component_extraction_derivation_requirements_payload
      payload =
      completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_component_requirements.mpr payload) := by
  apply Subsingleton.elim

/--
The certified package-layer constructor is the remaining-dependency certified
package-layer constructor applied to the package reconstructed from the layers.
-/
theorem completion_certificate_of_package_layer_extraction_derivation_requirements_to_remaining_dependency_eq
    (smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (analyticRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage)
    (surgeryRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage)
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (topologyRequirement :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_extraction_derivation_requirements
      smoothabilityRequirement analyticRequirement surgeryRequirement
      finiteExtinctionRequirement topologyRequirement =
      completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_package_layer_requirements.mpr
          ⟨smoothabilityRequirement, analyticRequirement, surgeryRequirement,
            finiteExtinctionRequirement, topologyRequirement⟩) := by
  apply Subsingleton.elim

/--
The certified package-layer payload constructor is the remaining-dependency
certified package-layer constructor applied to the package reconstructed from the
payload.
-/
theorem completion_certificate_of_package_layer_extraction_derivation_requirements_payload_to_remaining_dependency_eq
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    completion_certificate_of_package_layer_extraction_derivation_requirements_payload
      payload =
      completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_package_layer_requirements.mpr payload) := by
  apply Subsingleton.elim

/--
The certified milestone constructor is the remaining-dependency certified
milestone constructor applied to the package reconstructed from the milestones.
-/
theorem completion_certificate_of_milestone_extraction_derivation_requirements_to_remaining_dependency_eq
    (smoothabilityBridgeRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge)
    (ricciFlowAnalyticFoundationRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation)
    (ricciFlowWithSurgeryRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionRequirement :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction)
    (extinctionToSphereHomeomorphismRequirement :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_extraction_derivation_requirements
      smoothabilityBridgeRequirement ricciFlowAnalyticFoundationRequirement
      ricciFlowWithSurgeryRequirement perelmanSingularityControlRequirement
      finiteExtinctionRequirement extinctionToSphereHomeomorphismRequirement =
      completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_milestone_requirements.mpr
          ⟨smoothabilityBridgeRequirement, ricciFlowAnalyticFoundationRequirement,
            ricciFlowWithSurgeryRequirement, perelmanSingularityControlRequirement,
            finiteExtinctionRequirement,
            extinctionToSphereHomeomorphismRequirement⟩) := by
  apply Subsingleton.elim

/--
The certified milestone payload constructor is the remaining-dependency
certified milestone constructor applied to the package reconstructed from the
payload.
-/
theorem completion_certificate_of_milestone_extraction_derivation_requirements_payload_to_remaining_dependency_eq
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    completion_certificate_of_milestone_extraction_derivation_requirements_payload
      payload =
      completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_milestone_requirements.mpr payload) := by
  apply Subsingleton.elim

/--
The aggregate certified component certificate constructor is exactly the
remaining-dependency certified component constructor after converting aggregate
dependencies to the remaining-dependency package.
-/
theorem completion_certificate_of_poincareProofDependencies_component_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_component_extraction_derivation_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_component_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified component equivalence is the aggregate dependency
projection paired with the aggregate certified component certificate
constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_component_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_component_extraction_derivation_requirements =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_component_extraction_derivation_requirements⟩ := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer certificate constructor is exactly the
remaining-dependency certified package-layer constructor after converting
aggregate dependencies to the remaining-dependency package.
-/
theorem completion_certificate_of_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_package_layer_extraction_derivation_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_package_layer_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified package-layer equivalence is the aggregate dependency
projection paired with the aggregate certified package-layer certificate
constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_package_layer_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_package_layer_extraction_derivation_requirements =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_package_layer_extraction_derivation_requirements⟩ := by
  apply Subsingleton.elim

/--
The aggregate certified milestone certificate constructor is exactly the
remaining-dependency certified milestone constructor after converting aggregate
dependencies to the remaining-dependency package.
-/
theorem completion_certificate_of_poincareProofDependencies_milestone_extraction_derivation_requirements_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_milestone_extraction_derivation_requirements
      dependencies =
      completion_certificate_of_remaining_dependency_milestone_extraction_derivation_requirements
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate certified milestone equivalence is the aggregate dependency
projection paired with the aggregate certified milestone certificate
constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_milestone_extraction_derivation_requirements_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_milestone_extraction_derivation_requirements =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_milestone_extraction_derivation_requirements⟩ := by
  apply Subsingleton.elim

/--
The aggregate extraction-derivation certificate constructor is exactly the
record built from the canonical aggregate extraction-derivation payload.
-/
theorem completion_certificate_of_aggregate_extraction_derivation_dependencies_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_aggregate_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
          canonical_completion_payload_of_aggregate_extraction_derivation_dependencies
            dependencies with
          ⟨target, criterion⟩
        exact
          ⟨canonicalCompletionTheoremName, rfl, dependencies, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
The extraction-derivation projection certificate constructor is exactly the
record built from the canonical projection extraction-derivation payload.
-/
theorem completion_certificate_of_extraction_derivation_dependency_projections_eq
    (dependencies : RemainingDependencyPackage.{u}) :
    completion_certificate_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
          canonical_completion_payload_of_extraction_derivation_dependency_projections
            dependencies with
          ⟨target, criterion⟩
        exact
          ⟨canonicalCompletionTheoremName, rfl, dependencies, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
The aggregate extraction-derivation equivalence is the remaining-dependency
projection paired with the aggregate extraction-derivation certificate
constructor.
-/
theorem poincareCompletionCertificate_iff_aggregate_extraction_derivation_dependencies_eq :
    poincareCompletionCertificate_iff_aggregate_extraction_derivation_dependencies =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_aggregate_extraction_derivation_dependencies⟩ := by
  apply Subsingleton.elim

/--
The extraction-derivation projection equivalence is the remaining-dependency
projection paired with the projection certificate constructor.
-/
theorem poincareCompletionCertificate_iff_extraction_derivation_dependency_projections_eq :
    poincareCompletionCertificate_iff_extraction_derivation_dependency_projections =
      ⟨remaining_dependency_package_of_completion_certificate,
        completion_certificate_of_extraction_derivation_dependency_projections⟩ := by
  apply Subsingleton.elim

/--
The aggregate-dependency extraction-derivation constructor is exactly the
remaining-dependency aggregate extraction-derivation constructor after
converting aggregate dependencies.
-/
theorem completion_certificate_of_poincareProofDependencies_aggregate_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_aggregate_extraction_derivation
      dependencies =
      completion_certificate_of_aggregate_extraction_derivation_dependencies
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate-dependency extraction-derivation equivalence is the aggregate
dependency projection paired with its certificate constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_aggregate_extraction_derivation_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_aggregate_extraction_derivation =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_aggregate_extraction_derivation⟩ := by
  apply Subsingleton.elim

/--
The aggregate-dependency extraction-derivation projection constructor is exactly
the remaining-dependency projection constructor after converting aggregate
dependencies.
-/
theorem completion_certificate_of_poincareProofDependencies_extraction_derivation_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    completion_certificate_of_poincareProofDependencies_extraction_derivation_projections
      dependencies =
      completion_certificate_of_extraction_derivation_dependency_projections
        (remainingDependencyPackage_iff_poincareProofDependencies.mpr
          dependencies) := by
  apply Subsingleton.elim

/--
The aggregate-dependency extraction-derivation projection equivalence is the
aggregate dependency projection paired with its certificate constructor.
-/
theorem poincareCompletionCertificate_iff_poincareProofDependencies_extraction_derivation_projections_eq :
    poincareCompletionCertificate_iff_poincareProofDependencies_extraction_derivation_projections =
      ⟨poincareProofDependencies_of_completion_certificate,
        completion_certificate_of_poincareProofDependencies_extraction_derivation_projections⟩ := by
  apply Subsingleton.elim

end Poincare
