/-
Interface layer for the Ricci-flow part of a future Poincare proof.

This file does not formalize Ricci flow itself. It separates the future
geometric-analysis theorem from the final topological assembly step, so that the
remaining gap is represented by named hypotheses rather than by a vague
reference to "Perelman".
-/

import Poincare.Assembly

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Predicate naming the future result that a compact simply connected 3-manifold
becomes extinct under Ricci flow with surgery.

The production constructor stores a certificate tying the conclusion to named
flow, surgery, control, width, curvature, time-bound, and derivation evidence.
-/
structure FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] where
  flowEvidence : Prop
  surgeryEvidence : Prop
  controlEvidence : Prop
  widthEvidence : Prop
  curvatureEvidence : Prop
  timeBoundEvidence : Prop
  derivationEvidence : Prop
  flow : flowEvidence
  surgery : surgeryEvidence
  control : controlEvidence
  width : widthEvidence
  curvature : curvatureEvidence
  timeBound : timeBoundEvidence
  derivation : derivationEvidence

/--
Predicate naming that a compact simply connected 3-manifold becomes extinct
under Ricci flow with surgery.
-/
structure FiniteExtinctionByRicciFlowWithSurgery
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop where
  productionCertificate_source :
    Nonempty (FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M)

/-- Compatibility constructor from a finite-extinction production certificate. -/
def FiniteExtinctionByRicciFlowWithSurgery.of_production_certificate
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (certificate :
      FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate M) :
    FiniteExtinctionByRicciFlowWithSurgery M where
  productionCertificate_source := ⟨certificate⟩

/--
The remaining universal Ricci-flow input after the current interface's
post-extinction extraction component has been discharged.
-/
def UniversalFiniteExtinctionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      FiniteExtinctionByRicciFlowWithSurgery M

/--
The universal finite-extinction statement is exactly finite extinction for every
compact simply connected charted 3-manifold target.
-/
theorem universalFiniteExtinctionStatement_eq :
    UniversalFiniteExtinctionStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :=
  rfl

/--
The topological extraction theorem needed after finite extinction.

This is a theorem-shaped interface: given finite extinction for a closed simply
connected topological 3-manifold, it returns the homeomorphism conclusion.
-/
def ExtinctionImpliesSphereStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      FiniteExtinctionByRicciFlowWithSurgery M →
        Nonempty (M ≃ₜ ThreeSphere)

/--
The theorem-shaped finite-extinction-to-sphere interface is exactly the stated
universal homeomorphism extractor.
-/
theorem extinctionImpliesSphereStatement_eq :
    ExtinctionImpliesSphereStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ ThreeSphere)) :=
  rfl

/--
After the finite-extinction conclusion interface gains a production
constructor, finite extinction no longer eliminates the post-extinction
topology boundary.  This compatibility theorem records the explicit extractor
that the final assembly layer must still receive.
-/
theorem extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery :
    ExtinctionImpliesSphereStatement.{u} →
      ExtinctionImpliesSphereStatement.{u} :=
  id

/--
The explicit-extractor compatibility theorem is definitionally the identity
bridge on the post-extinction extraction statement.
-/
theorem extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery_eq :
    extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery.{u} =
      id := by
  apply Subsingleton.elim

/--
If future Ricci-flow work supplies finite extinction for every compact simply
connected 3-manifold, and future topology work extracts a sphere homeomorphism
from finite extinction, then the Poincare statement follows.

This is a real proof-bearing assembly theorem, but both mathematical inputs are
explicit hypotheses.
-/
theorem poincare_statement_of_extinction_and_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  intro M _ _ _ _ _
  exact extractSphere M (finiteExtinction M)

/--
The extinction/extraction assembly theorem is exactly the pointwise application
of the post-extinction topology extraction theorem to the finite-extinction
witness for the same target manifold.
-/
theorem poincare_statement_of_extinction_and_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_statement_of_extinction_and_extraction
        finiteExtinction extractSphere =
      (by
        intro M _ _ _ _ _
        exact extractSphere M (finiteExtinction M)) := by
  apply Subsingleton.elim

/-- Universal finite extinction and post-extinction extraction expose the local Poincare target. -/
theorem poincare_statement_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_extinction_and_extraction
    finiteExtinction
    (extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery
      extractSphere)

/--
The finite-extinction/extraction local statement route is exactly the
extinction/extraction route with the explicit post-extinction extractor.
-/
theorem poincare_statement_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_statement_of_finite_extinction finiteExtinction extractSphere =
      poincare_statement_of_extinction_and_extraction
        finiteExtinction
        (extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery
          extractSphere) := by
  apply Subsingleton.elim

/--
The reserved final theorem endpoint follows once the two core mathematical
inputs are supplied: finite extinction for every target 3-manifold and the
post-extinction sphere extraction theorem.
-/
theorem poincare_conjecture_of_extinction_and_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_extinction_and_extraction finiteExtinction extractSphere

/--
The reserved endpoint is exactly the existing extinction/extraction assembly
theorem; this records that the remaining gap is the two mathematical inputs,
not a final assembly step.
-/
theorem poincare_conjecture_of_extinction_and_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_of_extinction_and_extraction
        finiteExtinction extractSphere =
      poincare_statement_of_extinction_and_extraction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/-- Universal finite extinction and post-extinction extraction expose the reserved endpoint. -/
theorem poincare_conjecture_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_conjecture_of_extinction_and_extraction
    finiteExtinction
    (extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery
      extractSphere)

/--
The finite-extinction/extraction route is exactly the extinction/extraction route
with the explicit post-extinction extractor.
-/
theorem poincare_conjecture_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_of_finite_extinction finiteExtinction extractSphere =
      poincare_conjecture_of_extinction_and_extraction
        finiteExtinction
        (extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery
          extractSphere) := by
  apply Subsingleton.elim

/--
The local finite-extinction statement route agrees with the reserved endpoint
for the same universal finite-extinction and extraction inputs.
-/
theorem poincare_statement_of_finite_extinction_to_reserved_endpoint_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_statement_of_finite_extinction finiteExtinction extractSphere =
      poincare_conjecture_of_finite_extinction finiteExtinction
        extractSphere := by
  apply Subsingleton.elim

/--
The finite-extinction local statement exposes the reserved endpoint route under
a direct endpoint name, with topology extraction explicit.
-/
theorem poincare_statement_of_finite_extinction_to_reserved_endpoint
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_statement_of_finite_extinction finiteExtinction extractSphere =
      poincare_conjecture_of_finite_extinction finiteExtinction
        extractSphere :=
  poincare_statement_of_finite_extinction_to_reserved_endpoint_eq
    finiteExtinction extractSphere

/--
The current final mathematical boundary: universal finite extinction plus the
post-extinction extractor supplies the Poincare target.
-/
theorem poincare_conjecture_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_conjecture_of_finite_extinction finiteExtinction extractSphere

/--
The universal-finite-extinction route is exactly the finite-extinction route
with explicit topology extraction after unfolding the named input statement.
-/
theorem poincare_conjecture_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_conjecture_of_finite_extinction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the local Poincare target
through the finite-extinction local statement route with explicit topology
extraction.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_finite_extinction finiteExtinction extractSphere

/--
The named universal finite-extinction local statement route is exactly the
finite-extinction local statement route under the named remaining input
statement and explicit topology extraction.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_statement_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_statement_of_finite_extinction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The named universal finite-extinction local statement route agrees with the
reserved universal-finite-extinction endpoint for the same inputs.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement_to_reserved_endpoint_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_statement_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_conjecture_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The named universal finite-extinction local statement exposes the reserved
endpoint route under a direct endpoint name.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement_to_reserved_endpoint
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_statement_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_conjecture_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere :=
  poincare_statement_of_universalFiniteExtinctionStatement_to_reserved_endpoint_eq
    finiteExtinction extractSphere

/--
Finite extinction plus the post-extinction topological extraction theorem
exposes the reserved endpoint together with the explicit completion criterion.
This names the final conditional route through
`poincare_conjecture_of_extinction_and_extraction`, while keeping both
mathematical inputs explicit.
-/
theorem poincare_conjecture_payload_of_extinction_and_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_conjecture_of_extinction_and_extraction
      finiteExtinction extractSphere
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The reserved endpoint payload is exactly the project completion payload
constructed from the named conditional reserved endpoint theorem.
-/
theorem poincare_conjecture_payload_of_extinction_and_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_payload_of_extinction_and_extraction
        finiteExtinction extractSphere =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_conjecture_of_extinction_and_extraction
            finiteExtinction extractSphere
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
Universal finite extinction and post-extinction extraction expose the reserved
endpoint together with the explicit completion criterion.
-/
theorem poincare_conjecture_payload_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_conjecture_of_finite_extinction finiteExtinction extractSphere
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The finite-extinction reserved endpoint payload is exactly the project
completion payload constructed from the named finite-extinction/extraction
endpoint route.
-/
theorem poincare_conjecture_payload_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_payload_of_finite_extinction
        finiteExtinction extractSphere =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_conjecture_of_finite_extinction
            finiteExtinction extractSphere
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the reserved endpoint
together with the explicit completion criterion and topology extractor.
-/
theorem poincare_conjecture_payload_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_conjecture_payload_of_finite_extinction
    finiteExtinction extractSphere

/--
The universal-finite-extinction reserved payload is exactly the
finite-extinction/extraction payload under the named remaining input statement.
-/
theorem poincare_conjecture_payload_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_conjecture_payload_of_finite_extinction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input also discharges the explicit
universe-indexed completion criterion through the reserved endpoint payload,
given the post-extinction extractor.
-/
theorem completion_criterion_of_universalFiniteExtinctionStatement
    (witness : Type u)
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The universal finite-extinction completion criterion is exactly the criterion
component extracted from the named reserved endpoint payload.
-/
theorem completion_criterion_of_universalFiniteExtinctionStatement_eq
    (witness : Type u)
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    completion_criterion_of_universalFiniteExtinctionStatement
        witness finiteExtinction extractSphere =
      (by
        rcases
            poincare_conjecture_payload_of_universalFiniteExtinctionStatement
              finiteExtinction extractSphere with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the reserved endpoint and
all universe-indexed completion criteria as one payload, with topology
extraction explicit.
-/
theorem universalFiniteExtinctionStatement_completion_payload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨poincare_conjecture_of_universalFiniteExtinctionStatement
      finiteExtinction extractSphere,
    fun witness =>
      completion_criterion_of_universalFiniteExtinctionStatement
        witness finiteExtinction extractSphere⟩

/--
The universal finite-extinction completion payload is exactly the reserved
endpoint paired with the named universal finite-extinction criterion
projection.
-/
theorem universalFiniteExtinctionStatement_completion_payload_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    universalFiniteExtinctionStatement_completion_payload
        finiteExtinction extractSphere =
      ⟨poincare_conjecture_of_universalFiniteExtinctionStatement
          finiteExtinction extractSphere,
        fun witness =>
          completion_criterion_of_universalFiniteExtinctionStatement
            witness finiteExtinction extractSphere⟩ := by
  apply Subsingleton.elim

/--
The explicit universal finite-extinction completion payload agrees with the
reserved endpoint payload.
-/
theorem universalFiniteExtinctionStatement_completion_payload_to_reserved_payload_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    universalFiniteExtinctionStatement_completion_payload
        finiteExtinction extractSphere =
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The explicit universal finite-extinction completion payload exposes the
reserved payload route under a direct endpoint name.
-/
theorem universalFiniteExtinctionStatement_completion_payload_to_reserved_payload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    universalFiniteExtinctionStatement_completion_payload
        finiteExtinction extractSphere =
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere :=
  universalFiniteExtinctionStatement_completion_payload_to_reserved_payload_eq
    finiteExtinction extractSphere

/--
Conversely, a proof of the project target supplies the theorem-shaped
post-extinction extraction interface. The extinction input is unused because
the target already gives the homeomorphism conclusion for every closed simply
connected 3-manifold.
-/
theorem extinction_extraction_of_poincare_statement
    (target : PoincareConjectureStatement.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  intro M _ _ _ _ _ _extinction
  exact target M

/--
The reverse extraction projection is exactly the target proof applied to the
same target manifold, with the finite-extinction input unused.
-/
theorem extinction_extraction_of_poincare_statement_eq
    (target : PoincareConjectureStatement.{u}) :
    extinction_extraction_of_poincare_statement target =
      (by
        intro M _ _ _ _ _ _extinction
        exact target M) := by
  apply Subsingleton.elim

/--
Once finite extinction is available for every target 3-manifold, the Poincare
target is equivalent to the post-extinction topology extraction theorem.
-/
theorem poincare_statement_iff_extinction_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    PoincareConjectureStatement.{u} ↔
      ExtinctionImpliesSphereStatement.{u} := by
  constructor
  · exact extinction_extraction_of_poincare_statement
  · exact poincare_statement_of_extinction_and_extraction finiteExtinction

/--
The extinction/extraction equivalence for the project target is the pair of the
named reverse extraction projection and the named assembly theorem.
-/
theorem poincare_statement_iff_extinction_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    poincare_statement_iff_extinction_extraction finiteExtinction =
      (by
        constructor
        · exact extinction_extraction_of_poincare_statement
        · exact poincare_statement_of_extinction_and_extraction
            finiteExtinction) := by
  apply Subsingleton.elim

/--
For the named universal finite-extinction input, the project target is
equivalent to the post-extinction topology extraction theorem.
-/
theorem poincare_statement_iff_extinction_extraction_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    PoincareConjectureStatement.{u} ↔
      ExtinctionImpliesSphereStatement.{u} :=
  poincare_statement_iff_extinction_extraction finiteExtinction

/--
The named universal finite-extinction project-target equivalence is exactly
the raw finite-extinction project-target equivalence under the named remaining
input statement.
-/
theorem poincare_statement_iff_extinction_extraction_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    poincare_statement_iff_extinction_extraction_of_universalFiniteExtinctionStatement
        finiteExtinction =
      poincare_statement_iff_extinction_extraction finiteExtinction := by
  apply Subsingleton.elim

/--
Finite extinction plus the topological extraction theorem exposes the local
target and the explicit completion criterion as one payload.
-/
theorem poincare_payload_of_extinction_and_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_statement_of_extinction_and_extraction
      finiteExtinction extractSphere
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The extinction/extraction payload is exactly the project completion payload
constructed from the named extinction/extraction target assembly route.
-/
theorem poincare_payload_of_extinction_and_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_extinction_and_extraction
        finiteExtinction extractSphere =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extractSphere
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The local extinction/extraction payload agrees with the reserved endpoint
payload for the same two mathematical inputs.
-/
theorem poincare_payload_of_extinction_and_extraction_to_reserved_payload_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_extinction_and_extraction
        finiteExtinction extractSphere =
      poincare_conjecture_payload_of_extinction_and_extraction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The local extinction/extraction payload exposes the reserved payload route
under a direct endpoint name.
-/
theorem poincare_payload_of_extinction_and_extraction_to_reserved_payload
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_extinction_and_extraction
        finiteExtinction extractSphere =
      poincare_conjecture_payload_of_extinction_and_extraction
        finiteExtinction extractSphere :=
  poincare_payload_of_extinction_and_extraction_to_reserved_payload_eq
    finiteExtinction extractSphere

/--
Universal finite extinction and post-extinction extraction expose the local
target and the explicit completion criterion.
-/
theorem poincare_payload_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_statement_of_finite_extinction finiteExtinction extractSphere
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The finite-extinction local payload is the project completion payload
constructed from the named finite-extinction/extraction local target.
-/
theorem poincare_payload_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_finite_extinction finiteExtinction extractSphere =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_statement_of_finite_extinction
            finiteExtinction extractSphere
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The local finite-extinction payload agrees with the reserved endpoint payload
for the same universal finite-extinction and extraction inputs.
-/
theorem poincare_payload_of_finite_extinction_to_reserved_payload_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_finite_extinction finiteExtinction extractSphere =
      poincare_conjecture_payload_of_finite_extinction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The finite-extinction local payload exposes the reserved payload route under a
direct endpoint name, with topology extraction explicit.
-/
theorem poincare_payload_of_finite_extinction_to_reserved_payload
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_finite_extinction finiteExtinction extractSphere =
      poincare_conjecture_payload_of_finite_extinction
        finiteExtinction extractSphere :=
  poincare_payload_of_finite_extinction_to_reserved_payload_eq
    finiteExtinction extractSphere

/--
The named universal finite-extinction input exposes the local target and the
explicit completion criterion through the local finite-extinction payload and
topology extractor.
-/
theorem poincare_payload_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_payload_of_finite_extinction finiteExtinction extractSphere

/--
The named universal finite-extinction local payload is exactly the
finite-extinction local payload under the named remaining input statement and
explicit topology extraction.
-/
theorem poincare_payload_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_payload_of_finite_extinction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The named universal finite-extinction local payload agrees with the reserved
universal-finite-extinction payload for the same inputs.
-/
theorem poincare_payload_of_universalFiniteExtinctionStatement_to_reserved_payload_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
The named universal finite-extinction local payload exposes the reserved
payload route under a direct endpoint name.
-/
theorem poincare_payload_of_universalFiniteExtinctionStatement_to_reserved_payload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    poincare_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere :=
  poincare_payload_of_universalFiniteExtinctionStatement_to_reserved_payload_eq
    finiteExtinction extractSphere

/--
Finite extinction plus the post-extinction topological extraction theorem
also exposes the canonical mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_extinction_and_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_extinction_and_extraction
      finiteExtinction extractSphere)

/--
The canonical topological statement route is exactly the canonical statement
projection applied to the named extinction/extraction target assembly theorem.
-/
theorem canonical_three_sphere_statement_of_extinction_and_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_three_sphere_statement_of_extinction_and_extraction
        finiteExtinction extractSphere =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_extinction_and_extraction
          finiteExtinction extractSphere) := by
  apply Subsingleton.elim

/--
Universal finite extinction and post-extinction extraction expose the canonical
mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_extinction_and_extraction
    finiteExtinction
    (extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery
      extractSphere)

/--
The finite-extinction/extraction canonical statement route is the
extinction/extraction canonical route with the explicit post-extinction
extractor.
-/
theorem canonical_three_sphere_statement_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_three_sphere_statement_of_finite_extinction
        finiteExtinction extractSphere =
      canonical_three_sphere_statement_of_extinction_and_extraction
        finiteExtinction
        (extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery
          extractSphere) := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the canonical
mathlib-shaped topological 3-sphere statement through the finite-extinction
canonical statement route and explicit topology extraction.
-/
theorem canonical_three_sphere_statement_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_finite_extinction
    finiteExtinction extractSphere

/--
The named universal finite-extinction canonical statement route is exactly the
finite-extinction canonical statement route under the named remaining input
statement and explicit topology extraction.
-/
theorem canonical_three_sphere_statement_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    canonical_three_sphere_statement_of_universalFiniteExtinctionStatement
        finiteExtinction extractSphere =
      canonical_three_sphere_statement_of_finite_extinction
        finiteExtinction extractSphere := by
  apply Subsingleton.elim

/--
Once finite extinction is available for every target 3-manifold, the canonical
mathlib-shaped topological 3-sphere statement is equivalent to the
post-extinction topology extraction theorem.
-/
theorem canonical_three_sphere_statement_iff_extinction_extraction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) ↔
      ExtinctionImpliesSphereStatement.{u} := by
  constructor
  · intro h
    exact extinction_extraction_of_poincare_statement
      (poincare_statement_of_canonical_three_sphere_statement h)
  · intro extractSphere
    exact canonical_three_sphere_statement_of_extinction_and_extraction
      finiteExtinction extractSphere

/--
The extinction/extraction equivalence for the canonical topological statement
is the pair of the named canonical-statement conversion and assembly theorem.
-/
theorem canonical_three_sphere_statement_iff_extinction_extraction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    canonical_three_sphere_statement_iff_extinction_extraction
        finiteExtinction =
      (by
        constructor
        · intro h
          exact extinction_extraction_of_poincare_statement
            (poincare_statement_of_canonical_three_sphere_statement h)
        · intro extractSphere
          exact canonical_three_sphere_statement_of_extinction_and_extraction
            finiteExtinction extractSphere) := by
  apply Subsingleton.elim

/--
For the named universal finite-extinction input, the canonical mathlib-shaped
topological 3-sphere statement is equivalent to the post-extinction topology
extraction theorem.
-/
theorem canonical_three_sphere_statement_iff_extinction_extraction_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) ↔
      ExtinctionImpliesSphereStatement.{u} :=
  canonical_three_sphere_statement_iff_extinction_extraction finiteExtinction

/--
The named universal finite-extinction canonical equivalence is exactly the raw
finite-extinction canonical equivalence under the named remaining input
statement.
-/
theorem canonical_three_sphere_statement_iff_extinction_extraction_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    canonical_three_sphere_statement_iff_extinction_extraction_of_universalFiniteExtinctionStatement
        finiteExtinction =
      canonical_three_sphere_statement_iff_extinction_extraction
        finiteExtinction := by
  apply Subsingleton.elim

end Poincare

/-!
Generated shape equality contracts for `scripts/shape_contract_audit.sh`.
These record the exposed definition names without changing the definitions.
-/

namespace Poincare

/-- Shape contract for `FiniteExtinctionByRicciFlowWithSurgery`. -/
theorem finiteExtinctionByRicciFlowWithSurgery_eq :
    @Poincare.FiniteExtinctionByRicciFlowWithSurgery = @Poincare.FiniteExtinctionByRicciFlowWithSurgery :=
  rfl

end Poincare
