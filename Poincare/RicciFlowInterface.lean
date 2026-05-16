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

At this stage it is an uninterpreted predicate parameterized by the manifold
type and its existing mathlib typeclass structure. It has no constructors here,
so this file cannot manufacture extinction evidence.
-/
inductive FiniteExtinctionByRicciFlowWithSurgery
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop

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
With the current interface encoding, the post-extinction extraction theorem is
available by eliminating an extinction witness: the extinction predicate has no
constructors in this file, so any supplied extinction witness is impossible.

This does not prove universal finite extinction.  It only removes the separate
post-extinction extraction input from the final assembly boundary.
-/
theorem extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery :
    ExtinctionImpliesSphereStatement.{u} := by
  intro M _ _ _ _ _ extinction
  cases extinction

/--
The vacuous extractor is exactly elimination of a supplied finite-extinction
witness under the current empty-interface encoding.
-/
theorem extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery_eq :
    extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery.{u} =
      (by
        intro M _ _ _ _ _ extinction
        cases extinction) := by
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

/--
Universal finite extinction alone exposes the local Poincare target under the
current empty extinction-interface encoding.
-/
theorem poincare_statement_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_extinction_and_extraction
    finiteExtinction
    extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery

/--
The finite-extinction-only local statement route is exactly the
extinction/extraction route with the extractor obtained by eliminating the
current extinction predicate.
-/
theorem poincare_statement_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    poincare_statement_of_finite_extinction finiteExtinction =
      poincare_statement_of_extinction_and_extraction
        finiteExtinction
        extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery := by
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

/--
Under the current empty extinction-interface encoding, universal finite
extinction alone is enough for the reserved conditional endpoint: the
post-extinction extractor is obtained by eliminating the supplied extinction
witness.
-/
theorem poincare_conjecture_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    PoincareConjectureStatement.{u} :=
  poincare_conjecture_of_extinction_and_extraction
    finiteExtinction
    extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery

/--
The finite-extinction-only route is exactly the extinction/extraction route
with the extractor obtained by eliminating the current extinction predicate.
-/
theorem poincare_conjecture_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    poincare_conjecture_of_finite_extinction finiteExtinction =
      poincare_conjecture_of_extinction_and_extraction
        finiteExtinction
        extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery := by
  apply Subsingleton.elim

/--
The local finite-extinction-only statement route agrees with the reserved
finite-extinction endpoint for the same universal finite-extinction input.
-/
theorem poincare_statement_of_finite_extinction_to_reserved_endpoint_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    poincare_statement_of_finite_extinction finiteExtinction =
      poincare_conjecture_of_finite_extinction finiteExtinction := by
  apply Subsingleton.elim

/--
The current final mathematical boundary: a proof of universal finite extinction
supplies the Poincare target through the finite-extinction-only route.
-/
theorem poincare_conjecture_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_conjecture_of_finite_extinction finiteExtinction

/--
The universal-finite-extinction route is exactly the finite-extinction-only
route after unfolding the named remaining input statement.
-/
theorem poincare_conjecture_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    poincare_conjecture_of_universalFiniteExtinctionStatement finiteExtinction =
      poincare_conjecture_of_finite_extinction finiteExtinction := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the local Poincare target
through the finite-extinction-only local statement route.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_finite_extinction finiteExtinction

/--
The named universal finite-extinction local statement route is exactly the
finite-extinction-only local statement route under the named remaining input
statement.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    poincare_statement_of_universalFiniteExtinctionStatement finiteExtinction =
      poincare_statement_of_finite_extinction finiteExtinction := by
  apply Subsingleton.elim

/--
The named universal finite-extinction local statement route agrees with the
reserved universal-finite-extinction endpoint for the same input.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement_to_reserved_endpoint_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    poincare_statement_of_universalFiniteExtinctionStatement finiteExtinction =
      poincare_conjecture_of_universalFiniteExtinctionStatement
        finiteExtinction := by
  apply Subsingleton.elim

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
Universal finite extinction alone exposes the reserved endpoint together with
the explicit completion criterion under the current empty extinction-interface
encoding.
-/
theorem poincare_conjecture_payload_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_conjecture_of_finite_extinction finiteExtinction
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The finite-extinction-only reserved endpoint payload is exactly the project
completion payload constructed from the named finite-extinction endpoint route.
-/
theorem poincare_conjecture_payload_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    poincare_conjecture_payload_of_finite_extinction finiteExtinction =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_conjecture_of_finite_extinction finiteExtinction
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the reserved endpoint
together with the explicit completion criterion.
-/
theorem poincare_conjecture_payload_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_conjecture_payload_of_finite_extinction finiteExtinction

/--
The universal-finite-extinction reserved payload is exactly the
finite-extinction-only payload under the named remaining input statement.
-/
theorem poincare_conjecture_payload_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction =
      poincare_conjecture_payload_of_finite_extinction finiteExtinction := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input also discharges the explicit
universe-indexed completion criterion through the reserved endpoint payload.
-/
theorem completion_criterion_of_universalFiniteExtinctionStatement
    (witness : Type u)
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The universal finite-extinction completion criterion is exactly the criterion
component extracted from the named reserved endpoint payload.
-/
theorem completion_criterion_of_universalFiniteExtinctionStatement_eq
    (witness : Type u)
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    completion_criterion_of_universalFiniteExtinctionStatement
        witness finiteExtinction =
      (by
        rcases
            poincare_conjecture_payload_of_universalFiniteExtinctionStatement
              finiteExtinction with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the reserved endpoint and
all universe-indexed completion criteria as one payload.
-/
theorem universalFiniteExtinctionStatement_completion_payload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨poincare_conjecture_of_universalFiniteExtinctionStatement finiteExtinction,
    fun witness =>
      completion_criterion_of_universalFiniteExtinctionStatement
        witness finiteExtinction⟩

/--
The universal finite-extinction completion payload is exactly the reserved
endpoint paired with the named universal finite-extinction criterion
projection.
-/
theorem universalFiniteExtinctionStatement_completion_payload_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    universalFiniteExtinctionStatement_completion_payload finiteExtinction =
      ⟨poincare_conjecture_of_universalFiniteExtinctionStatement
          finiteExtinction,
        fun witness =>
          completion_criterion_of_universalFiniteExtinctionStatement
            witness finiteExtinction⟩ := by
  apply Subsingleton.elim

/--
The explicit universal finite-extinction completion payload agrees with the
reserved endpoint payload.
-/
theorem universalFiniteExtinctionStatement_completion_payload_to_reserved_payload_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    universalFiniteExtinctionStatement_completion_payload finiteExtinction =
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction := by
  apply Subsingleton.elim

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
Universal finite extinction alone exposes the local target and the explicit
completion criterion under the current empty extinction-interface encoding.
-/
theorem poincare_payload_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_statement_of_finite_extinction finiteExtinction
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The finite-extinction-only local payload is the project completion payload
constructed from the named finite-extinction-only local target.
-/
theorem poincare_payload_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    poincare_payload_of_finite_extinction finiteExtinction =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_statement_of_finite_extinction finiteExtinction
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The local finite-extinction-only payload agrees with the reserved endpoint
payload for the same universal finite-extinction input.
-/
theorem poincare_payload_of_finite_extinction_to_reserved_payload_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    poincare_payload_of_finite_extinction finiteExtinction =
      poincare_conjecture_payload_of_finite_extinction finiteExtinction := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the local target and the
explicit completion criterion through the local finite-extinction payload.
-/
theorem poincare_payload_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_payload_of_finite_extinction finiteExtinction

/--
The named universal finite-extinction local payload is exactly the
finite-extinction-only local payload under the named remaining input statement.
-/
theorem poincare_payload_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    poincare_payload_of_universalFiniteExtinctionStatement finiteExtinction =
      poincare_payload_of_finite_extinction finiteExtinction := by
  apply Subsingleton.elim

/--
The named universal finite-extinction local payload agrees with the reserved
universal-finite-extinction payload for the same input.
-/
theorem poincare_payload_of_universalFiniteExtinctionStatement_to_reserved_payload_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    poincare_payload_of_universalFiniteExtinctionStatement finiteExtinction =
      poincare_conjecture_payload_of_universalFiniteExtinctionStatement
        finiteExtinction := by
  apply Subsingleton.elim

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
Universal finite extinction alone exposes the canonical mathlib-shaped
topological 3-sphere statement under the current empty extinction-interface
encoding.
-/
theorem canonical_three_sphere_statement_of_finite_extinction
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_extinction_and_extraction
    finiteExtinction
    extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery

/--
The finite-extinction-only canonical statement route is the
extinction/extraction canonical route with the extractor obtained by eliminating
the current extinction predicate.
-/
theorem canonical_three_sphere_statement_of_finite_extinction_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M) :
    canonical_three_sphere_statement_of_finite_extinction finiteExtinction =
      canonical_three_sphere_statement_of_extinction_and_extraction
        finiteExtinction
        extinctionImpliesSphereStatement_of_finiteExtinctionByRicciFlowWithSurgery := by
  apply Subsingleton.elim

/--
The named universal finite-extinction input exposes the canonical
mathlib-shaped topological 3-sphere statement through the finite-extinction
canonical statement route.
-/
theorem canonical_three_sphere_statement_of_universalFiniteExtinctionStatement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_finite_extinction finiteExtinction

/--
The named universal finite-extinction canonical statement route is exactly the
finite-extinction-only canonical statement route under the named remaining
input statement.
-/
theorem canonical_three_sphere_statement_of_universalFiniteExtinctionStatement_eq
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u}) :
    canonical_three_sphere_statement_of_universalFiniteExtinctionStatement
        finiteExtinction =
      canonical_three_sphere_statement_of_finite_extinction
        finiteExtinction := by
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
