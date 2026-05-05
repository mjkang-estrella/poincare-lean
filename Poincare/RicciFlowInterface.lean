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

end Poincare
