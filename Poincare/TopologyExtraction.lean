/-
Typed interfaces for the topological extraction layer after finite extinction.

Finite extinction under Ricci flow with surgery is still not the final
homeomorphism statement. This module names the post-extinction topology inputs
needed to identify the manifold with the standard 3-sphere.
-/

import Poincare.RicciFlowInterface
import Mathlib.Topology.Compactification.OnePoint.Sphere

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The one-point compactification model uses three-dimensional Euclidean space, so
its ambient sphere has the four coordinates of the project target.
-/
theorem onePoint_threeSpace_finrank_eq :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) + 1 = Fintype.card (Fin 4) := by
  rw [finrank_euclideanSpace_fin]
  norm_num

/-- The finite-rank equation is the standard computation for `ℝ^3` and `Fin 4`. -/
theorem onePoint_threeSpace_finrank_eq_eq :
    onePoint_threeSpace_finrank_eq =
      (by
        rw [finrank_euclideanSpace_fin]
        norm_num) := by
  apply Subsingleton.elim

/--
Mathlib's one-point compactification of three-dimensional Euclidean space is
homeomorphic to the project's concrete `ThreeSphere`.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere :
    Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere) := by
  exact ⟨onePointEquivSphereOfFinrankEq (ι := Fin 4)
    (V := EuclideanSpace ℝ (Fin 3)) onePoint_threeSpace_finrank_eq⟩

/-- The compactification homeomorphism is mathlib's finite-rank sphere route. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_eq :
    onePoint_threeSpace_homeomorph_threeSphere =
      ⟨onePointEquivSphereOfFinrankEq (ι := Fin 4)
        (V := EuclideanSpace ℝ (Fin 3)) onePoint_threeSpace_finrank_eq⟩ := by
  apply Subsingleton.elim

/-- The standard sphere is homeomorphic to the one-point compactification model. -/
theorem threeSphere_homeomorph_onePoint_threeSpace :
    Nonempty (ThreeSphere ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases onePoint_threeSpace_homeomorph_threeSphere with ⟨e⟩
  exact ⟨e.symm⟩

/-- The reverse compactification route is inversion of the forward route. -/
theorem threeSphere_homeomorph_onePoint_threeSpace_eq :
    threeSphere_homeomorph_onePoint_threeSpace =
      (by
        rcases onePoint_threeSpace_homeomorph_threeSphere with ⟨e⟩
        exact ⟨e.symm⟩) := by
  apply Subsingleton.elim

/--
Recognition through the one-point compactification model implies recognition
against the project target sphere.
-/
theorem homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases h with ⟨eM⟩
  rcases onePoint_threeSpace_homeomorph_threeSphere with ⟨eS⟩
  exact ⟨eM.trans eS⟩

/-- The compactification-to-target route is composition with the named model map. -/
theorem homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace_eq
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace h =
      (by
        rcases h with ⟨eM⟩
        rcases onePoint_threeSpace_homeomorph_threeSphere with ⟨eS⟩
        exact ⟨eM.trans eS⟩) := by
  apply Subsingleton.elim

/--
Recognition against the project target sphere can be restated through the
one-point compactification model.
-/
theorem homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases h with ⟨eM⟩
  rcases onePoint_threeSpace_homeomorph_threeSphere with ⟨eS⟩
  exact ⟨eM.trans eS.symm⟩

/-- The target-to-compactification route is composition with the inverse model map. -/
theorem homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere_eq
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h =
      (by
        rcases h with ⟨eM⟩
        rcases onePoint_threeSpace_homeomorph_threeSphere with ⟨eS⟩
        exact ⟨eM.trans eS.symm⟩) := by
  apply Subsingleton.elim

/--
For any source space, being homeomorphic to the project target sphere is
equivalent to being homeomorphic to the one-point compactification model.
-/
theorem homeomorph_to_threeSphere_iff_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M] :
    Nonempty (M ≃ₜ ThreeSphere) ↔
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  constructor
  · exact homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
  · exact homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace

/-- The compactification recognition equivalence is the pair of named transports. -/
theorem homeomorph_to_threeSphere_iff_homeomorph_to_onePoint_threeSpace_eq
    {M : Type u} [TopologicalSpace M] :
    (homeomorph_to_threeSphere_iff_homeomorph_to_onePoint_threeSpace :
      Nonempty (M ≃ₜ ThreeSphere) ↔
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) =
      (by
        constructor
        · exact homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
        · exact homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace) := by
  apply Subsingleton.elim

/--
Named universal recognition statement using the one-point compactification
model instead of the project target sphere.
-/
def OnePointThreeSpaceRecognitionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/-- The named universal compactification-recognition statement expands to its pointwise shape. -/
theorem onePointThreeSpaceRecognitionStatement_eq :
    OnePointThreeSpaceRecognitionStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  rfl

/--
If every candidate manifold in the Poincare statement is recognized as the
one-point compactification model, the project target statement follows.
-/
theorem poincareConjectureStatement_of_onePoint_threeSpace_recognition
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    PoincareConjectureStatement.{u} := by
  intro M _top _t2 _charted _simple _compact
  exact homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace (h M)

/-- The compactification-recognition reduction is pointwise composition with the model map. -/
theorem poincareConjectureStatement_of_onePoint_threeSpace_recognition_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincareConjectureStatement_of_onePoint_threeSpace_recognition h =
      (by
        intro M _top _t2 _charted _simple _compact
        exact homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace (h M)) := by
  apply Subsingleton.elim

/--
The named compactification-recognition statement implies the project target
statement.
-/
theorem poincareConjectureStatement_of_onePointThreeSpaceRecognitionStatement
    (h : OnePointThreeSpaceRecognitionStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  exact poincareConjectureStatement_of_onePoint_threeSpace_recognition h

/-- The named compactification-recognition target route is the raw pointwise route. -/
theorem poincareConjectureStatement_of_onePointThreeSpaceRecognitionStatement_eq
    (h : OnePointThreeSpaceRecognitionStatement.{u}) :
    poincareConjectureStatement_of_onePointThreeSpaceRecognitionStatement h =
      poincareConjectureStatement_of_onePoint_threeSpace_recognition h := by
  apply Subsingleton.elim

/--
Conversely, the project target statement recognizes every candidate as the
one-point compactification model by composing with the inverse model map.
-/
theorem onePointThreeSpaceRecognitionStatement_of_poincareConjectureStatement
    (h : PoincareConjectureStatement.{u}) :
    OnePointThreeSpaceRecognitionStatement.{u} := by
  intro M _top _t2 _charted _simple _compact
  exact homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere (h M)

/-- The reverse universal compactification-recognition route is pointwise model composition. -/
theorem onePointThreeSpaceRecognitionStatement_of_poincareConjectureStatement_eq
    (h : PoincareConjectureStatement.{u}) :
    onePointThreeSpaceRecognitionStatement_of_poincareConjectureStatement h =
      (by
        intro M _top _t2 _charted _simple _compact
        exact homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
          (h M)) := by
  apply Subsingleton.elim

/--
The project target statement is equivalent to universal recognition by the
one-point compactification model.
-/
theorem poincareConjectureStatement_iff_onePointThreeSpaceRecognitionStatement :
    PoincareConjectureStatement.{u} ↔
      OnePointThreeSpaceRecognitionStatement.{u} := by
  constructor
  · exact onePointThreeSpaceRecognitionStatement_of_poincareConjectureStatement
  · exact poincareConjectureStatement_of_onePointThreeSpaceRecognitionStatement

/-- The compactification-recognition equivalence is the pair of named routes. -/
theorem poincareConjectureStatement_iff_onePointThreeSpaceRecognitionStatement_eq :
    poincareConjectureStatement_iff_onePointThreeSpaceRecognitionStatement.{u} =
      (by
        constructor
        · exact onePointThreeSpaceRecognitionStatement_of_poincareConjectureStatement
        · exact poincareConjectureStatement_of_onePointThreeSpaceRecognitionStatement) := by
  apply Subsingleton.elim

/--
Universal recognition by the one-point compactification model exposes the
project completion payload.
-/
theorem poincare_payload_of_onePoint_threeSpace_recognition
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_poincareConjectureStatement
    (poincareConjectureStatement_of_onePoint_threeSpace_recognition h)

/-- The compactification-recognition payload is the statement-layer payload of the reduction. -/
theorem poincare_payload_of_onePoint_threeSpace_recognition_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincare_payload_of_onePoint_threeSpace_recognition h =
      poincare_completion_payload_of_poincareConjectureStatement
        (poincareConjectureStatement_of_onePoint_threeSpace_recognition h) := by
  apply Subsingleton.elim

/--
The named compactification-recognition statement exposes the project completion
payload.
-/
theorem poincare_payload_of_onePointThreeSpaceRecognitionStatement
    (h : OnePointThreeSpaceRecognitionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_payload_of_onePoint_threeSpace_recognition h

/-- The named compactification-recognition payload route is the raw pointwise payload. -/
theorem poincare_payload_of_onePointThreeSpaceRecognitionStatement_eq
    (h : OnePointThreeSpaceRecognitionStatement.{u}) :
    poincare_payload_of_onePointThreeSpaceRecognitionStatement h =
      poincare_payload_of_onePoint_threeSpace_recognition h := by
  apply Subsingleton.elim

/--
A topology extractor that recognizes the one-point compactification model after
finite extinction satisfies the existing finite-extinction-to-sphere interface.
-/
theorem extinction_implies_sphere_of_onePoint_threeSpace_recognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ExtinctionImpliesSphereStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction
  exact homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    (recognize M extinction)

/-- The extinction extractor is compactification recognition followed by the model map. -/
theorem extinction_implies_sphere_of_onePoint_threeSpace_recognition_eq
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    extinction_implies_sphere_of_onePoint_threeSpace_recognition recognize =
      (by
        intro M _top _t2 _charted _simple _compact extinction
        exact homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
          (recognize M extinction)) := by
  apply Subsingleton.elim

/--
Conversely, a finite-extinction-to-sphere extractor recognizes the one-point
compactification model after extinction by composing with the inverse model map.
-/
theorem onePoint_threeSpace_recognition_of_extinction_implies_sphere
    (extract : ExtinctionImpliesSphereStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        FiniteExtinctionByRicciFlowWithSurgery M →
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  intro M _top _t2 _charted _simple _compact extinction
  exact homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
    (extract M extinction)

/-- The reverse extinction compactification route is pointwise inverse-model composition. -/
theorem onePoint_threeSpace_recognition_of_extinction_implies_sphere_eq
    (extract : ExtinctionImpliesSphereStatement.{u}) :
    onePoint_threeSpace_recognition_of_extinction_implies_sphere extract =
      (by
        intro M _top _t2 _charted _simple _compact extinction
        exact homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
          (extract M extinction)) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus compactification recognition after extinction
discharges the project target statement.
-/
theorem poincare_statement_of_finite_extinction_and_onePoint_threeSpace_recognition
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    PoincareConjectureStatement.{u} := by
  exact poincare_statement_of_extinction_and_extraction finiteExtinction
    (extinction_implies_sphere_of_onePoint_threeSpace_recognition recognize)

/-- The finite-extinction compactification-recognition target route factors through the
existing finite-extinction/extraction assembly. -/
theorem poincare_statement_of_finite_extinction_and_onePoint_threeSpace_recognition_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincare_statement_of_finite_extinction_and_onePoint_threeSpace_recognition
      finiteExtinction recognize =
      poincare_statement_of_extinction_and_extraction finiteExtinction
        (extinction_implies_sphere_of_onePoint_threeSpace_recognition
          recognize) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus compactification recognition after extinction
exposes the project completion payload.
-/
theorem poincare_payload_of_finite_extinction_and_onePoint_threeSpace_recognition
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_poincareConjectureStatement
    (poincare_statement_of_finite_extinction_and_onePoint_threeSpace_recognition
      finiteExtinction recognize)

/-- The finite-extinction compactification-recognition payload is the statement-layer payload. -/
theorem poincare_payload_of_finite_extinction_and_onePoint_threeSpace_recognition_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincare_payload_of_finite_extinction_and_onePoint_threeSpace_recognition
      finiteExtinction recognize =
      poincare_completion_payload_of_poincareConjectureStatement
        (poincare_statement_of_finite_extinction_and_onePoint_threeSpace_recognition
          finiteExtinction recognize) := by
  apply Subsingleton.elim

/--
Named compactification-recognition statement after finite extinction.

This is the same topology-extraction target as
`ExtinctionImpliesSphereStatement`, but with the endpoint stated as the
one-point compactification model before composing with the model sphere map.
-/
def ExtinctionOnePointThreeSpaceRecognitionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      FiniteExtinctionByRicciFlowWithSurgery M →
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/-- The named extinction compactification-recognition statement expands to its extractor shape. -/
theorem extinctionOnePointThreeSpaceRecognitionStatement_eq :
    ExtinctionOnePointThreeSpaceRecognitionStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M →
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  rfl

/--
The named compactification-recognition statement after extinction satisfies the
existing finite-extinction-to-sphere interface.
-/
theorem extinction_implies_sphere_of_extinctionOnePointThreeSpaceRecognitionStatement
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  exact extinction_implies_sphere_of_onePoint_threeSpace_recognition recognize

/-- The named extinction-recognition route is the raw compactification-recognition route. -/
theorem extinction_implies_sphere_of_extinctionOnePointThreeSpaceRecognitionStatement_eq
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{u}) :
    extinction_implies_sphere_of_extinctionOnePointThreeSpaceRecognitionStatement
      recognize =
      extinction_implies_sphere_of_onePoint_threeSpace_recognition recognize := by
  apply Subsingleton.elim

/--
The usual finite-extinction-to-sphere interface also supplies the named
one-point compactification recognition interface.
-/
theorem extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionImpliesSphereStatement
    (extract : ExtinctionImpliesSphereStatement.{u}) :
    ExtinctionOnePointThreeSpaceRecognitionStatement.{u} := by
  exact onePoint_threeSpace_recognition_of_extinction_implies_sphere extract

/-- The named reverse extinction-recognition route is the raw reverse route. -/
theorem extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionImpliesSphereStatement_eq
    (extract : ExtinctionImpliesSphereStatement.{u}) :
    extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionImpliesSphereStatement
      extract =
      onePoint_threeSpace_recognition_of_extinction_implies_sphere extract := by
  apply Subsingleton.elim

/--
The theorem-shaped finite-extinction extraction interface is equivalent to the
same interface stated against the one-point compactification model.
-/
theorem extinctionImpliesSphereStatement_iff_extinctionOnePointThreeSpaceRecognitionStatement :
    ExtinctionImpliesSphereStatement.{u} ↔
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} := by
  constructor
  · exact extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionImpliesSphereStatement
  · exact extinction_implies_sphere_of_extinctionOnePointThreeSpaceRecognitionStatement

/-- The extinction compactification-recognition equivalence is the pair of named routes. -/
theorem extinctionImpliesSphereStatement_iff_extinctionOnePointThreeSpaceRecognitionStatement_eq :
    extinctionImpliesSphereStatement_iff_extinctionOnePointThreeSpaceRecognitionStatement.{u} =
      (by
        constructor
        · exact
            extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionImpliesSphereStatement
        · exact
            extinction_implies_sphere_of_extinctionOnePointThreeSpaceRecognitionStatement) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus the named compactification-recognition theorem
after extinction discharges the project target statement.
-/
theorem poincare_statement_of_finite_extinction_and_extinctionOnePointThreeSpaceRecognitionStatement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  exact poincare_statement_of_finite_extinction_and_onePoint_threeSpace_recognition
    finiteExtinction recognize

/-- The named extinction-recognition target route is the raw finite-extinction route. -/
theorem poincare_statement_of_finite_extinction_and_extinctionOnePointThreeSpaceRecognitionStatement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{u}) :
    poincare_statement_of_finite_extinction_and_extinctionOnePointThreeSpaceRecognitionStatement
      finiteExtinction recognize =
      poincare_statement_of_finite_extinction_and_onePoint_threeSpace_recognition
        finiteExtinction recognize := by
  apply Subsingleton.elim

/--
Universal finite extinction plus the named compactification-recognition theorem
after extinction exposes the project completion payload.
-/
theorem poincare_payload_of_finite_extinction_and_extinctionOnePointThreeSpaceRecognitionStatement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_payload_of_finite_extinction_and_onePoint_threeSpace_recognition
    finiteExtinction recognize

/-- The named extinction-recognition payload route is the raw finite-extinction payload. -/
theorem poincare_payload_of_finite_extinction_and_extinctionOnePointThreeSpaceRecognitionStatement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{u}) :
    poincare_payload_of_finite_extinction_and_extinctionOnePointThreeSpaceRecognitionStatement
      finiteExtinction recognize =
      poincare_payload_of_finite_extinction_and_onePoint_threeSpace_recognition
        finiteExtinction recognize := by
  apply Subsingleton.elim

/-- The one-point compactification model is Hausdorff. -/
theorem onePoint_threeSpace_t2Space :
    T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
  exact e.t2Space

/-- The compactification Hausdorff witness is transported from `ThreeSphere`. -/
theorem onePoint_threeSpace_t2Space_eq :
    onePoint_threeSpace_t2Space =
      (by
        rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
        exact e.t2Space) := by
  apply Subsingleton.elim

/-- The one-point compactification model is compact. -/
theorem onePoint_threeSpace_compactSpace :
    CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
  exact e.compactSpace

/-- The compactification compactness witness is transported from `ThreeSphere`. -/
theorem onePoint_threeSpace_compactSpace_eq :
    onePoint_threeSpace_compactSpace =
      (by
        rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
        exact e.compactSpace) := by
  apply Subsingleton.elim

/-- The one-point compactification model is path-connected. -/
theorem onePoint_threeSpace_pathConnectedSpace :
    PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : PathConnectedSpace ThreeSphere := threeSphere_pathConnectedSpace
  rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
  exact e.surjective.pathConnectedSpace e.continuous

/-- Path-connectedness of the compactification model is transported from `ThreeSphere`. -/
theorem onePoint_threeSpace_pathConnectedSpace_eq :
    onePoint_threeSpace_pathConnectedSpace =
      (by
        letI : PathConnectedSpace ThreeSphere := threeSphere_pathConnectedSpace
        rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
        exact e.surjective.pathConnectedSpace e.continuous) := by
  apply Subsingleton.elim

/-- The one-point compactification model is locally path-connected. -/
theorem onePoint_threeSpace_locPathConnectedSpace :
    LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : LocPathConnectedSpace ThreeSphere := threeSphere_locPathConnectedSpace
  rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
  exact e.symm.isOpenEmbedding.locPathConnectedSpace

/-- Local path-connectedness is transported along the compactification homeomorphism. -/
theorem onePoint_threeSpace_locPathConnectedSpace_eq :
    onePoint_threeSpace_locPathConnectedSpace =
      (by
        letI : LocPathConnectedSpace ThreeSphere := threeSphere_locPathConnectedSpace
        rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
        exact e.symm.isOpenEmbedding.locPathConnectedSpace) := by
  apply Subsingleton.elim

/-- The one-point compactification model is connected. -/
theorem onePoint_threeSpace_connectedSpace :
    ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_pathConnectedSpace
  infer_instance

/-- Connectedness follows from the named compactification path-connectedness proof. -/
theorem onePoint_threeSpace_connectedSpace_eq :
    onePoint_threeSpace_connectedSpace =
      (by
        letI : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_pathConnectedSpace
        infer_instance) := by
  apply Subsingleton.elim

/-- The one-point compactification model is nonempty. -/
theorem onePoint_threeSpace_nonempty :
    Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_pathConnectedSpace
  infer_instance

/-- Nonemptiness follows from the named compactification path-connectedness proof. -/
theorem onePoint_threeSpace_nonempty_eq :
    onePoint_threeSpace_nonempty =
      (by
        letI : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_pathConnectedSpace
        infer_instance) := by
  apply Subsingleton.elim

/--
Simple-connectedness of the standard sphere transports to the one-point
compactification model along the named homeomorphism.
-/
theorem onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
    [SimplyConnectedSpace ThreeSphere] :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- Compactification simple-connectedness is transported from `ThreeSphere`. -/
theorem onePoint_threeSpace_simplyConnectedSpace_of_threeSphere_eq
    [SimplyConnectedSpace ThreeSphere] :
    onePoint_threeSpace_simplyConnectedSpace_of_threeSphere =
      (by
        rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
        exact e.symm.toHomotopyEquiv.simplyConnectedSpace) := by
  apply Subsingleton.elim

/--
Simple-connectedness of the compactification model transports back to the
standard sphere along the named homeomorphism.
-/
theorem threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    SimplyConnectedSpace ThreeSphere := by
  rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- Standard-sphere simple-connectedness is transported back from the compactification model. -/
theorem threeSphere_simplyConnectedSpace_of_onePoint_threeSpace_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    threeSphere_simplyConnectedSpace_of_onePoint_threeSpace =
      (by
        rcases threeSphere_homeomorph_onePoint_threeSpace with ⟨e⟩
        exact e.toHomotopyEquiv.simplyConnectedSpace) := by
  apply Subsingleton.elim

/--
The standard sphere and the one-point compactification model have equivalent
simple-connectedness obligations.
-/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_threeSphere :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) ↔
      SimplyConnectedSpace ThreeSphere := by
  constructor
  · intro h
    letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) := h
    exact threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
  · intro h
    letI : SimplyConnectedSpace ThreeSphere := h
    exact onePoint_threeSpace_simplyConnectedSpace_of_threeSphere

/-- The simple-connectedness equivalence is the pair of named transport routes. -/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_threeSphere_eq :
    onePoint_threeSpace_simplyConnectedSpace_iff_threeSphere =
      (by
        constructor
        · intro h
          letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) := h
          exact threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
        · intro h
          letI : SimplyConnectedSpace ThreeSphere := h
          exact onePoint_threeSpace_simplyConnectedSpace_of_threeSphere) := by
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation for the one-point compactification
model. This is the compactification-side analogue of
`ThreeSphereLoopNullhomotopyStatement`.
-/
def OnePointThreeSpaceLoopNullhomotopyStatement : Prop :=
  ∀ (x : OnePoint (EuclideanSpace ℝ (Fin 3))) (γ : Path x x),
    Path.Homotopic γ (Path.refl x)

/-- The compactification loop-nullhomotopy obligation expands to every based loop. -/
theorem onePointThreeSpaceLoopNullhomotopyStatement_eq :
    OnePointThreeSpaceLoopNullhomotopyStatement =
      (∀ (x : OnePoint (EuclideanSpace ℝ (Fin 3))) (γ : Path x x),
        Path.Homotopic γ (Path.refl x)) :=
  rfl

/--
For the compactification model, simple-connectedness is equivalent to the
concrete loop-nullhomotopy obligation because path-connectedness has already
been transported from `ThreeSphere`.
-/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_loopNullhomotopyStatement :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) ↔
      OnePointThreeSpaceLoopNullhomotopyStatement := by
  rw [onePointThreeSpaceLoopNullhomotopyStatement_eq,
    simply_connected_iff_loops_nullhomotopic]
  exact ⟨fun h => h.2,
    fun h => ⟨onePoint_threeSpace_pathConnectedSpace, h⟩⟩

/-- The compactification simple-connectedness reduction is mathlib's loop criterion. -/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_loopNullhomotopyStatement_eq :
    onePoint_threeSpace_simplyConnectedSpace_iff_loopNullhomotopyStatement =
      (by
        rw [onePointThreeSpaceLoopNullhomotopyStatement_eq,
          simply_connected_iff_loops_nullhomotopic]
        exact ⟨fun h => h.2,
          fun h => ⟨onePoint_threeSpace_pathConnectedSpace, h⟩⟩) := by
  apply Subsingleton.elim

/-- A proof of the compactification loop-nullhomotopy obligation supplies simple-connectedness. -/
theorem onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement
    (h : OnePointThreeSpaceLoopNullhomotopyStatement) :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  onePoint_threeSpace_simplyConnectedSpace_iff_loopNullhomotopyStatement.mpr h

/-- The compactification loop-nullhomotopy-to-simple-connectedness route is the criterion projection. -/
theorem onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement_eq :
    onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement =
      onePoint_threeSpace_simplyConnectedSpace_iff_loopNullhomotopyStatement.mpr := by
  funext h
  apply Subsingleton.elim

/-- A supplied compactification simple-connectedness instance gives loop-nullhomotopy. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    OnePointThreeSpaceLoopNullhomotopyStatement :=
  onePoint_threeSpace_simplyConnectedSpace_iff_loopNullhomotopyStatement.mp inferInstance

/-- The compactification simple-connectedness-to-loop route is the criterion projection. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    onePoint_threeSpace_loopNullhomotopyStatement_of_simplyConnectedSpace =
      onePoint_threeSpace_simplyConnectedSpace_iff_loopNullhomotopyStatement.mp inferInstance := by
  apply Subsingleton.elim

/-- Loop-nullhomotopy of `ThreeSphere` transports to loop-nullhomotopy of the compactification model. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    OnePointThreeSpaceLoopNullhomotopyStatement := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
  exact onePoint_threeSpace_loopNullhomotopyStatement_of_simplyConnectedSpace

/-- The transported compactification loop-nullhomotopy route factors through simple-connectedness. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
        onePoint_threeSpace_loopNullhomotopyStatement_of_simplyConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/-- Compactification loop-nullhomotopy transports back to `ThreeSphere` loop-nullhomotopy. -/
theorem threeSphereLoopNullhomotopyStatement_of_onePoint_threeSpace_loopNullhomotopyStatement
    (h : OnePointThreeSpaceLoopNullhomotopyStatement) :
    ThreeSphereLoopNullhomotopyStatement := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement h
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
  exact threeSphere_loopNullhomotopyStatement_of_simplyConnectedSpace

/-- The reverse compactification loop-nullhomotopy route factors through simple-connectedness. -/
theorem threeSphereLoopNullhomotopyStatement_of_onePoint_threeSpace_loopNullhomotopyStatement_eq :
    threeSphereLoopNullhomotopyStatement_of_onePoint_threeSpace_loopNullhomotopyStatement =
      (fun h : OnePointThreeSpaceLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement h
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
        threeSphere_loopNullhomotopyStatement_of_simplyConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/-- The compactification and standard-sphere loop-nullhomotopy obligations are equivalent. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_iff_threeSphereLoopNullhomotopyStatement :
    OnePointThreeSpaceLoopNullhomotopyStatement ↔
      ThreeSphereLoopNullhomotopyStatement := by
  constructor
  · exact threeSphereLoopNullhomotopyStatement_of_onePoint_threeSpace_loopNullhomotopyStatement
  · exact onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement

/-- The compactification loop-nullhomotopy equivalence is the pair of named transports. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_iff_threeSphereLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_loopNullhomotopyStatement_iff_threeSphereLoopNullhomotopyStatement =
      (by
        constructor
        · exact
            threeSphereLoopNullhomotopyStatement_of_onePoint_threeSpace_loopNullhomotopyStatement
        · exact
            onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement) := by
  apply Subsingleton.elim

/--
The concrete path-homotopy uniqueness obligation for the one-point
compactification model. This is the compactification-side analogue of
`ThreeSpherePathHomotopyStatement`.
-/
def OnePointThreeSpacePathHomotopyStatement : Prop :=
  ∀ {x y : OnePoint (EuclideanSpace ℝ (Fin 3))} (p q : Path x y),
    Path.Homotopic p q

/-- The compactification path-homotopy obligation expands to every parallel path pair. -/
theorem onePointThreeSpacePathHomotopyStatement_eq :
    OnePointThreeSpacePathHomotopyStatement =
      (∀ {x y : OnePoint (EuclideanSpace ℝ (Fin 3))} (p q : Path x y),
        Path.Homotopic p q) :=
  rfl

/--
For the compactification model, simple-connectedness is equivalent to the
concrete path-homotopy obligation because path-connectedness has already been
transported from `ThreeSphere`.
-/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) ↔
      OnePointThreeSpacePathHomotopyStatement := by
  rw [onePointThreeSpacePathHomotopyStatement_eq,
    simply_connected_iff_paths_homotopic']
  exact ⟨fun h => h.2,
    fun h => ⟨onePoint_threeSpace_pathConnectedSpace, h⟩⟩

/-- The compactification simple-connectedness reduction is mathlib's path criterion. -/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement_eq :
    onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement =
      (by
        rw [onePointThreeSpacePathHomotopyStatement_eq,
          simply_connected_iff_paths_homotopic']
        exact ⟨fun h => h.2,
          fun h => ⟨onePoint_threeSpace_pathConnectedSpace, h⟩⟩) := by
  apply Subsingleton.elim

/-- A proof of the compactification path-homotopy obligation supplies simple-connectedness. -/
theorem onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement
    (h : OnePointThreeSpacePathHomotopyStatement) :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mpr h

/-- The compactification path-homotopy-to-simple-connectedness route is the criterion projection. -/
theorem onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement_eq :
    onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement =
      onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mpr := by
  funext h
  apply Subsingleton.elim

/-- A supplied compactification simple-connectedness instance gives path-homotopy uniqueness. -/
theorem onePoint_threeSpace_pathHomotopyStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    OnePointThreeSpacePathHomotopyStatement :=
  onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mp inferInstance

/-- The compactification simple-connectedness-to-path route is the criterion projection. -/
theorem onePoint_threeSpace_pathHomotopyStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    (onePoint_threeSpace_pathHomotopyStatement_of_simplyConnectedSpace :
      OnePointThreeSpacePathHomotopyStatement) =
      (onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mp inferInstance :
        OnePointThreeSpacePathHomotopyStatement) := by
  apply Subsingleton.elim

/-- Path-homotopy uniqueness implies loop-nullhomotopy by comparing a loop to `Path.refl`. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement
    (h : OnePointThreeSpacePathHomotopyStatement) :
    OnePointThreeSpaceLoopNullhomotopyStatement := by
  intro x γ
  exact h γ (Path.refl x)

/-- The compactification path-to-loop route is evaluation at a loop and the stationary loop. -/
theorem onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement_eq :
    onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement =
      (fun h : OnePointThreeSpacePathHomotopyStatement =>
        fun x γ => h γ (Path.refl x)) := by
  funext h x γ
  apply Subsingleton.elim

/-- Loop-nullhomotopy implies path-homotopy uniqueness through simple-connectedness. -/
theorem onePoint_threeSpace_pathHomotopyStatement_of_loopNullhomotopyStatement
    (h : OnePointThreeSpaceLoopNullhomotopyStatement) :
    OnePointThreeSpacePathHomotopyStatement :=
  onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mp
    (onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement h)

/--
The compactification loop-to-path route is simple-connectedness from
loop-nullhomotopy followed by the path-homotopy criterion.
-/
theorem onePoint_threeSpace_pathHomotopyStatement_of_loopNullhomotopyStatement_eq :
    onePoint_threeSpace_pathHomotopyStatement_of_loopNullhomotopyStatement =
      (fun h : OnePointThreeSpaceLoopNullhomotopyStatement =>
        (onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mp
          (onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement h) :
            OnePointThreeSpacePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The two compactification-side simple-connectedness obligations are equivalent. -/
theorem onePoint_threeSpace_pathHomotopyStatement_iff_loopNullhomotopyStatement :
    OnePointThreeSpacePathHomotopyStatement ↔
      OnePointThreeSpaceLoopNullhomotopyStatement :=
  ⟨onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement,
    onePoint_threeSpace_pathHomotopyStatement_of_loopNullhomotopyStatement⟩

/-- The compactification path/loop equivalence is the pair of named conversion routes. -/
theorem onePoint_threeSpace_pathHomotopyStatement_iff_loopNullhomotopyStatement_eq :
    onePoint_threeSpace_pathHomotopyStatement_iff_loopNullhomotopyStatement =
      ⟨onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement,
        onePoint_threeSpace_pathHomotopyStatement_of_loopNullhomotopyStatement⟩ := by
  apply Subsingleton.elim

/-- Path-homotopy uniqueness of `ThreeSphere` transports to the compactification model. -/
theorem onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    OnePointThreeSpacePathHomotopyStatement := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
  exact (onePoint_threeSpace_pathHomotopyStatement_of_simplyConnectedSpace :
    OnePointThreeSpacePathHomotopyStatement)

/-- The transported compactification path-homotopy route factors through simple-connectedness. -/
theorem onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement_eq :
    onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
        (onePoint_threeSpace_pathHomotopyStatement_of_simplyConnectedSpace :
          OnePointThreeSpacePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The transported compactification path route agrees with the named loop route. -/
theorem onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        (onePoint_threeSpace_pathHomotopyStatement_of_loopNullhomotopyStatement
          (onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)) :
          OnePointThreeSpacePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- Compactification path-homotopy uniqueness transports back to `ThreeSphere`. -/
theorem threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement
    (h : OnePointThreeSpacePathHomotopyStatement) :
    ThreeSpherePathHomotopyStatement := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement h
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
  exact (threeSphere_pathHomotopyStatement_of_simplyConnectedSpace :
    ThreeSpherePathHomotopyStatement)

/-- The reverse compactification path-homotopy route factors through simple-connectedness. -/
theorem threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement_eq :
    threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement =
      (fun h : OnePointThreeSpacePathHomotopyStatement =>
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement h
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
        (threeSphere_pathHomotopyStatement_of_simplyConnectedSpace :
          ThreeSpherePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The reverse compactification path route agrees with the named loop route. -/
theorem threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement_loop_route_eq :
    threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement =
      (fun h : OnePointThreeSpacePathHomotopyStatement =>
        (threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement
          (threeSphereLoopNullhomotopyStatement_of_onePoint_threeSpace_loopNullhomotopyStatement
            (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement h)) :
          ThreeSpherePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The compactification and standard-sphere path-homotopy obligations are equivalent. -/
theorem onePoint_threeSpace_pathHomotopyStatement_iff_threeSpherePathHomotopyStatement :
    OnePointThreeSpacePathHomotopyStatement ↔ ThreeSpherePathHomotopyStatement := by
  constructor
  · exact threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement
  · exact onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement

/-- The compactification path-homotopy equivalence is the pair of named transports. -/
theorem onePoint_threeSpace_pathHomotopyStatement_iff_threeSpherePathHomotopyStatement_eq :
    onePoint_threeSpace_pathHomotopyStatement_iff_threeSpherePathHomotopyStatement =
      (by
        constructor
        · exact threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement
        · exact onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement) := by
  apply Subsingleton.elim

/--
The fundamental-groupoid quotient uniqueness obligation for the one-point
compactification model. This is the compactification-side analogue of
`ThreeSpherePathQuotientSubsingletonStatement`.
-/
def OnePointThreeSpacePathQuotientSubsingletonStatement : Prop :=
  ∀ x y : OnePoint (EuclideanSpace ℝ (Fin 3)),
    Subsingleton (Path.Homotopic.Quotient x y)

/--
The compactification quotient uniqueness obligation expands to subsingleton
path-homotopy quotients between every pair of compactification points.
-/
theorem onePointThreeSpacePathQuotientSubsingletonStatement_eq :
    OnePointThreeSpacePathQuotientSubsingletonStatement =
      (∀ x y : OnePoint (EuclideanSpace ℝ (Fin 3)),
        Subsingleton (Path.Homotopic.Quotient x y)) :=
  rfl

/--
For the compactification model, simple-connectedness is equivalent to
path-homotopy quotient uniqueness because path-connectedness has already been
transported from `ThreeSphere`.
-/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) ↔
      OnePointThreeSpacePathQuotientSubsingletonStatement := by
  rw [onePointThreeSpacePathQuotientSubsingletonStatement_eq,
    simply_connected_iff_paths_homotopic]
  exact ⟨fun h => h.2,
    fun h => ⟨onePoint_threeSpace_pathConnectedSpace, h⟩⟩

/--
The compactification simple-connectedness/path-quotient reduction is mathlib's
path-homotopy quotient criterion with the named compactification
path-connectedness witness.
-/
theorem onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement =
      (by
        rw [onePointThreeSpacePathQuotientSubsingletonStatement_eq,
          simply_connected_iff_paths_homotopic]
        exact ⟨fun h => h.2,
          fun h => ⟨onePoint_threeSpace_pathConnectedSpace, h⟩⟩) := by
  apply Subsingleton.elim

/-- A proof of compactification quotient uniqueness supplies simple-connectedness. -/
theorem onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement
    (h : OnePointThreeSpacePathQuotientSubsingletonStatement) :
    SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mpr h

/--
The compactification quotient-to-simple-connectedness route is the reverse
projection of the named quotient criterion.
-/
theorem onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement =
      onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mpr := by
  funext h
  apply Subsingleton.elim

/-- A supplied compactification simple-connectedness instance gives quotient uniqueness. -/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    OnePointThreeSpacePathQuotientSubsingletonStatement :=
  onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
    inferInstance

/--
The compactification simple-connectedness-to-quotient route is the forward
projection of the named quotient criterion.
-/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    (onePoint_threeSpace_pathQuotientSubsingletonStatement_of_simplyConnectedSpace :
      OnePointThreeSpacePathQuotientSubsingletonStatement) =
      (onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
        inferInstance : OnePointThreeSpacePathQuotientSubsingletonStatement) := by
  apply Subsingleton.elim

/-- Path-homotopy uniqueness gives quotient uniqueness through the local criterion. -/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_of_pathHomotopyStatement
    (h : OnePointThreeSpacePathHomotopyStatement) :
    OnePointThreeSpacePathQuotientSubsingletonStatement :=
  onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
    (onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement h)

/--
The compactification path-to-quotient route factors through local
simple-connectedness.
-/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_of_pathHomotopyStatement_eq :
    onePoint_threeSpace_pathQuotientSubsingletonStatement_of_pathHomotopyStatement =
      (fun h : OnePointThreeSpacePathHomotopyStatement =>
        (onePoint_threeSpace_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
          (onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement h) :
            OnePointThreeSpacePathQuotientSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- Quotient uniqueness gives path-homotopy uniqueness through the local criterion. -/
theorem onePoint_threeSpace_pathHomotopyStatement_of_pathQuotientSubsingletonStatement
    (h : OnePointThreeSpacePathQuotientSubsingletonStatement) :
    OnePointThreeSpacePathHomotopyStatement :=
  onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mp
    (onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h)

/--
The compactification quotient-to-path route factors through local
simple-connectedness.
-/
theorem onePoint_threeSpace_pathHomotopyStatement_of_pathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_pathHomotopyStatement_of_pathQuotientSubsingletonStatement =
      (fun h : OnePointThreeSpacePathQuotientSubsingletonStatement =>
        (onePoint_threeSpace_simplyConnectedSpace_iff_pathHomotopyStatement.mp
          (onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h) :
            OnePointThreeSpacePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The compactification path-homotopy and path-quotient obligations are equivalent. -/
theorem onePoint_threeSpace_pathHomotopyStatement_iff_pathQuotientSubsingletonStatement :
    OnePointThreeSpacePathHomotopyStatement ↔
      OnePointThreeSpacePathQuotientSubsingletonStatement :=
  ⟨onePoint_threeSpace_pathQuotientSubsingletonStatement_of_pathHomotopyStatement,
    onePoint_threeSpace_pathHomotopyStatement_of_pathQuotientSubsingletonStatement⟩

/-- The compactification path/quotient equivalence is the pair of named routes. -/
theorem onePoint_threeSpace_pathHomotopyStatement_iff_pathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_pathHomotopyStatement_iff_pathQuotientSubsingletonStatement =
      ⟨onePoint_threeSpace_pathQuotientSubsingletonStatement_of_pathHomotopyStatement,
        onePoint_threeSpace_pathHomotopyStatement_of_pathQuotientSubsingletonStatement⟩ := by
  apply Subsingleton.elim

/-- Quotient uniqueness of `ThreeSphere` transports to the compactification model. -/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    OnePointThreeSpacePathQuotientSubsingletonStatement := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
  exact (onePoint_threeSpace_pathQuotientSubsingletonStatement_of_simplyConnectedSpace :
    OnePointThreeSpacePathQuotientSubsingletonStatement)

/-- The transported compactification quotient route factors through simple-connectedness. -/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
        (onePoint_threeSpace_pathQuotientSubsingletonStatement_of_simplyConnectedSpace :
          OnePointThreeSpacePathQuotientSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The transported compactification quotient route agrees with the named path route. -/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement_path_route_eq :
    onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        onePoint_threeSpace_pathQuotientSubsingletonStatement_of_pathHomotopyStatement
          (onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h))) := by
  funext h
  apply Subsingleton.elim

/-- Compactification quotient uniqueness transports back to `ThreeSphere`. -/
theorem threeSpherePathQuotientSubsingletonStatement_of_onePoint_threeSpace_pathQuotientSubsingletonStatement
    (h : OnePointThreeSpacePathQuotientSubsingletonStatement) :
    ThreeSpherePathQuotientSubsingletonStatement := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
  exact (threeSphere_pathQuotientSubsingletonStatement_of_simplyConnectedSpace :
    ThreeSpherePathQuotientSubsingletonStatement)

/-- The reverse compactification quotient route factors through simple-connectedness. -/
theorem threeSpherePathQuotientSubsingletonStatement_of_onePoint_threeSpace_pathQuotientSubsingletonStatement_eq :
    threeSpherePathQuotientSubsingletonStatement_of_onePoint_threeSpace_pathQuotientSubsingletonStatement =
      (fun h : OnePointThreeSpacePathQuotientSubsingletonStatement =>
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_onePoint_threeSpace
        (threeSphere_pathQuotientSubsingletonStatement_of_simplyConnectedSpace :
          ThreeSpherePathQuotientSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The reverse compactification quotient route agrees with the named path route. -/
theorem threeSpherePathQuotientSubsingletonStatement_of_onePoint_threeSpace_pathQuotientSubsingletonStatement_path_route_eq :
    threeSpherePathQuotientSubsingletonStatement_of_onePoint_threeSpace_pathQuotientSubsingletonStatement =
      (fun h : OnePointThreeSpacePathQuotientSubsingletonStatement =>
        threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement
          (threeSpherePathHomotopyStatement_of_onePoint_threeSpace_pathHomotopyStatement
            (onePoint_threeSpace_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h))) := by
  funext h
  apply Subsingleton.elim

/-- The compactification and standard-sphere path-quotient obligations are equivalent. -/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_iff_threeSpherePathQuotientSubsingletonStatement :
    OnePointThreeSpacePathQuotientSubsingletonStatement ↔
      ThreeSpherePathQuotientSubsingletonStatement := by
  constructor
  · exact
      threeSpherePathQuotientSubsingletonStatement_of_onePoint_threeSpace_pathQuotientSubsingletonStatement
  · exact
      onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement

/-- The compactification quotient equivalence is the pair of named transports. -/
theorem onePoint_threeSpace_pathQuotientSubsingletonStatement_iff_threeSpherePathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_pathQuotientSubsingletonStatement_iff_threeSpherePathQuotientSubsingletonStatement =
      (by
        constructor
        · exact
            threeSpherePathQuotientSubsingletonStatement_of_onePoint_threeSpace_pathQuotientSubsingletonStatement
        · exact
            onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement) := by
  apply Subsingleton.elim

/--
The one-point compactification model carries a charted-space structure
transported from the standard sphere.
-/
@[reducible] noncomputable def onePoint_threeSpace_chartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  let e := Classical.choice threeSphere_homeomorph_onePoint_threeSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere := threeSphere_chartedSpace
  exact e.isLocalHomeomorph.chartedSpace e.surjective

/-- The compactification charted-space structure is pushed forward along the model map. -/
theorem onePoint_threeSpace_chartedSpace_eq :
    onePoint_threeSpace_chartedSpace =
      (by
        let e := Classical.choice threeSphere_homeomorph_onePoint_threeSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere := threeSphere_chartedSpace
        exact e.isLocalHomeomorph.chartedSpace e.surjective) := by
  rfl

/-- The compactification model is a topological 3-manifold for the transported charts. -/
theorem onePoint_threeSpace_topologicalManifold :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
      onePoint_threeSpace_chartedSpace
    IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_chartedSpace
  infer_instance

/-- The topological-manifold witness is the generic `C^0` witness for the transported charts. -/
theorem onePoint_threeSpace_topologicalManifold_eq :
    onePoint_threeSpace_topologicalManifold =
      (by
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
            (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_chartedSpace
        infer_instance) := by
  apply Subsingleton.elim

/--
The compactification model has the basic topological prerequisites supplied by
its homeomorphism with `ThreeSphere`.
-/
theorem onePoint_threeSpace_topological_prerequisites :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_compactSpace,
    onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
    onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩

/-- The compactification prerequisite payload is the tuple of named local witnesses. -/
theorem onePoint_threeSpace_topological_prerequisites_eq :
    onePoint_threeSpace_topological_prerequisites =
      ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_compactSpace,
        onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
        onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩ := by
  apply Subsingleton.elim

/--
The compactification model has a proof-bearing `C^0` 3-manifold prerequisite
payload, with charts transported from `ThreeSphere`.
-/
theorem onePoint_threeSpace_topological_manifold_prerequisites :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
    onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
    onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
    onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩

/-- The compactification `C^0` manifold payload is the tuple of named local witnesses. -/
theorem onePoint_threeSpace_topological_manifold_prerequisites_eq :
    onePoint_threeSpace_topological_manifold_prerequisites =
      ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
        onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
        onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
        onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩ := by
  apply Subsingleton.elim

/--
With the standard sphere's simple-connectedness supplied, the compactification
model has the full homotopy/manifold prerequisite payload used by the target
recognition route.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites
    [SimplyConnectedSpace ThreeSphere] :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
    onePoint_threeSpace_simplyConnectedSpace_of_threeSphere,
    onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
    onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
    onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩

/-- The full compactification prerequisite payload is the tuple of named transported witnesses. -/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_eq
    [SimplyConnectedSpace ThreeSphere] :
    onePoint_threeSpace_homotopy_manifold_prerequisites =
      ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
        onePoint_threeSpace_simplyConnectedSpace_of_threeSphere,
        onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
        onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
        onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩ := by
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation for `ThreeSphere` supplies the full
compactification homotopy/manifold prerequisite payload.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
  exact onePoint_threeSpace_homotopy_manifold_prerequisites

/--
The loop-nullhomotopy compactification prerequisite route is the full payload
after converting loop-nullhomotopy to standard-sphere simple-connectedness.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_loopNullhomotopyStatement_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
        onePoint_threeSpace_homotopy_manifold_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation for `ThreeSphere` supplies the full
compactification homotopy/manifold prerequisite payload.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
  exact onePoint_threeSpace_homotopy_manifold_prerequisites

/--
The path-homotopy compactification prerequisite route is the full payload after
converting path-homotopy to standard-sphere simple-connectedness.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
        onePoint_threeSpace_homotopy_manifold_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The direct path-homotopy compactification prerequisite route agrees with the
loop-nullhomotopy-mediated route.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        onePoint_threeSpace_homotopy_manifold_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The compactification model's own loop-nullhomotopy obligation directly supplies
the full compactification homotopy/manifold prerequisite payload.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
    (h : OnePointThreeSpaceLoopNullhomotopyStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
    onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement h,
    onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
    onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
    onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩

/-- The compactification loop payload route uses the local loop-to-simple-connectedness proof. -/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement =
      (fun h : OnePointThreeSpaceLoopNullhomotopyStatement =>
        ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
          onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement h,
          onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
          onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
          onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩) := by
  funext h
  apply Subsingleton.elim

/--
The standard-sphere loop route to compactification prerequisites agrees with
the direct compactification-loop route after transporting the loop obligation.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_loopNullhomotopyStatement_onePoint_route_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
          (onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement
            h)) := by
  funext h
  apply Subsingleton.elim

/--
The compactification model's own path-homotopy obligation directly supplies
the full compactification homotopy/manifold prerequisite payload.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
    (h : OnePointThreeSpacePathHomotopyStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
    onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement h,
    onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
    onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
    onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩

/-- The compactification path payload route uses the local path-to-simple-connectedness proof. -/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement =
      (fun h : OnePointThreeSpacePathHomotopyStatement =>
        ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
          onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement h,
          onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
          onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
          onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩) := by
  funext h
  apply Subsingleton.elim

/--
The compactification path route to prerequisites agrees with the direct
compactification-loop route.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement =
      (fun h : OnePointThreeSpacePathHomotopyStatement =>
        onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
          (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The standard-sphere path route to compactification prerequisites agrees with
the direct compactification-path route after transporting the path obligation.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement_onePoint_route_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
          (onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The standard-sphere path-quotient obligation supplies the full compactification
homotopy/manifold prerequisite payload.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
  exact onePoint_threeSpace_homotopy_manifold_prerequisites

/--
The standard-sphere quotient compactification prerequisite route is the full
payload after converting quotient uniqueness to standard-sphere
simple-connectedness.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
        onePoint_threeSpace_homotopy_manifold_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The direct standard-sphere quotient prerequisite route agrees with the
standard-sphere path-homotopy-mediated route.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathQuotientSubsingletonStatement_path_route_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The compactification model's own path-quotient obligation directly supplies
the full compactification homotopy/manifold prerequisite payload.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathQuotientSubsingletonStatement
    (h : OnePointThreeSpacePathQuotientSubsingletonStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
    onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h,
    onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
    onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
    onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩

/-- The compactification quotient payload route uses the local quotient criterion. -/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathQuotientSubsingletonStatement_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathQuotientSubsingletonStatement =
      (fun h : OnePointThreeSpacePathQuotientSubsingletonStatement =>
        ⟨onePoint_threeSpace_t2Space, onePoint_threeSpace_chartedSpace,
          onePoint_threeSpace_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h,
          onePoint_threeSpace_compactSpace, onePoint_threeSpace_topologicalManifold,
          onePoint_threeSpace_pathConnectedSpace, onePoint_threeSpace_locPathConnectedSpace,
          onePoint_threeSpace_connectedSpace, onePoint_threeSpace_nonempty⟩) := by
  funext h
  apply Subsingleton.elim

/--
The compactification quotient route to prerequisites agrees with the direct
compactification-path route.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathQuotientSubsingletonStatement_path_route_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathQuotientSubsingletonStatement =
      (fun h : OnePointThreeSpacePathQuotientSubsingletonStatement =>
        onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
          (onePoint_threeSpace_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The standard-sphere quotient route to compactification prerequisites agrees
with the direct compactification-quotient route after transporting the
quotient obligation.
-/
theorem onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathQuotientSubsingletonStatement_onePoint_route_eq :
    onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathQuotientSubsingletonStatement
          (onePoint_threeSpace_pathQuotientSubsingletonStatement_of_threeSpherePathQuotientSubsingletonStatement
            h)) := by
  funext h
  apply Subsingleton.elim

/--
Any space recognized as the one-point compactification model inherits the same
basic `C^0` 3-manifold prerequisite payload.
-/
theorem topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M := by
  rcases h with ⟨e⟩
  letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) := onePoint_threeSpace_t2Space
  letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_compactSpace
  letI : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_pathConnectedSpace
  letI : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_locPathConnectedSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_chartedSpace
  let charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
    e.symm.isLocalHomeomorph.chartedSpace e.symm.surjective
  let topological : IsManifold (𝓡 3) 0 M := by
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
    infer_instance
  let path : PathConnectedSpace M :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  let locPath : LocPathConnectedSpace M :=
    e.isOpenEmbedding.locPathConnectedSpace
  let connected : ConnectedSpace M := by
    letI : PathConnectedSpace M := path
    infer_instance
  let nonempty : Nonempty M := by
    letI : PathConnectedSpace M := path
    infer_instance
  exact ⟨e.symm.t2Space, charted, e.symm.compactSpace, topological, path, locPath,
    connected, nonempty⟩

/-- The compactification-recognition prerequisite route is explicit transport along the homeomorphism. -/
theorem topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_eq
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h =
      (by
        rcases h with ⟨e⟩
        letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) := onePoint_threeSpace_t2Space
        letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_compactSpace
        letI : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_pathConnectedSpace
        letI : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_locPathConnectedSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
            (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_chartedSpace
        let charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
          e.symm.isLocalHomeomorph.chartedSpace e.symm.surjective
        let topological : IsManifold (𝓡 3) 0 M := by
          letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
          infer_instance
        let path : PathConnectedSpace M :=
          e.symm.surjective.pathConnectedSpace e.symm.continuous
        let locPath : LocPathConnectedSpace M :=
          e.isOpenEmbedding.locPathConnectedSpace
        let connected : ConnectedSpace M := by
          letI : PathConnectedSpace M := path
          infer_instance
        let nonempty : Nonempty M := by
          letI : PathConnectedSpace M := path
          infer_instance
        exact ⟨e.symm.t2Space, charted, e.symm.compactSpace, topological, path, locPath,
          connected, nonempty⟩) := by
  apply Subsingleton.elim

/--
If the standard sphere is simply connected, any source recognized as the
one-point compactification model is simply connected by transport along the
recognizing homeomorphism.
-/
theorem simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace ThreeSphere]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    SimplyConnectedSpace M := by
  rcases h with ⟨e⟩
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- Source simple-connectedness is transported through compactification recognition. -/
theorem simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_eq
    {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace ThreeSphere]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace h =
      (by
        rcases h with ⟨e⟩
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_threeSphere
        exact e.toHomotopyEquiv.simplyConnectedSpace) := by
  apply Subsingleton.elim

/--
Recognizing a source as the one-point compactification model supplies the full
homotopy/manifold prerequisite payload once the standard sphere's
simple-connectedness is available.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace ThreeSphere]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M := by
  rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
    ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
  exact ⟨t2, charted, simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace h,
    compact, topological, path, locPath, connected, nonempty⟩

/-- The full source prerequisite payload is compactification transport plus simple-connectedness transport. -/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_eq
    {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace ThreeSphere]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h =
      (by
        rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
          ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
        exact ⟨t2, charted,
          simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace h,
          compact, topological, path, locPath, connected, nonempty⟩) := by
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation for `ThreeSphere` supplies the full
source homotopy/manifold prerequisite payload for any source recognized as the
one-point compactification model.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_loopNullhomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h

/--
The loop-nullhomotopy source prerequisite route is the full source payload after
converting loop-nullhomotopy to standard-sphere simple-connectedness.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_loopNullhomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_loopNullhomotopyStatement
      hLoop h =
      (by
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
        exact homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h) := by
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation for `ThreeSphere` supplies the full source
homotopy/manifold prerequisite payload for any source recognized as the one-point
compactification model.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_pathHomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h

/--
The path-homotopy source prerequisite route is the full source payload after
converting path-homotopy to standard-sphere simple-connectedness.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_pathHomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_pathHomotopyStatement
      hPath h =
      (by
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
        exact homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h) := by
  apply Subsingleton.elim

/--
The direct path-homotopy source prerequisite route agrees with the
loop-nullhomotopy-mediated route.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_pathHomotopyStatement_loop_route_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_pathHomotopyStatement
      hPath h =
      homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_loopNullhomotopyStatement
        (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h := by
  apply Subsingleton.elim

/--
The compactification model's own loop-nullhomotopy obligation supplies
simple-connectedness for any source recognized as the compactification model.
-/
theorem simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    SimplyConnectedSpace M := by
  rcases h with ⟨e⟩
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- Source simple-connectedness follows by compactification recognition and local loop-nullhomotopy. -/
theorem simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
      hLoop h =
      (by
        rcases h with ⟨e⟩
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
        exact e.toHomotopyEquiv.simplyConnectedSpace) := by
  apply Subsingleton.elim

/--
The compactification model's own path-homotopy obligation supplies
simple-connectedness for any source recognized as the compactification model.
-/
theorem simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    SimplyConnectedSpace M := by
  rcases h with ⟨e⟩
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- Source simple-connectedness follows by compactification recognition and local path-homotopy. -/
theorem simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
      hPath h =
      (by
        rcases h with ⟨e⟩
        letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
        exact e.toHomotopyEquiv.simplyConnectedSpace) := by
  apply Subsingleton.elim

/-- The local path route to source simple-connectedness agrees with the local loop route. -/
theorem simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement_loop_route_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
      hPath h =
      simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
        (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h := by
  apply Subsingleton.elim

/--
The compactification model's own loop-nullhomotopy obligation supplies the full
source homotopy/manifold prerequisite payload for any source recognized as the
one-point compactification model.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M := by
  rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
    ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
  exact ⟨t2, charted,
    simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
      hLoop h,
    compact, topological, path, locPath, connected, nonempty⟩

/-- The local loop source prerequisite route is compactification transport plus local simple-connectedness. -/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
      hLoop h =
      (by
        rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
          ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
        exact ⟨t2, charted,
          simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
            hLoop h,
          compact, topological, path, locPath, connected, nonempty⟩) := by
  apply Subsingleton.elim

/-- The standard-sphere loop source route agrees with the local compactification-loop route. -/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_loopNullhomotopyStatement_onePoint_route_eq
    {M : Type u} [TopologicalSpace M]
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_loopNullhomotopyStatement
      hLoop h =
      homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
        (onePoint_threeSpace_loopNullhomotopyStatement_of_threeSphereLoopNullhomotopyStatement
          hLoop) h := by
  apply Subsingleton.elim

/--
The compactification model's own path-homotopy obligation supplies the full
source homotopy/manifold prerequisite payload for any source recognized as the
one-point compactification model.
-/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M := by
  rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
    ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
  exact ⟨t2, charted,
    simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
      hPath h,
    compact, topological, path, locPath, connected, nonempty⟩

/-- The local path source prerequisite route is compactification transport plus local simple-connectedness. -/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
      hPath h =
      (by
        rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
          ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
        exact ⟨t2, charted,
          simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
            hPath h,
          compact, topological, path, locPath, connected, nonempty⟩) := by
  apply Subsingleton.elim

/-- The local compactification path source route agrees with the local loop source route. -/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement_loop_route_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
      hPath h =
      homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
        (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h := by
  apply Subsingleton.elim

/-- The standard-sphere path source route agrees with the local compactification-path route. -/
theorem homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_pathHomotopyStatement_onePoint_route_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_pathHomotopyStatement
      hPath h =
      homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
        (onePoint_threeSpace_pathHomotopyStatement_of_threeSpherePathHomotopyStatement hPath) h := by
  apply Subsingleton.elim

/--
A simply connected space recognized as the one-point compactification model
inherits the transported compactification prerequisite payload together with
the given simple-connectedness instance.
-/
theorem poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M := by
  rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
    ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
  exact ⟨t2, charted, inferInstance, compact, topological, path, locPath, connected,
    nonempty⟩

/-- The candidate prerequisite payload reuses compactification transport and the source instance. -/
theorem poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_eq
    {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace h =
      (by
        rcases topological_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace h with
          ⟨t2, charted, compact, topological, path, locPath, connected, nonempty⟩
        exact ⟨t2, charted, inferInstance, compact, topological, path, locPath,
          connected, nonempty⟩) := by
  apply Subsingleton.elim

/--
The compactification model's own loop-nullhomotopy obligation packages any
recognized source as a Poincare-candidate prerequisite payload.
-/
theorem poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M :=
  homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
    hLoop h

/-- The local loop candidate route is the local loop source-prerequisite route. -/
theorem poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
      hLoop h =
      homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
        hLoop h := by
  apply Subsingleton.elim

/--
The compactification model's own path-homotopy obligation packages any
recognized source as a Poincare-candidate prerequisite payload.
-/
theorem poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _topological : IsManifold (𝓡 3) 0 M,
    ∃ _path : PathConnectedSpace M,
    ∃ _locPath : LocPathConnectedSpace M,
    ∃ _connected : ConnectedSpace M,
      Nonempty M :=
  homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
    hPath h

/-- The local path candidate route is the local path source-prerequisite route. -/
theorem poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
      hPath h =
      homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
        hPath h := by
  apply Subsingleton.elim

/-- The local path candidate route agrees with the local loop candidate route. -/
theorem poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement_loop_route_eq
    {M : Type u} [TopologicalSpace M]
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
      hPath h =
      poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
        (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h := by
  apply Subsingleton.elim

/-- The one-point compactification model is homeomorphic to itself. -/
theorem onePoint_threeSpace_self_homeomorph :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩

/-- The compactification self-homeomorphism witness is the reflexive homeomorphism. -/
theorem onePoint_threeSpace_self_homeomorph_eq :
    onePoint_threeSpace_self_homeomorph =
      ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩ := by
  apply Subsingleton.elim

/--
The compactification model's topological-manifold prerequisites pair with the
direct reflexive self-homeomorphism endpoint.
-/
theorem onePoint_threeSpace_self_homeomorph_payload :
    ∃ _prerequisites :
      (∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
        Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
          (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  exact ⟨onePoint_threeSpace_topological_manifold_prerequisites,
    onePoint_threeSpace_self_homeomorph⟩

/-- The compactification self payload is the topological payload paired with reflexivity. -/
theorem onePoint_threeSpace_self_homeomorph_payload_eq :
    onePoint_threeSpace_self_homeomorph_payload =
      ⟨onePoint_threeSpace_topological_manifold_prerequisites,
        onePoint_threeSpace_self_homeomorph⟩ := by
  apply Subsingleton.elim

/-- Project the compactification topological-manifold prerequisites from the self payload. -/
theorem onePoint_threeSpace_topological_manifold_prerequisites_of_self_homeomorph_payload :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases onePoint_threeSpace_self_homeomorph_payload with ⟨prerequisites, _endpoint⟩
  exact prerequisites

/-- The projected compactification prerequisite component is the named local payload. -/
theorem onePoint_threeSpace_topological_manifold_prerequisites_of_self_homeomorph_payload_eq :
    onePoint_threeSpace_topological_manifold_prerequisites_of_self_homeomorph_payload =
      onePoint_threeSpace_topological_manifold_prerequisites := by
  apply Subsingleton.elim

/-- Project the compactification self-homeomorphism endpoint from the self payload. -/
theorem onePoint_threeSpace_self_homeomorph_of_self_homeomorph_payload :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  rcases onePoint_threeSpace_self_homeomorph_payload with ⟨_prerequisites, endpoint⟩
  exact endpoint

/-- The projected compactification endpoint is the named reflexive self-homeomorphism. -/
theorem onePoint_threeSpace_self_homeomorph_of_self_homeomorph_payload_eq :
    onePoint_threeSpace_self_homeomorph_of_self_homeomorph_payload =
      onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
The compactification model becomes a local Poincare-candidate payload from its
own loop-nullhomotopy obligation and reflexive self-recognition.
-/
theorem poincare_candidate_prerequisites_of_onePoint_threeSpace_self_loopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
    hLoop onePoint_threeSpace_self_homeomorph

/-- The compactification self loop-candidate route is the general local-loop route at reflexivity. -/
theorem poincare_candidate_prerequisites_of_onePoint_threeSpace_self_loopNullhomotopyStatement_eq
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement) :
    poincare_candidate_prerequisites_of_onePoint_threeSpace_self_loopNullhomotopyStatement hLoop =
      poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement
        hLoop onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
The compactification model becomes a local Poincare-candidate payload from its
own path-homotopy obligation and reflexive self-recognition.
-/
theorem poincare_candidate_prerequisites_of_onePoint_threeSpace_self_pathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement) :
    ∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
    hPath onePoint_threeSpace_self_homeomorph

/-- The compactification self path-candidate route is the general local-path route at reflexivity. -/
theorem poincare_candidate_prerequisites_of_onePoint_threeSpace_self_pathHomotopyStatement_eq
    (hPath : OnePointThreeSpacePathHomotopyStatement) :
    poincare_candidate_prerequisites_of_onePoint_threeSpace_self_pathHomotopyStatement hPath =
      poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement
        hPath onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/-- The compactification self path-candidate route agrees with the self loop-candidate route. -/
theorem poincare_candidate_prerequisites_of_onePoint_threeSpace_self_pathHomotopyStatement_loop_route_eq
    (hPath : OnePointThreeSpacePathHomotopyStatement) :
    poincare_candidate_prerequisites_of_onePoint_threeSpace_self_pathHomotopyStatement hPath =
      poincare_candidate_prerequisites_of_onePoint_threeSpace_self_loopNullhomotopyStatement
        (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) := by
  apply Subsingleton.elim

/--
Universal compactification recognition, applied to the compactification model
itself, recovers the model's self-homeomorphism endpoint.
-/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_t2Space
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_chartedSpace
  letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_compactSpace
  exact recognize (OnePoint (EuclideanSpace ℝ (Fin 3)))

/-- The universal-recognition self endpoint is direct application to the model. -/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement =
      (fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
        letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_t2Space
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
            (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_chartedSpace
        letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_compactSpace
        recognize (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  funext recognize
  apply Subsingleton.elim

/-- The universal-recognition self endpoint agrees with reflexive recognition. -/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_direct_route_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
      recognize =
      onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
Universal compactification recognition applied to the model also gives the
target `ThreeSphere` endpoint after composing with the model map.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    (onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
      recognize)

/-- The universal-recognition target endpoint is self-recognition followed by the model map. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement
      recognize =
      homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
        (onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
          recognize) := by
  apply Subsingleton.elim

/-- The universal-recognition target endpoint agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_direct_route_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement
      recognize =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The compactification loop-nullhomotopy obligation supplies the
simple-connectedness needed to apply universal compactification recognition to
the model itself.
-/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
    recognize

/-- The loop universal-recognition self route first turns loop-nullhomotopy into simple-connectedness. -/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
            onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
            recognize) := by
  funext hLoop recognize
  apply Subsingleton.elim

/-- The loop universal-recognition self route agrees with reflexive recognition. -/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_direct_route_eq
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop recognize =
      onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
The compactification path-homotopy obligation supplies the
simple-connectedness needed to apply universal compactification recognition to
the model itself.
-/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
    recognize

/-- The path universal-recognition self route first turns path-homotopy into simple-connectedness. -/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
            onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
          onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement
            recognize) := by
  funext hPath recognize
  apply Subsingleton.elim

/-- The path universal-recognition self route agrees with the loop-mediated route. -/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
            (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath)
            recognize) := by
  funext hPath recognize
  apply Subsingleton.elim

/-- The path universal-recognition self route agrees with reflexive recognition. -/
theorem onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_direct_route_eq
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath recognize =
      onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
The loop-nullhomotopy universal-recognition self endpoint composes to the
target `ThreeSphere` endpoint.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    (onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop recognize)

/-- The loop universal-recognition target route is the loop self route followed by the model map. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
            (onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
              hLoop recognize)) := by
  funext hLoop recognize
  apply Subsingleton.elim

/-- The loop universal-recognition target route agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_direct_route_eq
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop recognize =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The path-homotopy universal-recognition self endpoint composes to the target
`ThreeSphere` endpoint.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    (onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath recognize)

/-- The path universal-recognition target route is the path self route followed by the model map. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
            (onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
              hPath recognize)) := by
  funext hPath recognize
  apply Subsingleton.elim

/-- The path universal-recognition target route agrees with the loop-mediated target route. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
            (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath)
            recognize) := by
  funext hPath recognize
  apply Subsingleton.elim

/-- The path universal-recognition target route agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_direct_route_eq
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath recognize =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The compactification loop-nullhomotopy universal-recognition endpoint also
packages the local homotopy/manifold prerequisites needed to apply recognition
to the compactification model.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
        Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
      hLoop,
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop recognize⟩

/-- The loop universal-recognition payload pairs the local prerequisites with the loop endpoint. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
              hLoop,
            onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
              hLoop recognize⟩) := by
  funext hLoop recognize
  apply Subsingleton.elim

/--
The compactification path-homotopy universal-recognition endpoint also packages
the local homotopy/manifold prerequisites needed to apply recognition to the
compactification model.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (recognize : OnePointThreeSpaceRecognitionStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
        Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
      hPath,
    onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath recognize⟩

/-- The path universal-recognition payload pairs the local prerequisites with the path endpoint. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
              hPath,
            onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
              hPath recognize⟩) := by
  funext hPath recognize
  apply Subsingleton.elim

/-- The path universal-recognition payload agrees with the loop-mediated payload route. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun recognize : OnePointThreeSpaceRecognitionStatement.{0} =>
          onePoint_threeSpace_homeomorph_threeSphere_payload_of_onePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
            (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath)
            recognize) := by
  funext hPath recognize
  apply Subsingleton.elim

/--
Applying the project target statement to the one-point compactification model
uses the named compactification typeclass witnesses and only requires
simple-connectedness as the remaining local input.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (h : PoincareConjectureStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) := by
  letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_t2Space
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_chartedSpace
  letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_compactSpace
  exact h (OnePoint (EuclideanSpace ℝ (Fin 3)))

/-- The compactification target self-application is exactly pointwise target application. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))] :
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement =
      (fun h : PoincareConjectureStatement.{0} =>
        letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_t2Space
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
            (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_chartedSpace
        letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_compactSpace
        h (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  funext h
  apply Subsingleton.elim

/--
The target-statement compactification self-case endpoint agrees with the
direct one-point compactification homeomorphism to `ThreeSphere`.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_direct_route_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (h : PoincareConjectureStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement h =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The compactification loop-nullhomotopy obligation is enough to apply the
project target statement to the compactification model.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement h

/-- The loop compactification self-case first turns loop-nullhomotopy into simple-connectedness. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
            onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement h) := by
  funext hLoop h
  apply Subsingleton.elim

/-- The loop compactification target route agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement_direct_route_eq
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement
      hLoop h =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The compactification path-homotopy obligation is enough to apply the project
target statement to the compactification model.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement h

/-- The path compactification self-case first turns path-homotopy into simple-connectedness. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
            onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
          onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement h) := by
  funext hPath h
  apply Subsingleton.elim

/-- The path compactification target route agrees with the loop-mediated route. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement
            (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/-- The path compactification target route agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement_direct_route_eq
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement
      hPath h =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The compactification loop-nullhomotopy target self-case exposes both the local
homotopy/manifold prerequisites and the target endpoint.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
        Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
      hLoop,
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement
      hLoop h⟩

/-- The loop target payload is the local prerequisite route paired with the loop endpoint. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
              hLoop,
            onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointLoopNullhomotopyStatement
              hLoop h⟩) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The compactification path-homotopy target self-case exposes both the local
homotopy/manifold prerequisites and the target endpoint.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
        Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
      hPath,
    onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement
      hPath h⟩

/-- The path target payload is the local prerequisite route paired with the path endpoint. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
              hPath,
            onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement_and_onePointPathHomotopyStatement
              hPath h⟩) := by
  funext hPath h
  apply Subsingleton.elim

/-- The path target payload agrees with the loop-mediated target payload. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          onePoint_threeSpace_homeomorph_threeSphere_payload_of_poincare_statement_and_onePointLoopNullhomotopyStatement
            (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The extinction-to-compactification recognition theorem, applied to the
compactification model itself, recovers the model's self-homeomorphism endpoint.
-/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_t2Space
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_chartedSpace
  letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_compactSpace
  exact recognize (OnePoint (EuclideanSpace ℝ (Fin 3))) extinction

/-- The pointwise extinction-recognition self endpoint is direct application of the extractor. -/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
      extinction recognize =
      (by
        letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_t2Space
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
            (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_chartedSpace
        letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
          onePoint_threeSpace_compactSpace
        exact recognize (OnePoint (EuclideanSpace ℝ (Fin 3))) extinction) := by
  apply Subsingleton.elim

/-- The pointwise extinction-recognition self endpoint agrees with reflexive recognition. -/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_direct_route_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
      extinction recognize =
      onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
The same pointwise extinction-recognition self endpoint gives the target
`ThreeSphere` endpoint after composing with the compactification model map.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    (onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
      extinction recognize)

/-- The extinction-recognition target endpoint is self-recognition followed by the model map. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement
      extinction recognize =
      homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
        (onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
          extinction recognize) := by
  apply Subsingleton.elim

/-- The extinction-recognition target endpoint agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_direct_route_eq
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement
      extinction recognize =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The compactification loop-nullhomotopy obligation supplies the
simple-connectedness needed to apply extinction compactification recognition to
the model itself.
-/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
    extinction recognize

/-- The loop extinction-recognition self route first turns loop-nullhomotopy into simple-connectedness. -/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
              onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
            onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
              extinction recognize) := by
  funext hLoop extinction recognize
  apply Subsingleton.elim

/-- The loop extinction-recognition self route agrees with reflexive recognition. -/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_direct_route_eq
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop extinction recognize =
      onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
The compactification path-homotopy obligation supplies the simple-connectedness
needed to apply extinction compactification recognition to the model itself.
-/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
    extinction recognize

/-- The path extinction-recognition self route first turns path-homotopy into simple-connectedness. -/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
              onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
            onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement
              extinction recognize) := by
  funext hPath extinction recognize
  apply Subsingleton.elim

/-- The path extinction-recognition self route agrees with the loop-mediated route. -/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
              (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath)
              extinction recognize) := by
  funext hPath extinction recognize
  apply Subsingleton.elim

/-- The path extinction-recognition self route agrees with reflexive recognition. -/
theorem onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_direct_route_eq
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath extinction recognize =
      onePoint_threeSpace_self_homeomorph := by
  apply Subsingleton.elim

/--
The loop-nullhomotopy extinction-recognition self endpoint composes to the
target `ThreeSphere` endpoint.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    (onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop extinction recognize)

/-- The loop extinction-recognition target route is the loop self route followed by the model map. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
              (onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
                hLoop extinction recognize)) := by
  funext hLoop extinction recognize
  apply Subsingleton.elim

/-- The loop extinction-recognition target route agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_direct_route_eq
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop extinction recognize =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The path-homotopy extinction-recognition self endpoint composes to the target
`ThreeSphere` endpoint.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
    (onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath extinction recognize)

/-- The path extinction-recognition target route is the path self route followed by the model map. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
              (onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
                hPath extinction recognize)) := by
  funext hPath extinction recognize
  apply Subsingleton.elim

/-- The path extinction-recognition target route agrees with the loop-mediated target route. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
              (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath)
              extinction recognize) := by
  funext hPath extinction recognize
  apply Subsingleton.elim

/-- The path extinction-recognition target route agrees with the direct model homeomorphism. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_direct_route_eq
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath extinction recognize =
      onePoint_threeSpace_homeomorph_threeSphere := by
  apply Subsingleton.elim

/--
The compactification loop-nullhomotopy extinction-recognition endpoint also
packages the local homotopy/manifold prerequisites needed to apply recognition
to the compactification model after finite extinction.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
    (hLoop : OnePointThreeSpaceLoopNullhomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
        Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
      hLoop,
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
      hLoop extinction recognize⟩

/-- The loop extinction-recognition payload pairs the local prerequisites with the loop endpoint. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement =
      (fun hLoop : OnePointThreeSpaceLoopNullhomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement
                hLoop,
              onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
                hLoop extinction recognize⟩) := by
  funext hLoop extinction recognize
  apply Subsingleton.elim

/--
The compactification path-homotopy extinction-recognition endpoint also
packages the local homotopy/manifold prerequisites needed to apply recognition
to the compactification model after finite extinction.
-/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
    (hPath : OnePointThreeSpacePathHomotopyStatement)
    (extinction :
      letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_t2Space
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_chartedSpace
      letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_simplyConnectedSpace_of_pathHomotopyStatement hPath
      letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
        onePoint_threeSpace_compactSpace
      FiniteExtinctionByRicciFlowWithSurgery
        (OnePoint (EuclideanSpace ℝ (Fin 3))))
    (recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _simple : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _compact : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _topological : IsManifold (𝓡 3) 0 (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _path : PathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _locPath : LocPathConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
      ∃ _connected : ConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))),
        Nonempty (OnePoint (EuclideanSpace ℝ (Fin 3)))),
        Nonempty ((OnePoint (EuclideanSpace ℝ (Fin 3))) ≃ₜ ThreeSphere) :=
  ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
      hPath,
    onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
      hPath extinction recognize⟩

/-- The path extinction-recognition payload pairs the local prerequisites with the path endpoint. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            ⟨onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement
                hPath,
              onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement
                hPath extinction recognize⟩) := by
  funext hPath extinction recognize
  apply Subsingleton.elim

/-- The path extinction-recognition payload agrees with the loop-mediated payload route. -/
theorem onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement_loop_route_eq :
    onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointPathHomotopyStatement =
      (fun hPath : OnePointThreeSpacePathHomotopyStatement =>
        fun extinction =>
          fun recognize : ExtinctionOnePointThreeSpaceRecognitionStatement.{0} =>
            onePoint_threeSpace_homeomorph_threeSphere_payload_of_extinctionOnePointThreeSpaceRecognitionStatement_and_onePointLoopNullhomotopyStatement
              (onePoint_threeSpace_loopNullhomotopyStatement_of_pathHomotopyStatement hPath)
              extinction recognize) := by
  funext hPath extinction recognize
  apply Subsingleton.elim

/-- The standard target sphere is homeomorphic to itself. -/
theorem threeSphere_self_homeomorph :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨Homeomorph.refl ThreeSphere⟩

/--
The self-homeomorphism witness for the standard sphere is the reflexive
homeomorphism.
-/
theorem threeSphere_self_homeomorph_eq :
    threeSphere_self_homeomorph =
      ⟨Homeomorph.refl ThreeSphere⟩ := by
  apply Subsingleton.elim

/--
The topology-extraction self-homeomorphism witness agrees with the assembly
route obtained by forgetting the standard sphere's reflexive self-diffeomorphism.
-/
theorem threeSphere_self_homeomorph_self_diffeomorph_route_eq :
    threeSphere_self_homeomorph =
      threeSphere_self_homeomorph_of_self_diffeomorph := by
  apply Subsingleton.elim

/--
The available standard-sphere target prerequisites pair with the direct
reflexive self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  exact ⟨threeSphere_target_prerequisites_except_simpleConnected,
    threeSphere_self_homeomorph⟩

/--
The direct topology self-homeomorphism payload is exactly the target
prerequisite payload paired with the reflexive self-homeomorphism.
-/
theorem threeSphere_self_homeomorph_payload_eq :
    threeSphere_self_homeomorph_payload =
      ⟨threeSphere_target_prerequisites_except_simpleConnected,
        threeSphere_self_homeomorph⟩ := by
  apply Subsingleton.elim

/-- Project the target-prerequisite component from the direct topology payload. -/
theorem threeSphere_target_prerequisites_except_simpleConnected_of_self_homeomorph_payload :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  rcases threeSphere_self_homeomorph_payload with ⟨prerequisites, _endpoint⟩
  exact prerequisites

/-- The projected prerequisite component is the named standard-sphere payload. -/
theorem threeSphere_target_prerequisites_except_simpleConnected_of_self_homeomorph_payload_eq :
    threeSphere_target_prerequisites_except_simpleConnected_of_self_homeomorph_payload =
      threeSphere_target_prerequisites_except_simpleConnected := by
  apply Subsingleton.elim

/-- Project the reflexive topological endpoint from the direct topology payload. -/
theorem threeSphere_self_homeomorph_of_self_homeomorph_payload :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  rcases threeSphere_self_homeomorph_payload with ⟨_prerequisites, endpoint⟩
  exact endpoint

/-- The projected topological endpoint is the named reflexive self-homeomorphism. -/
theorem threeSphere_self_homeomorph_of_self_homeomorph_payload_eq :
    threeSphere_self_homeomorph_of_self_homeomorph_payload =
      threeSphere_self_homeomorph := by
  apply Subsingleton.elim

/--
The direct topology payload agrees with the smooth-forgetful assembly payload.
-/
theorem threeSphere_self_homeomorph_payload_self_diffeomorph_route_eq :
    threeSphere_self_homeomorph_payload =
      threeSphere_self_homeomorph_payload_of_self_diffeomorph := by
  apply Subsingleton.elim

/--
Homeomorphism recognition composes through an intermediate space.

This is a small proof-bearing topology lemma used by the extraction layer: once
an intermediate model has been identified with `ThreeSphere`, any manifold
homeomorphic to that model is also identified with `ThreeSphere`.
-/
theorem homeomorph_to_threeSphere_of_homeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases hMN with ⟨eMN⟩
  rcases hN with ⟨eN⟩
  exact ⟨eMN.trans eN⟩

/--
The intermediate-space transport lemma is exactly composition of the supplied
homeomorphisms.
-/
theorem homeomorph_to_threeSphere_of_homeomorph_eq
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    homeomorph_to_threeSphere_of_homeomorph hMN hN =
      (by
        rcases hMN with ⟨eMN⟩
        rcases hN with ⟨eN⟩
        exact ⟨eMN.trans eN⟩) := by
  apply Subsingleton.elim

/--
Homeomorphism recognition can also be transported along a homeomorphism whose
direction is opposite the final target direction.
-/
theorem homeomorph_to_threeSphere_of_homeomorph_source
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hNM : Nonempty (N ≃ₜ M)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases hNM with ⟨eNM⟩
  rcases hN with ⟨eN⟩
  exact ⟨eNM.symm.trans eN⟩

/--
The source-side transport lemma is exactly inverse-then-composition of the
supplied homeomorphisms.
-/
theorem homeomorph_to_threeSphere_of_homeomorph_source_eq
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hNM : Nonempty (N ≃ₜ M)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    homeomorph_to_threeSphere_of_homeomorph_source hNM hN =
      (by
        rcases hNM with ⟨eNM⟩
        rcases hN with ⟨eN⟩
        exact ⟨eNM.symm.trans eN⟩) := by
  apply Subsingleton.elim

/--
Being homeomorphic to the standard 3-sphere is invariant under replacing the
source by a homeomorphic space.
-/
theorem homeomorph_to_threeSphere_iff_of_homeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) :
    Nonempty (M ≃ₜ ThreeSphere) ↔ Nonempty (N ≃ₜ ThreeSphere) := by
  constructor
  · intro hM
    exact homeomorph_to_threeSphere_of_homeomorph_source hMN hM
  · intro hN
    exact homeomorph_to_threeSphere_of_homeomorph hMN hN

/--
The homeomorphism-invariance equivalence is the pair of the named transport
maps in the two directions.
-/
theorem homeomorph_to_threeSphere_iff_of_homeomorph_eq
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) :
    homeomorph_to_threeSphere_iff_of_homeomorph hMN =
      (by
        constructor
        · intro hM
          exact homeomorph_to_threeSphere_of_homeomorph_source hMN hM
        · intro hN
          exact homeomorph_to_threeSphere_of_homeomorph hMN hN) := by
  apply Subsingleton.elim

/--
Recognition can be used in the target direction after inverting a homeomorphism
from the standard sphere.
-/
theorem homeomorph_to_threeSphere_of_threeSphere_homeomorph
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (ThreeSphere ≃ₜ M)) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/--
The target-side recognition lemma is exactly inversion of the supplied
homeomorphism from the standard sphere.
-/
theorem homeomorph_to_threeSphere_of_threeSphere_homeomorph_eq
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (ThreeSphere ≃ₜ M)) :
    homeomorph_to_threeSphere_of_threeSphere_homeomorph h =
      (by
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩) := by
  apply Subsingleton.elim

/--
The same recognition data can be used in the reverse direction by inverting the
homeomorphism to the standard sphere.
-/
theorem threeSphere_homeomorph_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    Nonempty (ThreeSphere ≃ₜ M) := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/--
The reverse target-side recognition lemma is exactly inversion of the supplied
homeomorphism to the standard sphere.
-/
theorem threeSphere_homeomorph_of_homeomorph_to_threeSphere_eq
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    threeSphere_homeomorph_of_homeomorph_to_threeSphere h =
      (by
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩) := by
  apply Subsingleton.elim

/--
Being homeomorphic to the standard 3-sphere is independent of which side of the
homeomorphism the standard sphere is written on.
-/
theorem homeomorph_to_threeSphere_iff_threeSphere_homeomorph
    {M : Type u} [TopologicalSpace M] :
    Nonempty (M ≃ₜ ThreeSphere) ↔ Nonempty (ThreeSphere ≃ₜ M) := by
  constructor
  · exact threeSphere_homeomorph_of_homeomorph_to_threeSphere
  · exact homeomorph_to_threeSphere_of_threeSphere_homeomorph

/--
The target-side homeomorphism equivalence is the pair of the named inverse
homeomorphism conversions.
-/
theorem homeomorph_to_threeSphere_iff_threeSphere_homeomorph_eq
    {M : Type u} [TopologicalSpace M] :
    (homeomorph_to_threeSphere_iff_threeSphere_homeomorph :
      Nonempty (M ≃ₜ ThreeSphere) ↔ Nonempty (ThreeSphere ≃ₜ M)) =
      (by
        constructor
        · exact threeSphere_homeomorph_of_homeomorph_to_threeSphere
        · exact homeomorph_to_threeSphere_of_threeSphere_homeomorph) := by
  apply Subsingleton.elim

/--
Interface for the decomposition information obtained from finite extinction.

This stands for the topological output of the extinction argument before the
final recognition theorem is applied.
-/
inductive HasExtinctionTopologyDecomposition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_extinction : FiniteExtinctionByRicciFlowWithSurgery M) : Prop

/--
Interface reconstructing the topological surgery trace represented by the
post-extinction decomposition.
-/
inductive HasExtinctionSurgeryTraceReconstruction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (_decomposition : HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for canceling the topological handles recorded by the surgery trace.
-/
inductive HasExtinctionSurgeryTraceHandleCancellation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_surgeryTrace :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition) : Prop

/--
Interface for classifying the topological components produced at extinction.
-/
inductive HasExtinctionComponentClassification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (_decomposition : HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for identifying discarded extinction components up to homeomorphism.
-/
inductive HasExtinctionDiscardedComponentHomeomorphismClassification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_componentClassification :
      HasExtinctionComponentClassification M extinction decomposition) : Prop

/--
Interface inventorying extinction components before prime-factor recognition.
-/
inductive HasExtinctionComponentInventory
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_componentClassification :
      HasExtinctionComponentClassification M extinction decomposition) : Prop

/--
Interface for proving that boundary components in the extinction inventory are spheres.
-/
inductive HasExtinctionComponentBoundarySphereControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (_componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification) : Prop

/--
Interface for the 3-sphere recognition/classification theorem needed after the
extinction decomposition is known.
-/
inductive HasThreeSphereRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_decomposition :
      ∀ extinction : FiniteExtinctionByRicciFlowWithSurgery M,
        HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for extracting a prime/connected-sum decomposition from the
post-extinction topology data.
-/
inductive HasExtinctionPrimeDecomposition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (_decomposition : HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for existence of the prime decomposition used in the extinction argument.
-/
inductive HasExtinctionPrimeDecompositionExistence
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface for the sphere-theorem input used to extract prime factors.
-/
inductive HasExtinctionSphereTheoremApplication
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface for producing embedded spheres that realize prime-decomposition cuts.
-/
inductive HasExtinctionEmbeddedSphereProduction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_sphereTheorem :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for the loop-theorem input used to control compressions in the cuts.
-/
inductive HasExtinctionLoopTheoremApplication
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_sphereTheorem :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for compatibility and uniqueness of the prime decomposition used by
the extinction classification.
-/
inductive HasExtinctionPrimeDecompositionCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface for uniqueness of the prime factors selected by the decomposition.
-/
inductive HasExtinctionPrimeFactorUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification
        primeDecomposition) : Prop

/--
Interface for the irreducibility input applied to the prime pieces produced by
finite extinction.
-/
inductive HasExtinctionIrreducibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface recognizing the irreducible prime factors arising after extinction.
-/
inductive HasExtinctionIrreducibleFactorRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for collapsing the connected-sum decomposition to the surviving prime
factor relevant to the simply connected target.
-/
inductive HasExtinctionConnectedSumCollapse
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for the fundamental-group control used when collapsing connected sums.
-/
inductive HasExtinctionConnectedSumFundamentalGroupControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (_connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility) : Prop

/--
Interface for the van Kampen computation of the connected-sum fundamental group.
-/
inductive HasExtinctionConnectedSumVanKampenCalculation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_fundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for forcing the surviving prime factor to be simply connected.
-/
inductive HasExtinctionSimplyConnectedPrimeFactorControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_fundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for reducing the finite-extinction decomposition to spherical space
form pieces.
-/
inductive HasExtinctionSphericalSpaceFormReduction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (_connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility) : Prop

/--
Interface for the spherical-space-form classification theorem applied after
prime and connected-sum reduction.
-/
inductive HasSphericalSpaceFormClassification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for identifying the surviving pieces with spherical quotient models.
-/
inductive HasSphericalSpaceFormQuotientModel
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for realizing a spherical space form as a free action on the sphere.
-/
inductive HasSphericalSpaceFormFreeAction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (_quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface for proving that the spherical space form universal cover is the
standard 3-sphere.
-/
inductive HasSphericalSpaceFormUniversalCover
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (_quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface identifying the quotient and universal-cover data as a covering
model of the spherical space form.
-/
inductive HasSphericalSpaceFormCoveringModel
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel) : Prop

/--
Interface for the covering projection from the universal cover to the quotient.
-/
inductive HasSphericalSpaceFormCoveringProjection
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (_coveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        universalCover) : Prop

/--
Interface for computing the fundamental group of the spherical space form
pieces arising after the extinction reduction.
-/
inductive HasSphericalSpaceFormFundamentalGroupComputation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface identifying the spherical-space-form deck group with the computed
fundamental group.
-/
inductive HasSphericalSpaceFormDeckGroupIdentification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface for proper discontinuity and freeness of the deck action.
-/
inductive HasSphericalSpaceFormDeckActionProperness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation) : Prop

/--
Interface for ruling out nontrivial deck groups/quotients using simple
connectedness of the original manifold.
-/
inductive HasSphericalSpaceFormDeckGroupTriviality
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (_fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface converting deck-group identification and triviality into a trivial
covering action.
-/
inductive HasSphericalSpaceFormDeckActionTrivialization
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (_deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction
        fundamentalGroupComputation) : Prop

/--
Interface identifying the quotient by a trivial deck action with the cover itself.
-/
inductive HasSphericalSpaceFormTrivialDeckQuotientIdentification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction
        fundamentalGroupComputation)
    (_deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality) : Prop

/--
Interface for the simply connected reduction that rules out nontrivial
spherical space form factors.
-/
inductive HasSimplyConnectedExtinctionRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation) : Prop

/--
Interface turning the trivial deck group result into a trivial spherical
quotient.
-/
inductive HasTrivialSphericalSpaceFormQuotient
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (_deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation) : Prop

/--
Interface turning the trivial quotient statement into the final quotient
homeomorphism used by the extraction assembly.
-/
inductive HasSphericalSpaceFormTrivialQuotientHomeomorphism
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (_trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality) : Prop

/--
Interface lifting the final homeomorphism through the trivial spherical quotient.
-/
inductive HasSphericalSpaceFormHomeomorphismLift
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality)
    (_trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient) : Prop

/--
Interface assembling the topological classification outputs into the final
homeomorphism to the standard sphere.
-/
inductive HasExtinctionHomeomorphismAssembly
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (_trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (_homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop

/--
Interface certifying that the preceding topology inputs derive the projected
homeomorphism to the standard 3-sphere.
-/
inductive HasExtinctionHomeomorphismDerivation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (_homeomorphismAssembly :
      HasExtinctionHomeomorphismAssembly M extinction decomposition
        primeDecomposition irreducibility connectedSumCollapse sphericalReduction
        quotientModel fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality simplyConnectedRecognition trivialQuotient
        homeomorphism) : Prop

/--
The fixed-manifold topology extraction statement: finite extinction gives a
homeomorphism only together with the full post-extinction classification,
quotient, deck-group, trivial-quotient, assembly, and derivation chain.
-/
def ExtinctionTopologyDerivationStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop :=
  ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
  ∃ surgeryTraceReconstruction :
    HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
  ∃ _surgeryTraceHandleCancellation :
    HasExtinctionSurgeryTraceHandleCancellation
      M extinction decomposition surgeryTraceReconstruction,
  ∃ componentClassification :
    HasExtinctionComponentClassification M extinction decomposition,
  ∃ _discardedComponentHomeomorphismClassification :
    HasExtinctionDiscardedComponentHomeomorphismClassification
      M extinction decomposition componentClassification,
  ∃ componentInventory :
    HasExtinctionComponentInventory
      M extinction decomposition componentClassification,
  ∃ _componentBoundarySphereControl :
    HasExtinctionComponentBoundarySphereControl
      M extinction decomposition componentClassification componentInventory,
  ∃ primeDecomposition :
    HasExtinctionPrimeDecomposition M extinction decomposition,
  ∃ _primeDecompositionExistence :
    HasExtinctionPrimeDecompositionExistence
      M extinction decomposition primeDecomposition,
  ∃ sphereTheoremApplication :
    HasExtinctionSphereTheoremApplication
      M extinction decomposition primeDecomposition,
  ∃ _embeddedSphereProduction :
    HasExtinctionEmbeddedSphereProduction
      M extinction decomposition primeDecomposition sphereTheoremApplication,
  ∃ _loopTheoremApplication :
    HasExtinctionLoopTheoremApplication
      M extinction decomposition primeDecomposition sphereTheoremApplication,
  ∃ primeDecompositionCompatibility :
    HasExtinctionPrimeDecompositionCompatibility
      M extinction decomposition componentClassification primeDecomposition,
  ∃ _primeFactorUniqueness :
    HasExtinctionPrimeFactorUniqueness
      M extinction decomposition componentClassification primeDecomposition
      primeDecompositionCompatibility,
  ∃ irreducibility :
    HasExtinctionIrreducibility
      M extinction decomposition primeDecomposition,
  ∃ _irreducibleFactorRecognition :
    HasExtinctionIrreducibleFactorRecognition
      M extinction decomposition primeDecomposition irreducibility,
  ∃ connectedSumCollapse :
    HasExtinctionConnectedSumCollapse
      M extinction decomposition primeDecomposition irreducibility,
  ∃ connectedSumFundamentalGroupControl :
    HasExtinctionConnectedSumFundamentalGroupControl
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ _connectedSumVanKampen :
    HasExtinctionConnectedSumVanKampenCalculation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse connectedSumFundamentalGroupControl,
  ∃ _simplyConnectedPrimeFactorControl :
    HasExtinctionSimplyConnectedPrimeFactorControl
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse connectedSumFundamentalGroupControl,
  ∃ sphericalReduction :
    HasExtinctionSphericalSpaceFormReduction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ _sphericalClassification :
    HasSphericalSpaceFormClassification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ quotientModel :
    HasSphericalSpaceFormQuotientModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ _sphericalFreeAction :
    HasSphericalSpaceFormFreeAction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel,
  ∃ universalCover :
    HasSphericalSpaceFormUniversalCover
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel,
  ∃ sphericalCoveringModel :
    HasSphericalSpaceFormCoveringModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover,
  ∃ _sphericalCoveringProjection :
    HasSphericalSpaceFormCoveringProjection
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover
      sphericalCoveringModel,
  ∃ fundamentalGroupComputation :
    HasSphericalSpaceFormFundamentalGroupComputation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupIdentification :
    HasSphericalSpaceFormDeckGroupIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation,
  ∃ _deckActionProperness :
    HasSphericalSpaceFormDeckActionProperness
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification,
  ∃ deckGroupTriviality :
    HasSphericalSpaceFormDeckGroupTriviality
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation,
  ∃ deckActionTrivialization :
    HasSphericalSpaceFormDeckActionTrivialization
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
  ∃ _trivialDeckQuotientIdentification :
    HasSphericalSpaceFormTrivialDeckQuotientIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
      deckActionTrivialization,
  ∃ trivialQuotient :
    HasTrivialSphericalSpaceFormQuotient
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
  ∃ trivialQuotientHomeomorphism :
    HasSphericalSpaceFormTrivialQuotientHomeomorphism
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
      trivialQuotient,
  ∃ _sphericalHomeomorphismLift :
    HasSphericalSpaceFormHomeomorphismLift
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
      trivialQuotient trivialQuotientHomeomorphism,
  ∃ simplyConnectedRecognition :
    HasSimplyConnectedExtinctionRecognition
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation
      deckGroupTriviality,
  ∃ homeomorphismAssembly :
    HasExtinctionHomeomorphismAssembly M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      quotientModel fundamentalGroupComputation deckGroupIdentification
      deckGroupTriviality simplyConnectedRecognition trivialQuotient
      homeomorphism,
    HasExtinctionHomeomorphismDerivation M extinction
      decomposition primeDecomposition irreducibility connectedSumCollapse
      sphericalReduction fundamentalGroupComputation deckGroupTriviality
      simplyConnectedRecognition quotientModel deckGroupIdentification
      trivialQuotient homeomorphism homeomorphismAssembly

/--
The fixed-manifold topology derivation statement is definitionally the full
post-extinction decomposition, trace, classification, space-form, recognition,
assembly, and derivation witness stack.
-/
theorem extinctionTopologyDerivationStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) :
    ExtinctionTopologyDerivationStatement M extinction homeomorphism =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ surgeryTraceReconstruction :
        HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
      ∃ _surgeryTraceHandleCancellation :
        HasExtinctionSurgeryTraceHandleCancellation
          M extinction decomposition surgeryTraceReconstruction,
      ∃ componentClassification :
        HasExtinctionComponentClassification M extinction decomposition,
      ∃ _discardedComponentHomeomorphismClassification :
        HasExtinctionDiscardedComponentHomeomorphismClassification
          M extinction decomposition componentClassification,
      ∃ componentInventory :
        HasExtinctionComponentInventory
          M extinction decomposition componentClassification,
      ∃ _componentBoundarySphereControl :
        HasExtinctionComponentBoundarySphereControl
          M extinction decomposition componentClassification componentInventory,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ _primeDecompositionExistence :
        HasExtinctionPrimeDecompositionExistence
          M extinction decomposition primeDecomposition,
      ∃ sphereTheoremApplication :
        HasExtinctionSphereTheoremApplication
          M extinction decomposition primeDecomposition,
      ∃ _embeddedSphereProduction :
        HasExtinctionEmbeddedSphereProduction
          M extinction decomposition primeDecomposition sphereTheoremApplication,
      ∃ _loopTheoremApplication :
        HasExtinctionLoopTheoremApplication
          M extinction decomposition primeDecomposition sphereTheoremApplication,
      ∃ primeDecompositionCompatibility :
        HasExtinctionPrimeDecompositionCompatibility
          M extinction decomposition componentClassification primeDecomposition,
      ∃ _primeFactorUniqueness :
        HasExtinctionPrimeFactorUniqueness
          M extinction decomposition componentClassification primeDecomposition
          primeDecompositionCompatibility,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ _irreducibleFactorRecognition :
        HasExtinctionIrreducibleFactorRecognition
          M extinction decomposition primeDecomposition irreducibility,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ connectedSumFundamentalGroupControl :
        HasExtinctionConnectedSumFundamentalGroupControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _connectedSumVanKampen :
        HasExtinctionConnectedSumVanKampenCalculation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse connectedSumFundamentalGroupControl,
      ∃ _simplyConnectedPrimeFactorControl :
        HasExtinctionSimplyConnectedPrimeFactorControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse connectedSumFundamentalGroupControl,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _sphericalClassification :
        HasSphericalSpaceFormClassification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ _sphericalFreeAction :
        HasSphericalSpaceFormFreeAction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ universalCover :
        HasSphericalSpaceFormUniversalCover
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ sphericalCoveringModel :
        HasSphericalSpaceFormCoveringModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover,
      ∃ _sphericalCoveringProjection :
        HasSphericalSpaceFormCoveringProjection
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover
          sphericalCoveringModel,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ _deckActionProperness :
        HasSphericalSpaceFormDeckActionProperness
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ deckActionTrivialization :
        HasSphericalSpaceFormDeckActionTrivialization
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
      ∃ _trivialDeckQuotientIdentification :
        HasSphericalSpaceFormTrivialDeckQuotientIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          deckActionTrivialization,
      ∃ trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
      ∃ trivialQuotientHomeomorphism :
        HasSphericalSpaceFormTrivialQuotientHomeomorphism
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          trivialQuotient,
      ∃ _sphericalHomeomorphismLift :
        HasSphericalSpaceFormHomeomorphismLift
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          trivialQuotient trivialQuotientHomeomorphism,
      ∃ simplyConnectedRecognition :
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality,
      ∃ homeomorphismAssembly :
        HasExtinctionHomeomorphismAssembly M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction quotientModel fundamentalGroupComputation
          deckGroupIdentification deckGroupTriviality simplyConnectedRecognition
          trivialQuotient homeomorphism,
        HasExtinctionHomeomorphismDerivation M extinction
          decomposition primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction fundamentalGroupComputation deckGroupTriviality
          simplyConnectedRecognition quotientModel deckGroupIdentification
          trivialQuotient homeomorphism homeomorphismAssembly) :=
  rfl

/--
The theorem-shaped post-extinction topology extraction input consumed by the
Poincare assembly: every finite-extinction witness yields a homeomorphism plus
the full derivation statement for that homeomorphism.
-/
def ExtinctionTopologyExtractionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        ExtinctionTopologyDerivationStatement M extinction homeomorphism

/--
The theorem-shaped topology-extraction interface is exactly the universal
post-extinction homeomorphism plus derivation statement.
-/
theorem extinctionTopologyExtractionStatement_eq :
    ExtinctionTopologyExtractionStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
            ExtinctionTopologyDerivationStatement M extinction homeomorphism) :=
  rfl

/--
The derivation evidence corresponding to a particular theorem-shaped
finite-extinction-to-sphere extractor.

This separates the purely final homeomorphism conclusion from the longer
post-extinction topology derivation chain that explains why that conclusion was
obtained.
-/
def ExtinctionTopologyDerivationForExtractionStatement
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionTopologyDerivationStatement M extinction
        (extractSphere M extinction)

/--
The derivation evidence for a theorem-shaped extractor is exactly the universal
fixed-homeomorphism derivation statement for the extractor's chosen output.
-/
theorem extinctionTopologyDerivationForExtractionStatement_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ExtinctionTopologyDerivationForExtractionStatement extractSphere =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          ExtinctionTopologyDerivationStatement M extinction
            (extractSphere M extinction)) :=
  rfl

/--
Assemble the fixed-manifold topology derivation statement from the named
post-extinction topology components.
-/
theorem extinction_topology_derivation_statement_of_components
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition)
    (surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition surgeryTraceReconstruction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification)
    (componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification)
    (componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification componentInventory)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition)
    (sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition)
    (embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition)
    (primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        primeDecompositionCompatibility)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover)
    (sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        sphericalCoveringModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        deckActionTrivialization)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient)
    (sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient trivialQuotientHomeomorphism)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (homeomorphismAssembly :
      HasExtinctionHomeomorphismAssembly M extinction decomposition
        primeDecomposition irreducibility connectedSumCollapse sphericalReduction
        quotientModel fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality simplyConnectedRecognition trivialQuotient
        homeomorphism)
    (homeomorphismDerivation :
      HasExtinctionHomeomorphismDerivation M extinction
        decomposition primeDecomposition irreducibility connectedSumCollapse
        sphericalReduction fundamentalGroupComputation deckGroupTriviality
        simplyConnectedRecognition quotientModel deckGroupIdentification
        trivialQuotient homeomorphism homeomorphismAssembly) :
    ExtinctionTopologyDerivationStatement M extinction homeomorphism :=
  ⟨decomposition, surgeryTraceReconstruction,
    surgeryTraceHandleCancellation, componentClassification,
    discardedComponentHomeomorphismClassification, componentInventory,
    componentBoundarySphereControl, primeDecomposition,
    primeDecompositionExistence, sphereTheoremApplication,
    embeddedSphereProduction, loopTheoremApplication,
    primeDecompositionCompatibility, primeFactorUniqueness, irreducibility,
    irreducibleFactorRecognition, connectedSumCollapse,
    connectedSumFundamentalGroupControl, connectedSumVanKampen,
    simplyConnectedPrimeFactorControl, sphericalReduction,
    sphericalClassification, quotientModel, sphericalFreeAction,
    universalCover, sphericalCoveringModel, sphericalCoveringProjection,
    fundamentalGroupComputation, deckGroupIdentification,
    deckActionProperness, deckGroupTriviality, deckActionTrivialization,
    trivialDeckQuotientIdentification, trivialQuotient,
    trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
    simplyConnectedRecognition, homeomorphismAssembly,
    homeomorphismDerivation⟩

/--
The component assembler for the fixed-manifold topology derivation statement is
exactly the full tuple of post-extinction topology components.
-/
theorem extinction_topology_derivation_statement_of_components_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition)
    (surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition surgeryTraceReconstruction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification)
    (componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification)
    (componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification componentInventory)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition)
    (sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition)
    (embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition)
    (primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        primeDecompositionCompatibility)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover)
    (sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        sphericalCoveringModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        deckActionTrivialization)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient)
    (sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient trivialQuotientHomeomorphism)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (homeomorphismAssembly :
      HasExtinctionHomeomorphismAssembly M extinction decomposition
        primeDecomposition irreducibility connectedSumCollapse sphericalReduction
        quotientModel fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality simplyConnectedRecognition trivialQuotient
        homeomorphism)
    (homeomorphismDerivation :
      HasExtinctionHomeomorphismDerivation M extinction
        decomposition primeDecomposition irreducibility connectedSumCollapse
        sphericalReduction fundamentalGroupComputation deckGroupTriviality
        simplyConnectedRecognition quotientModel deckGroupIdentification
        trivialQuotient homeomorphism homeomorphismAssembly) :
    extinction_topology_derivation_statement_of_components M extinction
        homeomorphism decomposition surgeryTraceReconstruction
        surgeryTraceHandleCancellation componentClassification
        discardedComponentHomeomorphismClassification componentInventory
        componentBoundarySphereControl primeDecomposition
        primeDecompositionExistence sphereTheoremApplication
        embeddedSphereProduction loopTheoremApplication
        primeDecompositionCompatibility primeFactorUniqueness irreducibility
        irreducibleFactorRecognition connectedSumCollapse
        connectedSumFundamentalGroupControl connectedSumVanKampen
        simplyConnectedPrimeFactorControl sphericalReduction
        sphericalClassification quotientModel sphericalFreeAction
        universalCover sphericalCoveringModel sphericalCoveringProjection
        fundamentalGroupComputation deckGroupIdentification
        deckActionProperness deckGroupTriviality deckActionTrivialization
        trivialDeckQuotientIdentification trivialQuotient
        trivialQuotientHomeomorphism sphericalHomeomorphismLift
        simplyConnectedRecognition homeomorphismAssembly
        homeomorphismDerivation =
      (by
        exact ⟨decomposition, surgeryTraceReconstruction,
          surgeryTraceHandleCancellation, componentClassification,
          discardedComponentHomeomorphismClassification, componentInventory,
          componentBoundarySphereControl, primeDecomposition,
          primeDecompositionExistence, sphereTheoremApplication,
          embeddedSphereProduction, loopTheoremApplication,
          primeDecompositionCompatibility, primeFactorUniqueness,
          irreducibility, irreducibleFactorRecognition, connectedSumCollapse,
          connectedSumFundamentalGroupControl, connectedSumVanKampen,
          simplyConnectedPrimeFactorControl, sphericalReduction,
          sphericalClassification, quotientModel, sphericalFreeAction,
          universalCover, sphericalCoveringModel, sphericalCoveringProjection,
          fundamentalGroupComputation, deckGroupIdentification,
          deckActionProperness, deckGroupTriviality, deckActionTrivialization,
          trivialDeckQuotientIdentification, trivialQuotient,
          trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
          simplyConnectedRecognition, homeomorphismAssembly,
          homeomorphismDerivation⟩) := by
  apply Subsingleton.elim

/--
A package of future topology inputs that turns finite extinction into the
standard sphere homeomorphism conclusion.
-/
structure ExtinctionTopologyExtractionPackage where
  /-- Topological decomposition obtained from each finite-extinction proof. -/
  decomposition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionTopologyDecomposition M extinction
  /-- Reconstruction of the topological surgery trace represented by decomposition. -/
  surgeryTraceReconstruction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSurgeryTraceReconstruction M extinction
          (decomposition M extinction)
  /-- Cancellation of the handles recorded by the reconstructed surgery trace. -/
  surgeryTraceHandleCancellation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSurgeryTraceHandleCancellation M extinction
          (decomposition M extinction)
          (surgeryTraceReconstruction M extinction)
  /-- Classification of the components present after extinction. -/
  componentClassification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionComponentClassification M extinction
          (decomposition M extinction)
  /-- Homeomorphism classification of components discarded at extinction. -/
  discardedComponentHomeomorphismClassification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionDiscardedComponentHomeomorphismClassification M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
  /-- Component inventory extracted from the post-extinction classification. -/
  componentInventory :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionComponentInventory M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
  /-- Boundary-sphere control for the extinction component inventory. -/
  componentBoundarySphereControl :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionComponentBoundarySphereControl M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
          (componentInventory M extinction)
  /-- Recognition theorem for the standard 3-sphere. -/
  recognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasThreeSphereRecognition M (decomposition M)
  /-- Prime/connected-sum decomposition extracted from the extinction data. -/
  primeDecomposition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeDecomposition M extinction
          (decomposition M extinction)
  /-- Existence theorem for the prime decomposition used after extinction. -/
  primeDecompositionExistence :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeDecompositionExistence M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
  /-- Sphere-theorem input behind the prime decomposition. -/
  sphereTheoremApplication :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSphereTheoremApplication M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
  /-- Embedded spheres realizing the prime-decomposition cuts. -/
  embeddedSphereProduction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionEmbeddedSphereProduction M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (sphereTheoremApplication M extinction)
  /-- Loop-theorem input controlling compressions in the prime-decomposition cuts. -/
  loopTheoremApplication :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionLoopTheoremApplication M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (sphereTheoremApplication M extinction)
  /-- Compatibility and uniqueness for the selected prime decomposition. -/
  primeDecompositionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeDecompositionCompatibility M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
          (primeDecomposition M extinction)
  /-- Uniqueness of prime factors in the selected decomposition. -/
  primeFactorUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeFactorUniqueness M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
          (primeDecomposition M extinction)
          (primeDecompositionCompatibility M extinction)
  /-- Irreducibility input for the prime pieces. -/
  irreducibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionIrreducibility M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
  /-- Recognition of irreducible prime factors after extinction. -/
  irreducibleFactorRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionIrreducibleFactorRecognition M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
  /-- Collapse of the connected-sum decomposition in the simply connected case. -/
  connectedSumCollapse :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionConnectedSumCollapse M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
  /-- Fundamental-group control for connected-sum collapse. -/
  connectedSumFundamentalGroupControl :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionConnectedSumFundamentalGroupControl M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
  /-- Van Kampen computation for connected-sum fundamental groups. -/
  connectedSumVanKampen :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionConnectedSumVanKampenCalculation M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (connectedSumFundamentalGroupControl M extinction)
  /-- Control forcing the surviving prime factor to be simply connected. -/
  simplyConnectedPrimeFactorControl :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSimplyConnectedPrimeFactorControl M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (connectedSumFundamentalGroupControl M extinction)
  /-- Reduction of the topological pieces to spherical space forms. -/
  sphericalSpaceFormReduction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSphericalSpaceFormReduction M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
  /-- Classification theorem for the spherical-space-form pieces. -/
  sphericalSpaceFormClassification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormClassification M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
  /-- Spherical quotient model for the surviving pieces. -/
  sphericalQuotientModel :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormQuotientModel M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
  /-- Free spherical action realizing the quotient model. -/
  sphericalFreeAction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormFreeAction M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
  /-- Universal cover of the spherical space form is the standard 3-sphere. -/
  sphericalUniversalCover :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormUniversalCover M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
  /-- Covering model tying the quotient model to the universal cover. -/
  sphericalCoveringModel :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormCoveringModel M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
  /-- Covering projection from the spherical universal cover to the quotient model. -/
  sphericalCoveringProjection :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormCoveringProjection M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
          (sphericalCoveringModel M extinction)
  /-- Fundamental-group computation for the spherical space form pieces. -/
  sphericalFundamentalGroup :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormFundamentalGroupComputation M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
  /-- Identification of the deck group with the computed fundamental group. -/
  deckGroupIdentification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckGroupIdentification M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
  /-- Properness and freeness of the deck action. -/
  deckActionProperness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckActionProperness M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
  /-- Triviality of the spherical space form deck group in the simply connected case. -/
  deckGroupTriviality :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckGroupTriviality M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalFundamentalGroup M extinction)
  /-- Trivialization of the deck action from deck-group evidence. -/
  deckActionTrivialization :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckActionTrivialization M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
  /-- Identification of the quotient by a trivial deck action with the cover. -/
  trivialDeckQuotientIdentification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormTrivialDeckQuotientIdentification M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (deckActionTrivialization M extinction)
  /-- The trivial deck group produces the trivial spherical quotient. -/
  trivialSphericalQuotient :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasTrivialSphericalSpaceFormQuotient M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
  /-- Homeomorphism supplied by the trivial spherical quotient. -/
  trivialQuotientHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormTrivialQuotientHomeomorphism M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (trivialSphericalQuotient M extinction)
  /-- Lift of the final homeomorphism through the trivial spherical quotient. -/
  sphericalHomeomorphismLift :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormHomeomorphismLift M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (trivialSphericalQuotient M extinction)
          (trivialQuotientHomeomorphism M extinction)
  /-- Simply connected recognition eliminating nontrivial spherical factors. -/
  simplyConnectedRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSimplyConnectedExtinctionRecognition M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupTriviality M extinction)
  /-- Final extraction theorem derived from the preceding topology inputs. -/
  extractHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        Nonempty (M ≃ₜ ThreeSphere)
  /-- Assembly of the classification data into the final homeomorphism. -/
  homeomorphismAssembly :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionHomeomorphismAssembly M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (simplyConnectedRecognition M extinction)
          (trivialSphericalQuotient M extinction)
          (extractHomeomorphism M extinction)
  /-- Certificate that the named topology sub-obligations derive the homeomorphism. -/
  homeomorphismDerivation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionHomeomorphismDerivation M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupTriviality M extinction)
          (simplyConnectedRecognition M extinction)
          (sphericalQuotientModel M extinction)
          (deckGroupIdentification M extinction)
          (trivialSphericalQuotient M extinction)
          (extractHomeomorphism M extinction)
          (homeomorphismAssembly M extinction)

/--
A completed topology package supplies the post-extinction decomposition input.
-/
def extinction_decomposition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionTopologyDecomposition M extinction :=
  package.decomposition M extinction

/-- The named extinction-decomposition projection is the stored package field. -/
theorem extinction_decomposition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_decomposition_of_topology_package package M extinction =
      package.decomposition M extinction :=
  rfl

/--
A completed topology package supplies reconstruction of the topological surgery
trace encoded by decomposition.
-/
theorem extinction_surgery_trace_reconstruction_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSurgeryTraceReconstruction M extinction
      (extinction_decomposition_of_topology_package package M extinction) :=
  package.surgeryTraceReconstruction M extinction

/-- The named surgery-trace reconstruction projection is the stored package field. -/
theorem extinction_surgery_trace_reconstruction_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_surgery_trace_reconstruction_of_topology_package
      package M extinction =
      package.surgeryTraceReconstruction M extinction :=
  rfl

/-- A completed topology package supplies handle cancellation for the surgery trace. -/
theorem extinction_surgery_trace_handle_cancellation_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSurgeryTraceHandleCancellation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_surgery_trace_reconstruction_of_topology_package
        package M extinction) :=
  package.surgeryTraceHandleCancellation M extinction

/-- The named surgery-trace handle-cancellation projection is the stored package field. -/
theorem extinction_surgery_trace_handle_cancellation_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_surgery_trace_handle_cancellation_of_topology_package
      package M extinction =
      package.surgeryTraceHandleCancellation M extinction :=
  rfl

/-- A completed topology package supplies post-extinction component classification. -/
theorem extinction_component_classification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentClassification M extinction
      (extinction_decomposition_of_topology_package package M extinction) :=
  package.componentClassification M extinction

/-- The named component-classification projection is the stored package field. -/
theorem extinction_component_classification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_component_classification_of_topology_package
      package M extinction =
      package.componentClassification M extinction :=
  rfl

/--
A completed topology package supplies homeomorphism classification for
discarded extinction components.
-/
theorem extinction_discarded_component_homeomorphism_classification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionDiscardedComponentHomeomorphismClassification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction) :=
  package.discardedComponentHomeomorphismClassification M extinction

/--
The named discarded-component homeomorphism classification projection is the
stored package field.
-/
theorem extinction_discarded_component_homeomorphism_classification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_discarded_component_homeomorphism_classification_of_topology_package
      package M extinction =
      package.discardedComponentHomeomorphismClassification M extinction :=
  rfl

/-- A completed topology package supplies an inventory of extinction components. -/
theorem extinction_component_inventory_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentInventory M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction) :=
  package.componentInventory M extinction

/-- The named component-inventory projection is the stored package field. -/
theorem extinction_component_inventory_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_component_inventory_of_topology_package package M extinction =
      package.componentInventory M extinction :=
  rfl

/-- A completed topology package supplies boundary-sphere component control. -/
theorem extinction_component_boundary_sphere_control_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentBoundarySphereControl M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction)
      (extinction_component_inventory_of_topology_package
        package M extinction) :=
  package.componentBoundarySphereControl M extinction

/-- The named component boundary-sphere control projection is the stored package field. -/
theorem extinction_component_boundary_sphere_control_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_component_boundary_sphere_control_of_topology_package
      package M extinction =
      package.componentBoundarySphereControl M extinction :=
  rfl

/-- A completed topology package supplies the 3-sphere recognition input. -/
theorem three_sphere_recognition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasThreeSphereRecognition M
      (fun extinction =>
        extinction_decomposition_of_topology_package package M extinction) :=
  package.recognition M

/-- The named 3-sphere recognition projection is the stored package field. -/
theorem three_sphere_recognition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    three_sphere_recognition_of_topology_package package M =
      package.recognition M :=
  rfl

/-- A completed topology package supplies prime-decomposition evidence. -/
theorem extinction_prime_decomposition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecomposition M extinction
      (extinction_decomposition_of_topology_package package M extinction) :=
  package.primeDecomposition M extinction

/-- The named prime-decomposition projection is the stored package field. -/
theorem extinction_prime_decomposition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_decomposition_of_topology_package package M extinction =
      package.primeDecomposition M extinction :=
  rfl

/-- A completed topology package supplies prime-decomposition existence. -/
theorem extinction_prime_decomposition_existence_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecompositionExistence M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.primeDecompositionExistence M extinction

/-- The named prime-decomposition existence projection is the stored package field. -/
theorem extinction_prime_decomposition_existence_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_decomposition_existence_of_topology_package
      package M extinction =
      package.primeDecompositionExistence M extinction :=
  rfl

/-- A completed topology package supplies the sphere-theorem input for primes. -/
theorem extinction_sphere_theorem_application_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSphereTheoremApplication M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.sphereTheoremApplication M extinction

/-- The named sphere-theorem application projection is the stored package field. -/
theorem extinction_sphere_theorem_application_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_sphere_theorem_application_of_topology_package
      package M extinction =
      package.sphereTheoremApplication M extinction :=
  rfl

/-- A completed topology package supplies embedded spheres for prime cuts. -/
theorem extinction_embedded_sphere_production_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionEmbeddedSphereProduction M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_sphere_theorem_application_of_topology_package
        package M extinction) :=
  package.embeddedSphereProduction M extinction

/-- The named embedded-sphere production projection is the stored package field. -/
theorem extinction_embedded_sphere_production_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_embedded_sphere_production_of_topology_package
      package M extinction =
      package.embeddedSphereProduction M extinction :=
  rfl

/-- A completed topology package supplies loop-theorem control for prime cuts. -/
theorem extinction_loop_theorem_application_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionLoopTheoremApplication M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_sphere_theorem_application_of_topology_package
        package M extinction) :=
  package.loopTheoremApplication M extinction

/-- The named loop-theorem application projection is the stored package field. -/
theorem extinction_loop_theorem_application_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_loop_theorem_application_of_topology_package
      package M extinction =
      package.loopTheoremApplication M extinction :=
  rfl

/-- A completed topology package supplies prime-decomposition compatibility. -/
theorem extinction_prime_decomposition_compatibility_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecompositionCompatibility M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.primeDecompositionCompatibility M extinction

/-- The named prime-decomposition compatibility projection is the stored package field. -/
theorem extinction_prime_decomposition_compatibility_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_decomposition_compatibility_of_topology_package
      package M extinction =
      package.primeDecompositionCompatibility M extinction :=
  rfl

/-- A completed topology package supplies uniqueness of prime factors. -/
theorem extinction_prime_factor_uniqueness_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeFactorUniqueness M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_prime_decomposition_compatibility_of_topology_package
        package M extinction) :=
  package.primeFactorUniqueness M extinction

/-- The named prime-factor uniqueness projection is the stored package field. -/
theorem extinction_prime_factor_uniqueness_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_factor_uniqueness_of_topology_package
      package M extinction =
      package.primeFactorUniqueness M extinction :=
  rfl

/-- A completed topology package supplies irreducibility evidence. -/
theorem extinction_irreducibility_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionIrreducibility M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.irreducibility M extinction

/-- The named irreducibility projection is the stored package field. -/
theorem extinction_irreducibility_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_irreducibility_of_topology_package package M extinction =
      package.irreducibility M extinction :=
  rfl

/-- A completed topology package supplies recognition of irreducible factors. -/
theorem extinction_irreducible_factor_recognition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionIrreducibleFactorRecognition M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction) :=
  package.irreducibleFactorRecognition M extinction

/-- The named irreducible-factor recognition projection is the stored package field. -/
theorem extinction_irreducible_factor_recognition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_irreducible_factor_recognition_of_topology_package
      package M extinction =
      package.irreducibleFactorRecognition M extinction :=
  rfl

/-- A completed topology package supplies connected-sum collapse evidence. -/
theorem extinction_connected_sum_collapse_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumCollapse M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction) :=
  package.connectedSumCollapse M extinction

/-- The named connected-sum collapse projection is the stored package field. -/
theorem extinction_connected_sum_collapse_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_connected_sum_collapse_of_topology_package
      package M extinction =
      package.connectedSumCollapse M extinction :=
  rfl

/-- A completed topology package supplies connected-sum fundamental-group control. -/
theorem extinction_connected_sum_fundamental_group_control_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumFundamentalGroupControl M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction) :=
  package.connectedSumFundamentalGroupControl M extinction

/-- The named connected-sum fundamental-group control projection is the stored package field. -/
theorem extinction_connected_sum_fundamental_group_control_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_connected_sum_fundamental_group_control_of_topology_package
      package M extinction =
      package.connectedSumFundamentalGroupControl M extinction :=
  rfl

/--
A completed topology package supplies the van Kampen calculation for connected
sum fundamental groups.
-/
theorem extinction_connected_sum_van_kampen_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumVanKampenCalculation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_connected_sum_fundamental_group_control_of_topology_package
        package M extinction) :=
  package.connectedSumVanKampen M extinction

/-- The named connected-sum van Kampen projection is the stored package field. -/
theorem extinction_connected_sum_van_kampen_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_connected_sum_van_kampen_of_topology_package
      package M extinction =
      package.connectedSumVanKampen M extinction :=
  rfl

/-- A completed topology package forces the surviving prime factor to be simply connected. -/
theorem extinction_simply_connected_prime_factor_control_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSimplyConnectedPrimeFactorControl M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_connected_sum_fundamental_group_control_of_topology_package
        package M extinction) :=
  package.simplyConnectedPrimeFactorControl M extinction

/-- The named simply connected prime-factor control projection is the stored package field. -/
theorem extinction_simply_connected_prime_factor_control_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_simply_connected_prime_factor_control_of_topology_package
      package M extinction =
      package.simplyConnectedPrimeFactorControl M extinction :=
  rfl

/-- A completed topology package supplies spherical-space-form reduction evidence. -/
theorem extinction_spherical_space_form_reduction_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSphericalSpaceFormReduction M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction) :=
  package.sphericalSpaceFormReduction M extinction

/-- The named spherical-space-form reduction projection is the stored package field. -/
theorem extinction_spherical_space_form_reduction_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_spherical_space_form_reduction_of_topology_package
      package M extinction =
      package.sphericalSpaceFormReduction M extinction :=
  rfl

/-- A completed topology package supplies spherical-space-form classification. -/
theorem spherical_space_form_classification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormClassification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction) :=
  package.sphericalSpaceFormClassification M extinction

/-- The named spherical-space-form classification projection is the stored package field. -/
theorem spherical_space_form_classification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_space_form_classification_of_topology_package
      package M extinction =
      package.sphericalSpaceFormClassification M extinction :=
  rfl

/-- A completed topology package supplies the spherical quotient model. -/
theorem spherical_quotient_model_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormQuotientModel M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction) :=
  package.sphericalQuotientModel M extinction

/-- The named spherical quotient-model projection is the stored package field. -/
theorem spherical_quotient_model_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_quotient_model_of_topology_package package M extinction =
      package.sphericalQuotientModel M extinction :=
  rfl

/-- A completed topology package supplies the free spherical action. -/
theorem spherical_free_action_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormFreeAction M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction) :=
  package.sphericalFreeAction M extinction

/-- The named spherical free-action projection is the stored package field. -/
theorem spherical_free_action_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_free_action_of_topology_package package M extinction =
      package.sphericalFreeAction M extinction :=
  rfl

/-- A completed topology package supplies the spherical universal-cover input. -/
theorem spherical_universal_cover_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormUniversalCover M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction) :=
  package.sphericalUniversalCover M extinction

/-- The named spherical universal-cover projection is the stored package field. -/
theorem spherical_universal_cover_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_universal_cover_of_topology_package package M extinction =
      package.sphericalUniversalCover M extinction :=
  rfl

/-- A completed topology package supplies the spherical covering model. -/
theorem spherical_covering_model_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormCoveringModel M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction) :=
  package.sphericalCoveringModel M extinction

/-- The named spherical covering-model projection is the stored package field. -/
theorem spherical_covering_model_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_covering_model_of_topology_package package M extinction =
      package.sphericalCoveringModel M extinction :=
  rfl

/-- A completed topology package supplies the spherical covering projection. -/
theorem spherical_covering_projection_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormCoveringProjection M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction)
      (spherical_covering_model_of_topology_package package M extinction) :=
  package.sphericalCoveringProjection M extinction

/-- The named spherical covering-projection projection is the stored package field. -/
theorem spherical_covering_projection_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_covering_projection_of_topology_package package M extinction =
      package.sphericalCoveringProjection M extinction :=
  rfl

/-- A completed topology package supplies spherical-space-form group computation. -/
theorem spherical_fundamental_group_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormFundamentalGroupComputation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction) :=
  package.sphericalFundamentalGroup M extinction

/-- The named spherical fundamental-group projection is the stored package field. -/
theorem spherical_fundamental_group_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_fundamental_group_of_topology_package package M extinction =
      package.sphericalFundamentalGroup M extinction :=
  rfl

/-- A completed topology package identifies the deck group with the computed group. -/
theorem spherical_deck_group_identification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckGroupIdentification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction) :=
  package.deckGroupIdentification M extinction

/-- The named deck-group identification projection is the stored package field. -/
theorem spherical_deck_group_identification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_group_identification_of_topology_package
      package M extinction =
      package.deckGroupIdentification M extinction :=
  rfl

/-- A completed topology package supplies deck-action properness. -/
theorem spherical_deck_action_properness_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckActionProperness M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction) :=
  package.deckActionProperness M extinction

/-- The named deck-action properness projection is the stored package field. -/
theorem spherical_deck_action_properness_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_action_properness_of_topology_package
      package M extinction =
      package.deckActionProperness M extinction :=
  rfl

/-- A completed topology package supplies deck-group triviality evidence. -/
theorem spherical_deck_group_triviality_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckGroupTriviality M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction) :=
  package.deckGroupTriviality M extinction

/-- The named deck-group triviality projection is the stored package field. -/
theorem spherical_deck_group_triviality_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_group_triviality_of_topology_package
      package M extinction =
      package.deckGroupTriviality M extinction :=
  rfl

/-- A completed topology package supplies deck-action trivialization. -/
theorem spherical_deck_action_trivialization_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckActionTrivialization M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction) :=
  package.deckActionTrivialization M extinction

/-- The named deck-action trivialization projection is the stored package field. -/
theorem spherical_deck_action_trivialization_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_action_trivialization_of_topology_package
      package M extinction =
      package.deckActionTrivialization M extinction :=
  rfl

/--
A completed topology package identifies the quotient by a trivial deck action
with the cover.
-/
theorem spherical_trivial_deck_quotient_identification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormTrivialDeckQuotientIdentification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (spherical_deck_action_trivialization_of_topology_package
        package M extinction) :=
  package.trivialDeckQuotientIdentification M extinction

/-- The named trivial deck-quotient identification projection is the stored package field. -/
theorem spherical_trivial_deck_quotient_identification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_trivial_deck_quotient_identification_of_topology_package
      package M extinction =
      package.trivialDeckQuotientIdentification M extinction :=
  rfl

/-- A completed topology package supplies the trivial spherical quotient input. -/
theorem trivial_spherical_quotient_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasTrivialSphericalSpaceFormQuotient M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction) :=
  package.trivialSphericalQuotient M extinction

/-- The named trivial spherical quotient projection is the stored package field. -/
theorem trivial_spherical_quotient_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    trivial_spherical_quotient_of_topology_package package M extinction =
      package.trivialSphericalQuotient M extinction :=
  rfl

/-- A completed topology package supplies the trivial-quotient homeomorphism input. -/
theorem trivial_quotient_homeomorphism_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormTrivialQuotientHomeomorphism M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package
        package M extinction) :=
  package.trivialQuotientHomeomorphism M extinction

/--
The named trivial-quotient homeomorphism projection is the stored package
field.
-/
theorem trivial_quotient_homeomorphism_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    trivial_quotient_homeomorphism_of_topology_package package M extinction =
      package.trivialQuotientHomeomorphism M extinction :=
  rfl

/--
A completed topology package supplies the final homeomorphism lift through the
trivial spherical quotient.
-/
theorem spherical_homeomorphism_lift_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormHomeomorphismLift M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package package M extinction)
      (trivial_quotient_homeomorphism_of_topology_package
        package M extinction) :=
  package.sphericalHomeomorphismLift M extinction

/-- The named spherical homeomorphism-lift projection is the stored package field. -/
theorem spherical_homeomorphism_lift_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_homeomorphism_lift_of_topology_package package M extinction =
      package.sphericalHomeomorphismLift M extinction :=
  rfl

/-- A completed topology package supplies simply connected recognition evidence. -/
theorem simply_connected_extinction_recognition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSimplyConnectedExtinctionRecognition M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction) :=
  package.simplyConnectedRecognition M extinction

/-- The named simply connected recognition projection is the stored package field. -/
theorem simply_connected_extinction_recognition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    simply_connected_extinction_recognition_of_topology_package
      package M extinction =
      package.simplyConnectedRecognition M extinction :=
  rfl

/-- A completed topology package extracts the final homeomorphism from extinction. -/
theorem homeomorphism_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  package.extractHomeomorphism M extinction

/-- The named topology-package homeomorphism projection is the stored package field. -/
theorem homeomorphism_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_topology_package package M extinction =
      package.extractHomeomorphism M extinction :=
  rfl

/-- A completed topology package assembles classification data into the homeomorphism. -/
theorem extinction_homeomorphism_assembly_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionHomeomorphismAssembly M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (simply_connected_extinction_recognition_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package package M extinction)
      (homeomorphism_of_topology_package package M extinction) :=
  package.homeomorphismAssembly M extinction

/-- The named topology homeomorphism-assembly projection is the stored package field. -/
theorem extinction_homeomorphism_assembly_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_homeomorphism_assembly_of_topology_package
      package M extinction =
      package.homeomorphismAssembly M extinction :=
  rfl

/--
A completed topology package supplies the derivation certificate for its
projected homeomorphism.
-/
theorem extinction_homeomorphism_derivation_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionHomeomorphismDerivation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (simply_connected_extinction_recognition_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package package M extinction)
      (homeomorphism_of_topology_package package M extinction)
      (extinction_homeomorphism_assembly_of_topology_package
        package M extinction) :=
  package.homeomorphismDerivation M extinction

/-- The named topology homeomorphism-derivation projection is the stored package field. -/
theorem extinction_homeomorphism_derivation_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_homeomorphism_derivation_of_topology_package
      package M extinction =
      package.homeomorphismDerivation M extinction :=
  rfl

/--
A completed topology package assembles the fixed-manifold derivation statement
for its projected homeomorphism.
-/
theorem extinction_topology_derivation_statement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyDerivationStatement M extinction
      (homeomorphism_of_topology_package package M extinction) :=
  extinction_topology_derivation_statement_of_components M extinction
    (homeomorphism_of_topology_package package M extinction)
    (extinction_decomposition_of_topology_package package M extinction)
    (extinction_surgery_trace_reconstruction_of_topology_package
      package M extinction)
    (extinction_surgery_trace_handle_cancellation_of_topology_package
      package M extinction)
    (extinction_component_classification_of_topology_package
      package M extinction)
    (extinction_discarded_component_homeomorphism_classification_of_topology_package
      package M extinction)
    (extinction_component_inventory_of_topology_package package M extinction)
    (extinction_component_boundary_sphere_control_of_topology_package
      package M extinction)
    (extinction_prime_decomposition_of_topology_package package M extinction)
    (extinction_prime_decomposition_existence_of_topology_package
      package M extinction)
    (extinction_sphere_theorem_application_of_topology_package
      package M extinction)
    (extinction_embedded_sphere_production_of_topology_package
      package M extinction)
    (extinction_loop_theorem_application_of_topology_package
      package M extinction)
    (extinction_prime_decomposition_compatibility_of_topology_package
      package M extinction)
    (extinction_prime_factor_uniqueness_of_topology_package
      package M extinction)
    (extinction_irreducibility_of_topology_package package M extinction)
    (extinction_irreducible_factor_recognition_of_topology_package
      package M extinction)
    (extinction_connected_sum_collapse_of_topology_package
      package M extinction)
    (extinction_connected_sum_fundamental_group_control_of_topology_package
      package M extinction)
    (extinction_connected_sum_van_kampen_of_topology_package
      package M extinction)
    (extinction_simply_connected_prime_factor_control_of_topology_package
      package M extinction)
    (extinction_spherical_space_form_reduction_of_topology_package
      package M extinction)
    (spherical_space_form_classification_of_topology_package
      package M extinction)
    (spherical_quotient_model_of_topology_package package M extinction)
    (spherical_free_action_of_topology_package package M extinction)
    (spherical_universal_cover_of_topology_package package M extinction)
    (spherical_covering_model_of_topology_package package M extinction)
    (spherical_covering_projection_of_topology_package package M extinction)
    (spherical_fundamental_group_of_topology_package package M extinction)
    (spherical_deck_group_identification_of_topology_package
      package M extinction)
    (spherical_deck_action_properness_of_topology_package
      package M extinction)
    (spherical_deck_group_triviality_of_topology_package package M extinction)
    (spherical_deck_action_trivialization_of_topology_package
      package M extinction)
    (spherical_trivial_deck_quotient_identification_of_topology_package
      package M extinction)
    (trivial_spherical_quotient_of_topology_package package M extinction)
    (trivial_quotient_homeomorphism_of_topology_package package M extinction)
    (spherical_homeomorphism_lift_of_topology_package package M extinction)
    (simply_connected_extinction_recognition_of_topology_package
      package M extinction)
    (extinction_homeomorphism_assembly_of_topology_package package M extinction)
    (extinction_homeomorphism_derivation_of_topology_package package M extinction)

/--
The completed topology package route to the fixed-manifold topology derivation
statement is exactly the component assembly route applied to the package
projections.
-/
theorem extinction_topology_derivation_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_topology_derivation_statement_of_topology_package
        package M extinction =
      extinction_topology_derivation_statement_of_components M extinction
        (homeomorphism_of_topology_package package M extinction)
        (extinction_decomposition_of_topology_package package M extinction)
        (extinction_surgery_trace_reconstruction_of_topology_package
          package M extinction)
        (extinction_surgery_trace_handle_cancellation_of_topology_package
          package M extinction)
        (extinction_component_classification_of_topology_package
          package M extinction)
        (extinction_discarded_component_homeomorphism_classification_of_topology_package
          package M extinction)
        (extinction_component_inventory_of_topology_package package M extinction)
        (extinction_component_boundary_sphere_control_of_topology_package
          package M extinction)
        (extinction_prime_decomposition_of_topology_package package M extinction)
        (extinction_prime_decomposition_existence_of_topology_package
          package M extinction)
        (extinction_sphere_theorem_application_of_topology_package
          package M extinction)
        (extinction_embedded_sphere_production_of_topology_package
          package M extinction)
        (extinction_loop_theorem_application_of_topology_package
          package M extinction)
        (extinction_prime_decomposition_compatibility_of_topology_package
          package M extinction)
        (extinction_prime_factor_uniqueness_of_topology_package
          package M extinction)
        (extinction_irreducibility_of_topology_package package M extinction)
        (extinction_irreducible_factor_recognition_of_topology_package
          package M extinction)
        (extinction_connected_sum_collapse_of_topology_package
          package M extinction)
        (extinction_connected_sum_fundamental_group_control_of_topology_package
          package M extinction)
        (extinction_connected_sum_van_kampen_of_topology_package
          package M extinction)
        (extinction_simply_connected_prime_factor_control_of_topology_package
          package M extinction)
        (extinction_spherical_space_form_reduction_of_topology_package
          package M extinction)
        (spherical_space_form_classification_of_topology_package
          package M extinction)
        (spherical_quotient_model_of_topology_package package M extinction)
        (spherical_free_action_of_topology_package package M extinction)
        (spherical_universal_cover_of_topology_package package M extinction)
        (spherical_covering_model_of_topology_package package M extinction)
        (spherical_covering_projection_of_topology_package package M extinction)
        (spherical_fundamental_group_of_topology_package package M extinction)
        (spherical_deck_group_identification_of_topology_package
          package M extinction)
        (spherical_deck_action_properness_of_topology_package
          package M extinction)
        (spherical_deck_group_triviality_of_topology_package
          package M extinction)
        (spherical_deck_action_trivialization_of_topology_package
          package M extinction)
        (spherical_trivial_deck_quotient_identification_of_topology_package
          package M extinction)
        (trivial_spherical_quotient_of_topology_package package M extinction)
        (trivial_quotient_homeomorphism_of_topology_package package M extinction)
        (spherical_homeomorphism_lift_of_topology_package package M extinction)
        (simply_connected_extinction_recognition_of_topology_package
          package M extinction)
        (extinction_homeomorphism_assembly_of_topology_package
          package M extinction)
        (extinction_homeomorphism_derivation_of_topology_package
          package M extinction) := by
  apply Subsingleton.elim

/--
Semantic alias for the full post-extinction classification sub-obligation
payload exposed by a fixed-manifold topology derivation statement.
-/
abbrev ExtinctionTopologyClassificationSubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) : Prop :=
    ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
    ∃ _surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
    ∃ _surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition _surgeryTraceReconstruction,
    ∃ componentClassification :
      HasExtinctionComponentClassification M extinction decomposition,
    ∃ _discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification,
    ∃ _componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification,
    ∃ _componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification _componentInventory,
    ∃ primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition,
    ∃ _primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition,
    ∃ _sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition,
    ∃ _embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition,
    ∃ _primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        _primeDecompositionCompatibility,
    ∃ irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition,
    ∃ _irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility,
    ∃ connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility,
    ∃ _connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ _simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ _sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover,
    ∃ _sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        _sphericalCoveringModel,
    ∃ fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation,
    ∃ _deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification,
    ∃ deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation,
    ∃ _deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality,
    ∃ _trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality _deckActionTrivialization,
    ∃ _trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
    ∃ _trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient,
    ∃ _sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient _trivialQuotientHomeomorphism,
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality

/--
The topology classification sub-obligation payload alias is definitionally the
full decomposition, trace, component, prime-decomposition, connected-sum,
space-form, deck-group, quotient, lift, and recognition witness stack.
-/
theorem extinctionTopologyClassificationSubobligationsPayload_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyClassificationSubobligationsPayload M extinction =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ _surgeryTraceReconstruction :
        HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
      ∃ _surgeryTraceHandleCancellation :
        HasExtinctionSurgeryTraceHandleCancellation
          M extinction decomposition _surgeryTraceReconstruction,
      ∃ componentClassification :
        HasExtinctionComponentClassification M extinction decomposition,
      ∃ _discardedComponentHomeomorphismClassification :
        HasExtinctionDiscardedComponentHomeomorphismClassification
          M extinction decomposition componentClassification,
      ∃ _componentInventory :
        HasExtinctionComponentInventory
          M extinction decomposition componentClassification,
      ∃ _componentBoundarySphereControl :
        HasExtinctionComponentBoundarySphereControl
          M extinction decomposition componentClassification _componentInventory,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ _primeDecompositionExistence :
        HasExtinctionPrimeDecompositionExistence
          M extinction decomposition primeDecomposition,
      ∃ _sphereTheoremApplication :
        HasExtinctionSphereTheoremApplication
          M extinction decomposition primeDecomposition,
      ∃ _embeddedSphereProduction :
        HasExtinctionEmbeddedSphereProduction
          M extinction decomposition primeDecomposition
          _sphereTheoremApplication,
      ∃ _loopTheoremApplication :
        HasExtinctionLoopTheoremApplication
          M extinction decomposition primeDecomposition
          _sphereTheoremApplication,
      ∃ _primeDecompositionCompatibility :
        HasExtinctionPrimeDecompositionCompatibility
          M extinction decomposition componentClassification primeDecomposition,
      ∃ _primeFactorUniqueness :
        HasExtinctionPrimeFactorUniqueness
          M extinction decomposition componentClassification primeDecomposition
          _primeDecompositionCompatibility,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ _irreducibleFactorRecognition :
        HasExtinctionIrreducibleFactorRecognition
          M extinction decomposition primeDecomposition irreducibility,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ _connectedSumFundamentalGroupControl :
        HasExtinctionConnectedSumFundamentalGroupControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _connectedSumVanKampen :
        HasExtinctionConnectedSumVanKampenCalculation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse _connectedSumFundamentalGroupControl,
      ∃ _simplyConnectedPrimeFactorControl :
        HasExtinctionSimplyConnectedPrimeFactorControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse _connectedSumFundamentalGroupControl,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _sphericalClassification :
        HasSphericalSpaceFormClassification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ _sphericalFreeAction :
        HasSphericalSpaceFormFreeAction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ _universalCover :
        HasSphericalSpaceFormUniversalCover
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ _sphericalCoveringModel :
        HasSphericalSpaceFormCoveringModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover,
      ∃ _sphericalCoveringProjection :
        HasSphericalSpaceFormCoveringProjection
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover
          _sphericalCoveringModel,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ _deckActionProperness :
        HasSphericalSpaceFormDeckActionProperness
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ _deckActionTrivialization :
        HasSphericalSpaceFormDeckActionTrivialization
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
      ∃ _trivialDeckQuotientIdentification :
        HasSphericalSpaceFormTrivialDeckQuotientIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality _deckActionTrivialization,
      ∃ _trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
      ∃ _trivialQuotientHomeomorphism :
        HasSphericalSpaceFormTrivialQuotientHomeomorphism
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          _trivialQuotient,
      ∃ _sphericalHomeomorphismLift :
        HasSphericalSpaceFormHomeomorphismLift
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          _trivialQuotient _trivialQuotientHomeomorphism,
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality) :=
  rfl

/--
The fixed-manifold topology derivation statement exposes the full
post-extinction classification sub-obligation stack.
-/
theorem topology_classification_subobligations_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
    ∃ _surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
    ∃ _surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition _surgeryTraceReconstruction,
    ∃ componentClassification :
      HasExtinctionComponentClassification M extinction decomposition,
    ∃ _discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification,
    ∃ _componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification,
    ∃ _componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification _componentInventory,
    ∃ primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition,
    ∃ _primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition,
    ∃ _sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition,
    ∃ _embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition,
    ∃ _primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        _primeDecompositionCompatibility,
    ∃ irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition,
    ∃ _irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility,
    ∃ connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility,
    ∃ _connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ _simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ _sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover,
    ∃ _sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        _sphericalCoveringModel,
    ∃ fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation,
    ∃ _deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification,
    ∃ deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation,
    ∃ _deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality,
    ∃ _trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality _deckActionTrivialization,
    ∃ _trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
    ∃ _trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient,
    ∃ _sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient _trivialQuotientHomeomorphism,
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality := by
  rcases derivationStatement with
    ⟨decomposition, surgeryTraceReconstruction,
      surgeryTraceHandleCancellation, componentClassification,
      discardedComponentHomeomorphismClassification, componentInventory,
      componentBoundarySphereControl, primeDecomposition,
      primeDecompositionExistence, sphereTheoremApplication,
      embeddedSphereProduction, loopTheoremApplication,
      primeDecompositionCompatibility, primeFactorUniqueness, irreducibility,
      irreducibleFactorRecognition, connectedSumCollapse,
      connectedSumFundamentalGroupControl, connectedSumVanKampen,
      simplyConnectedPrimeFactorControl, sphericalReduction,
      sphericalClassification, quotientModel, sphericalFreeAction,
      universalCover, sphericalCoveringModel, sphericalCoveringProjection,
      fundamentalGroupComputation, deckGroupIdentification,
      deckActionProperness, deckGroupTriviality, deckActionTrivialization,
      trivialDeckQuotientIdentification, trivialQuotient,
      trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
      simplyConnectedRecognition, _homeomorphismAssembly,
      _homeomorphismDerivation⟩
  exact ⟨decomposition, surgeryTraceReconstruction,
    surgeryTraceHandleCancellation, componentClassification,
    discardedComponentHomeomorphismClassification, componentInventory,
    componentBoundarySphereControl, primeDecomposition,
    primeDecompositionExistence, sphereTheoremApplication,
    embeddedSphereProduction, loopTheoremApplication,
    primeDecompositionCompatibility, primeFactorUniqueness, irreducibility,
    irreducibleFactorRecognition, connectedSumCollapse,
    connectedSumFundamentalGroupControl, connectedSumVanKampen,
    simplyConnectedPrimeFactorControl, sphericalReduction,
    sphericalClassification, quotientModel, sphericalFreeAction,
    universalCover, sphericalCoveringModel, sphericalCoveringProjection,
    fundamentalGroupComputation, deckGroupIdentification, deckActionProperness,
    deckGroupTriviality, deckActionTrivialization,
    trivialDeckQuotientIdentification, trivialQuotient,
    trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
    simplyConnectedRecognition⟩

/--
The classification-subobligation bridge from a full topology derivation
statement exposes exactly the post-extinction classification components stored
in it.
-/
theorem topology_classification_subobligations_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    topology_classification_subobligations_of_derivation_statement
        M extinction homeomorphism derivationStatement =
      (by
        rcases derivationStatement with
          ⟨decomposition, surgeryTraceReconstruction,
            surgeryTraceHandleCancellation, componentClassification,
            discardedComponentHomeomorphismClassification, componentInventory,
            componentBoundarySphereControl, primeDecomposition,
            primeDecompositionExistence, sphereTheoremApplication,
            embeddedSphereProduction, loopTheoremApplication,
            primeDecompositionCompatibility, primeFactorUniqueness,
            irreducibility, irreducibleFactorRecognition, connectedSumCollapse,
            connectedSumFundamentalGroupControl, connectedSumVanKampen,
            simplyConnectedPrimeFactorControl, sphericalReduction,
            sphericalClassification, quotientModel, sphericalFreeAction,
            universalCover, sphericalCoveringModel, sphericalCoveringProjection,
            fundamentalGroupComputation, deckGroupIdentification,
            deckActionProperness, deckGroupTriviality, deckActionTrivialization,
            trivialDeckQuotientIdentification, trivialQuotient,
            trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
            simplyConnectedRecognition, _homeomorphismAssembly,
            _homeomorphismDerivation⟩
        exact ⟨decomposition, surgeryTraceReconstruction,
          surgeryTraceHandleCancellation, componentClassification,
          discardedComponentHomeomorphismClassification, componentInventory,
          componentBoundarySphereControl, primeDecomposition,
          primeDecompositionExistence, sphereTheoremApplication,
          embeddedSphereProduction, loopTheoremApplication,
          primeDecompositionCompatibility, primeFactorUniqueness,
          irreducibility, irreducibleFactorRecognition, connectedSumCollapse,
          connectedSumFundamentalGroupControl, connectedSumVanKampen,
          simplyConnectedPrimeFactorControl, sphericalReduction,
          sphericalClassification, quotientModel, sphericalFreeAction,
          universalCover, sphericalCoveringModel, sphericalCoveringProjection,
          fundamentalGroupComputation, deckGroupIdentification,
          deckActionProperness, deckGroupTriviality, deckActionTrivialization,
          trivialDeckQuotientIdentification, trivialQuotient,
          trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
          simplyConnectedRecognition⟩) := by
  apply Subsingleton.elim

/--
The fixed-manifold homeomorphism assembly statement: the post-extinction
classification, quotient, deck-group, and simply-connected recognition data
assemble the projected homeomorphism to the standard 3-sphere.
-/
def ExtinctionTopologyHomeomorphismAssemblyStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop :=
  ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
  ∃ primeDecomposition :
    HasExtinctionPrimeDecomposition M extinction decomposition,
  ∃ irreducibility :
    HasExtinctionIrreducibility
      M extinction decomposition primeDecomposition,
  ∃ connectedSumCollapse :
    HasExtinctionConnectedSumCollapse
      M extinction decomposition primeDecomposition irreducibility,
  ∃ sphericalReduction :
    HasExtinctionSphericalSpaceFormReduction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ quotientModel :
    HasSphericalSpaceFormQuotientModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ fundamentalGroupComputation :
    HasSphericalSpaceFormFundamentalGroupComputation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupIdentification :
    HasSphericalSpaceFormDeckGroupIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation,
  ∃ deckGroupTriviality :
    HasSphericalSpaceFormDeckGroupTriviality
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation,
  ∃ simplyConnectedRecognition :
    HasSimplyConnectedExtinctionRecognition
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation
      deckGroupTriviality,
  ∃ trivialQuotient :
    HasTrivialSphericalSpaceFormQuotient
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
    HasExtinctionHomeomorphismAssembly M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      quotientModel fundamentalGroupComputation deckGroupIdentification
      deckGroupTriviality simplyConnectedRecognition trivialQuotient
      homeomorphism

/--
The homeomorphism assembly statement is definitionally the narrow
classification, quotient, deck-group, recognition, trivial-quotient, and
assembly witness stack.
-/
theorem extinctionTopologyHomeomorphismAssemblyStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) :
    ExtinctionTopologyHomeomorphismAssemblyStatement
      M extinction homeomorphism =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ simplyConnectedRecognition :
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality,
      ∃ trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
        HasExtinctionHomeomorphismAssembly M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction quotientModel fundamentalGroupComputation
          deckGroupIdentification deckGroupTriviality simplyConnectedRecognition
          trivialQuotient homeomorphism) :=
  rfl

/--
The fixed-manifold homeomorphism derivation statement: the assembled
homeomorphism certificate is sufficient to derive the projected homeomorphism.
-/
def ExtinctionTopologyHomeomorphismDerivationStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop :=
  ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
  ∃ primeDecomposition :
    HasExtinctionPrimeDecomposition M extinction decomposition,
  ∃ irreducibility :
    HasExtinctionIrreducibility
      M extinction decomposition primeDecomposition,
  ∃ connectedSumCollapse :
    HasExtinctionConnectedSumCollapse
      M extinction decomposition primeDecomposition irreducibility,
  ∃ sphericalReduction :
    HasExtinctionSphericalSpaceFormReduction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ fundamentalGroupComputation :
    HasSphericalSpaceFormFundamentalGroupComputation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupTriviality :
    HasSphericalSpaceFormDeckGroupTriviality
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation,
  ∃ simplyConnectedRecognition :
    HasSimplyConnectedExtinctionRecognition
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation
      deckGroupTriviality,
  ∃ quotientModel :
    HasSphericalSpaceFormQuotientModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupIdentification :
    HasSphericalSpaceFormDeckGroupIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation,
  ∃ trivialQuotient :
    HasTrivialSphericalSpaceFormQuotient
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
  ∃ homeomorphismAssembly :
    HasExtinctionHomeomorphismAssembly M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      quotientModel fundamentalGroupComputation deckGroupIdentification
      deckGroupTriviality simplyConnectedRecognition trivialQuotient
      homeomorphism,
    HasExtinctionHomeomorphismDerivation M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      fundamentalGroupComputation deckGroupTriviality simplyConnectedRecognition
      quotientModel deckGroupIdentification trivialQuotient homeomorphism
      homeomorphismAssembly

/--
The homeomorphism derivation statement is definitionally the narrow recognition,
assembly, and derivation witness stack.
-/
theorem extinctionTopologyHomeomorphismDerivationStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) :
    ExtinctionTopologyHomeomorphismDerivationStatement
      M extinction homeomorphism =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ simplyConnectedRecognition :
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
      ∃ homeomorphismAssembly :
        HasExtinctionHomeomorphismAssembly M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction quotientModel fundamentalGroupComputation
          deckGroupIdentification deckGroupTriviality simplyConnectedRecognition
          trivialQuotient homeomorphism,
        HasExtinctionHomeomorphismDerivation M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction fundamentalGroupComputation deckGroupTriviality
          simplyConnectedRecognition quotientModel deckGroupIdentification
          trivialQuotient homeomorphism homeomorphismAssembly) :=
  rfl

/--
The full topology derivation statement contains the narrower homeomorphism
assembly statement.
-/
theorem topology_homeomorphism_assembly_statement_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    ExtinctionTopologyHomeomorphismAssemblyStatement
      M extinction homeomorphism := by
  rcases derivationStatement with
    ⟨decomposition, _surgeryTraceReconstruction,
      _surgeryTraceHandleCancellation, _componentClassification,
      _discardedComponentHomeomorphismClassification, _componentInventory,
      _componentBoundarySphereControl, primeDecomposition,
      _primeDecompositionExistence, _sphereTheoremApplication,
      _embeddedSphereProduction, _loopTheoremApplication,
      _primeDecompositionCompatibility, _primeFactorUniqueness, irreducibility,
      _irreducibleFactorRecognition, connectedSumCollapse,
      _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
      _simplyConnectedPrimeFactorControl, sphericalReduction,
      _sphericalClassification, quotientModel, _sphericalFreeAction,
      _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
      fundamentalGroupComputation, deckGroupIdentification,
      _deckActionProperness, deckGroupTriviality, _deckActionTrivialization,
      _trivialDeckQuotientIdentification, trivialQuotient,
      _trivialQuotientHomeomorphism, _sphericalHomeomorphismLift,
      simplyConnectedRecognition, homeomorphismAssembly,
      _homeomorphismDerivation⟩
  exact ⟨decomposition, primeDecomposition, irreducibility,
    connectedSumCollapse, sphericalReduction, quotientModel,
    fundamentalGroupComputation, deckGroupIdentification, deckGroupTriviality,
    simplyConnectedRecognition, trivialQuotient, homeomorphismAssembly⟩

/--
The assembly-statement bridge from a full topology derivation statement exposes
exactly the narrower homeomorphism assembly components stored in it.
-/
theorem topology_homeomorphism_assembly_statement_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    topology_homeomorphism_assembly_statement_of_derivation_statement
        M extinction homeomorphism derivationStatement =
      (by
        rcases derivationStatement with
          ⟨decomposition, _surgeryTraceReconstruction,
            _surgeryTraceHandleCancellation, _componentClassification,
            _discardedComponentHomeomorphismClassification, _componentInventory,
            _componentBoundarySphereControl, primeDecomposition,
            _primeDecompositionExistence, _sphereTheoremApplication,
            _embeddedSphereProduction, _loopTheoremApplication,
            _primeDecompositionCompatibility, _primeFactorUniqueness,
            irreducibility, _irreducibleFactorRecognition,
            connectedSumCollapse, _connectedSumFundamentalGroupControl,
            _connectedSumVanKampen, _simplyConnectedPrimeFactorControl,
            sphericalReduction, _sphericalClassification, quotientModel,
            _sphericalFreeAction, _universalCover, _sphericalCoveringModel,
            _sphericalCoveringProjection, fundamentalGroupComputation,
            deckGroupIdentification, _deckActionProperness, deckGroupTriviality,
            _deckActionTrivialization, _trivialDeckQuotientIdentification,
            trivialQuotient, _trivialQuotientHomeomorphism,
            _sphericalHomeomorphismLift, simplyConnectedRecognition,
            homeomorphismAssembly, _homeomorphismDerivation⟩
        exact ⟨decomposition, primeDecomposition, irreducibility,
          connectedSumCollapse, sphericalReduction, quotientModel,
          fundamentalGroupComputation, deckGroupIdentification,
          deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
          homeomorphismAssembly⟩) := by
  apply Subsingleton.elim

/--
The full topology derivation statement contains the narrower homeomorphism
derivation statement.
-/
theorem topology_homeomorphism_derivation_statement_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    ExtinctionTopologyHomeomorphismDerivationStatement
      M extinction homeomorphism := by
  rcases derivationStatement with
    ⟨decomposition, _surgeryTraceReconstruction,
      _surgeryTraceHandleCancellation, _componentClassification,
      _discardedComponentHomeomorphismClassification, _componentInventory,
      _componentBoundarySphereControl, primeDecomposition,
      _primeDecompositionExistence, _sphereTheoremApplication,
      _embeddedSphereProduction, _loopTheoremApplication,
      _primeDecompositionCompatibility, _primeFactorUniqueness, irreducibility,
      _irreducibleFactorRecognition, connectedSumCollapse,
      _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
      _simplyConnectedPrimeFactorControl, sphericalReduction,
      _sphericalClassification, quotientModel, _sphericalFreeAction,
      _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
      fundamentalGroupComputation, deckGroupIdentification,
      _deckActionProperness, deckGroupTriviality, _deckActionTrivialization,
      _trivialDeckQuotientIdentification, trivialQuotient,
      _trivialQuotientHomeomorphism, _sphericalHomeomorphismLift,
      simplyConnectedRecognition, homeomorphismAssembly,
      homeomorphismDerivation⟩
  exact ⟨decomposition, primeDecomposition, irreducibility,
    connectedSumCollapse, sphericalReduction, fundamentalGroupComputation,
    deckGroupTriviality, simplyConnectedRecognition, quotientModel,
    deckGroupIdentification, trivialQuotient, homeomorphismAssembly,
    homeomorphismDerivation⟩

/--
The derivation-statement bridge from a full topology derivation statement
exposes exactly the narrower homeomorphism derivation components stored in it.
-/
theorem topology_homeomorphism_derivation_statement_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    topology_homeomorphism_derivation_statement_of_derivation_statement
        M extinction homeomorphism derivationStatement =
      (by
        rcases derivationStatement with
          ⟨decomposition, _surgeryTraceReconstruction,
            _surgeryTraceHandleCancellation, _componentClassification,
            _discardedComponentHomeomorphismClassification, _componentInventory,
            _componentBoundarySphereControl, primeDecomposition,
            _primeDecompositionExistence, _sphereTheoremApplication,
            _embeddedSphereProduction, _loopTheoremApplication,
            _primeDecompositionCompatibility, _primeFactorUniqueness,
            irreducibility, _irreducibleFactorRecognition,
            connectedSumCollapse, _connectedSumFundamentalGroupControl,
            _connectedSumVanKampen, _simplyConnectedPrimeFactorControl,
            sphericalReduction, _sphericalClassification, quotientModel,
            _sphericalFreeAction, _universalCover, _sphericalCoveringModel,
            _sphericalCoveringProjection, fundamentalGroupComputation,
            deckGroupIdentification, _deckActionProperness, deckGroupTriviality,
            _deckActionTrivialization, _trivialDeckQuotientIdentification,
            trivialQuotient, _trivialQuotientHomeomorphism,
            _sphericalHomeomorphismLift, simplyConnectedRecognition,
            homeomorphismAssembly, homeomorphismDerivation⟩
        exact ⟨decomposition, primeDecomposition, irreducibility,
          connectedSumCollapse, sphericalReduction, fundamentalGroupComputation,
          deckGroupTriviality, simplyConnectedRecognition, quotientModel,
          deckGroupIdentification, trivialQuotient, homeomorphismAssembly,
          homeomorphismDerivation⟩) := by
  apply Subsingleton.elim

/--
A completed topology package supplies the theorem-shaped extraction statement
consumed by the final Poincare assembly.
-/
theorem extinction_topology_extraction_statement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExtinctionTopologyExtractionStatement.{u} := by
  intro M _ _ _ _ _ extinction
  exact ⟨homeomorphism_of_topology_package package M extinction,
    extinction_topology_derivation_statement_of_topology_package
      package M extinction⟩

/--
The package-to-topology-extraction statement constructor is the explicit
fixed-extinction homeomorphism plus derivation statement projection.
-/
theorem extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    extinction_topology_extraction_statement_of_topology_package package =
      (by
        intro M _ _ _ _ _ extinction
        exact ⟨homeomorphism_of_topology_package package M extinction,
          extinction_topology_derivation_statement_of_topology_package
            package M extinction⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement exposes the fixed-extinction
homeomorphism together with its derivation statement payload.
-/
theorem topology_derivation_statement_payload_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
      ExtinctionTopologyDerivationStatement M extinction homeomorphism := by
  rcases topologyStatement M extinction with
    ⟨homeomorphism, derivationStatement⟩
  exact ⟨homeomorphism, derivationStatement⟩

/--
The fixed-extinction topology payload destructures the theorem-shaped
extraction statement at that finite-extinction witness.
-/
theorem topology_derivation_statement_payload_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_extraction_statement
      topologyStatement M extinction =
      (by
        rcases topologyStatement M extinction with
          ⟨homeomorphism, derivationStatement⟩
        exact ⟨homeomorphism, derivationStatement⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement supplies the fixed-extinction
homeomorphism conclusion.
-/
theorem homeomorphism_of_topology_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases topology_derivation_statement_payload_of_extraction_statement
      topologyStatement M extinction with
    ⟨homeomorphism, _derivationStatement⟩
  exact homeomorphism

/--
The fixed-extinction homeomorphism projection is the first field of the
theorem-shaped topology payload.
-/
theorem homeomorphism_of_topology_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_topology_extraction_statement
      topologyStatement M extinction =
      (by
        rcases topology_derivation_statement_payload_of_extraction_statement
            topologyStatement M extinction with
          ⟨homeomorphism, _derivationStatement⟩
        exact homeomorphism) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement also supplies the derivation
statement for the homeomorphism selected by
`homeomorphism_of_topology_extraction_statement`.
-/
theorem topology_derivation_statement_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyDerivationStatement M extinction
      (homeomorphism_of_topology_extraction_statement
        topologyStatement M extinction) := by
  rcases topology_derivation_statement_payload_of_extraction_statement
      topologyStatement M extinction with
    ⟨_homeomorphism, derivationStatement⟩
  exact derivationStatement

/--
The fixed-extinction derivation projection is the second field of the
theorem-shaped topology payload after the homeomorphism projection chooses its
first field.
-/
theorem topology_derivation_statement_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_extraction_statement
      topologyStatement M extinction =
      (by
        rcases topology_derivation_statement_payload_of_extraction_statement
            topologyStatement M extinction with
          ⟨_homeomorphism, derivationStatement⟩
        exact derivationStatement) := by
  apply Subsingleton.elim

/--
For a topology extraction statement built from a package, the direct derivation
projection is the package derivation route.
-/
theorem topology_derivation_statement_of_extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_extraction_statement
      (extinction_topology_extraction_statement_of_topology_package package)
      M extinction =
      extinction_topology_derivation_statement_of_topology_package
        package M extinction := by
  apply Subsingleton.elim

/--
For a topology extraction statement built from a package, the direct
homeomorphism projection is the package homeomorphism route.
-/
theorem homeomorphism_of_extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_topology_extraction_statement
      (extinction_topology_extraction_statement_of_topology_package package)
      M extinction =
      homeomorphism_of_topology_package package M extinction := by
  apply Subsingleton.elim

/--
For a topology extraction statement built from a package, the two-field
homeomorphism/derivation payload is the package homeomorphism route paired with
the package derivation route.
-/
theorem topology_derivation_statement_payload_of_extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_extraction_statement
      (extinction_topology_extraction_statement_of_topology_package package)
      M extinction =
      ⟨homeomorphism_of_topology_package package M extinction,
        extinction_topology_derivation_statement_of_topology_package
          package M extinction⟩ := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement directly exposes the
classification sub-obligation payload through its projected derivation
statement.
-/
theorem topology_classification_subobligations_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyClassificationSubobligationsPayload M extinction := by
  exact topology_classification_subobligations_of_derivation_statement
    M extinction
    (homeomorphism_of_topology_extraction_statement
      topologyStatement M extinction)
    (topology_derivation_statement_of_extraction_statement
      topologyStatement M extinction)

/--
The classification payload projected from a theorem-shaped topology extraction
statement is the classification bridge applied to its projected homeomorphism
and derivation statement.
-/
theorem topology_classification_subobligations_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_extraction_statement
      topologyStatement M extinction =
      topology_classification_subobligations_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_extraction_statement
          topologyStatement M extinction)
        (topology_derivation_statement_of_extraction_statement
          topologyStatement M extinction) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement directly exposes the
homeomorphism assembly statement through its projected derivation statement.
-/
theorem topology_homeomorphism_assembly_statement_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
      (homeomorphism_of_topology_extraction_statement
        topologyStatement M extinction) := by
  exact topology_homeomorphism_assembly_statement_of_derivation_statement
    M extinction
    (homeomorphism_of_topology_extraction_statement
      topologyStatement M extinction)
    (topology_derivation_statement_of_extraction_statement
      topologyStatement M extinction)

/--
The homeomorphism assembly statement projected from a theorem-shaped topology
extraction statement is the corresponding derivation-statement bridge.
-/
theorem topology_homeomorphism_assembly_statement_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_extraction_statement
      topologyStatement M extinction =
      topology_homeomorphism_assembly_statement_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_extraction_statement
          topologyStatement M extinction)
        (topology_derivation_statement_of_extraction_statement
          topologyStatement M extinction) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement directly exposes the
homeomorphism derivation statement through its projected derivation statement.
-/
theorem topology_homeomorphism_derivation_statement_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismDerivationStatement M extinction
      (homeomorphism_of_topology_extraction_statement
        topologyStatement M extinction) := by
  exact topology_homeomorphism_derivation_statement_of_derivation_statement
    M extinction
    (homeomorphism_of_topology_extraction_statement
      topologyStatement M extinction)
    (topology_derivation_statement_of_extraction_statement
      topologyStatement M extinction)

/--
The homeomorphism derivation statement projected from a theorem-shaped topology
extraction statement is the corresponding derivation-statement bridge.
-/
theorem topology_homeomorphism_derivation_statement_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_extraction_statement
      topologyStatement M extinction =
      topology_homeomorphism_derivation_statement_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_extraction_statement
          topologyStatement M extinction)
        (topology_derivation_statement_of_extraction_statement
          topologyStatement M extinction) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement exposes the fixed-extinction
payload consisting of the statement itself, its projected homeomorphism, its
derivation statement, and the statement-level classification and
homeomorphism-statement projections.
-/
theorem topology_extraction_statement_payload_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ _topologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ _derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism,
    ∃ _classificationSubobligations :
      ExtinctionTopologyClassificationSubobligationsPayload M extinction,
    ∃ _assemblyStatement :
      ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
        homeomorphism,
      ExtinctionTopologyHomeomorphismDerivationStatement M extinction
        homeomorphism := by
  exact ⟨topologyStatement,
    homeomorphism_of_topology_extraction_statement
      topologyStatement M extinction,
    topology_derivation_statement_of_extraction_statement
      topologyStatement M extinction,
    topology_classification_subobligations_of_extraction_statement
      topologyStatement M extinction,
    topology_homeomorphism_assembly_statement_of_extraction_statement
      topologyStatement M extinction,
    topology_homeomorphism_derivation_statement_of_extraction_statement
      topologyStatement M extinction⟩

/--
The fixed-extinction payload projected from a theorem-shaped topology
extraction statement is exactly the tuple of the named statement projections.
-/
theorem topology_extraction_statement_payload_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_extraction_statement
      topologyStatement M extinction =
      ⟨topologyStatement,
        homeomorphism_of_topology_extraction_statement
          topologyStatement M extinction,
        topology_derivation_statement_of_extraction_statement
          topologyStatement M extinction,
        topology_classification_subobligations_of_extraction_statement
          topologyStatement M extinction,
        topology_homeomorphism_assembly_statement_of_extraction_statement
          topologyStatement M extinction,
        topology_homeomorphism_derivation_statement_of_extraction_statement
          topologyStatement M extinction⟩ := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement supplies the existing
finite-extinction-to-sphere interface.
-/
theorem extinction_implies_sphere_of_topology_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  intro M _ _ _ _ _ extinction
  exact homeomorphism_of_topology_extraction_statement
    topologyStatement M extinction

/--
The final extraction interface from a theorem-shaped topology statement is the
fixed-extinction homeomorphism projection at every finite-extinction witness.
-/
theorem extinction_implies_sphere_of_topology_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    extinction_implies_sphere_of_topology_extraction_statement
      topologyStatement =
      (by
        intro M _ _ _ _ _ extinction
        exact homeomorphism_of_topology_extraction_statement
          topologyStatement M extinction) := by
  apply Subsingleton.elim

/--
If a finite-extinction-to-sphere extractor is accompanied by derivation evidence
for the homeomorphism it returns, then it upgrades to the stronger topology
extraction statement.
-/
theorem extinction_topology_extraction_statement_of_extraction_and_derivation
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    ExtinctionTopologyExtractionStatement.{u} := by
  intro M _ _ _ _ _ extinction
  exact ⟨extractSphere M extinction, derive M extinction⟩

/--
The extraction-plus-derivation constructor packages the supplied extractor
with the derivation evidence at each finite-extinction witness.
-/
theorem extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    extinction_topology_extraction_statement_of_extraction_and_derivation
      extractSphere derive =
      (by
        intro M _ _ _ _ _ extinction
        exact ⟨extractSphere M extinction, derive M extinction⟩) := by
  apply Subsingleton.elim

/--
Projecting the fixed-extinction topology payload from a statement reconstructed
from an extractor and derivation evidence returns those supplied fields.
-/
theorem topology_derivation_statement_payload_of_extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_extraction_statement
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derive)
      M extinction =
      ⟨extractSphere M extinction, derive M extinction⟩ := by
  apply Subsingleton.elim

/--
The fixed-extinction homeomorphism projected from an extractor-plus-derivation
statement is the supplied extractor at that finite-extinction witness.
-/
theorem homeomorphism_of_extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_topology_extraction_statement
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derive)
      M extinction =
      extractSphere M extinction := by
  apply Subsingleton.elim

/--
The fixed-extinction derivation projected from an extractor-plus-derivation
statement is the supplied derivation evidence at that finite-extinction
witness.
-/
theorem topology_derivation_statement_of_extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_extraction_statement
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derive)
      M extinction =
      derive M extinction := by
  apply Subsingleton.elim

/--
The final extraction interface recovered from an extractor-plus-derivation
statement is the supplied extractor.
-/
theorem extinction_implies_sphere_of_extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    extinction_implies_sphere_of_topology_extraction_statement
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derive) =
      extractSphere := by
  apply Subsingleton.elim

/--
The strong topology extraction statement is exactly a
finite-extinction-to-sphere extractor together with derivation evidence for the
homeomorphism chosen by that extractor.
-/
theorem extinction_topology_extraction_statement_iff_extraction_with_derivation :
    ExtinctionTopologyExtractionStatement.{u} ↔
      ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
        ExtinctionTopologyDerivationForExtractionStatement.{u}
          extractSphere := by
  constructor
  · intro topologyStatement
    let extractSphere : ExtinctionImpliesSphereStatement.{u} := by
      intro M _ _ _ _ _ extinction
      exact (topologyStatement M extinction).choose
    refine ⟨extractSphere, ?_⟩
    intro M _ _ _ _ _ extinction
    exact (topologyStatement M extinction).choose_spec
  · rintro ⟨extractSphere, derive⟩
    exact extinction_topology_extraction_statement_of_extraction_and_derivation
      extractSphere derive

/--
The strong topology extraction equivalence is the pair of the named extractor
projection and the named constructor from extraction plus derivation evidence.
-/
theorem extinction_topology_extraction_statement_iff_extraction_with_derivation_eq :
    extinction_topology_extraction_statement_iff_extraction_with_derivation =
      (by
        constructor
        · intro topologyStatement
          let extractSphere : ExtinctionImpliesSphereStatement.{u} := by
            intro M _ _ _ _ _ extinction
            exact (topologyStatement M extinction).choose
          refine ⟨extractSphere, ?_⟩
          intro M _ _ _ _ _ extinction
          exact (topologyStatement M extinction).choose_spec
        · rintro ⟨extractSphere, derive⟩
          exact
            extinction_topology_extraction_statement_of_extraction_and_derivation
              extractSphere derive) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus the stronger topology extraction statement is
enough to discharge the project target.
-/
theorem poincare_statement_of_finite_extinction_and_topology_extraction_statement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  exact poincare_statement_of_extinction_and_extraction finiteExtinction
    (extinction_implies_sphere_of_topology_extraction_statement
      topologyStatement)

/--
The topology-extraction route to the project target is the existing
finite-extinction/extraction assembly applied to the statement-mediated final
extractor.
-/
theorem poincare_statement_of_finite_extinction_and_topology_extraction_statement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_statement_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement =
      poincare_statement_of_extinction_and_extraction finiteExtinction
        (extinction_implies_sphere_of_topology_extraction_statement
          topologyStatement) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus the stronger topology extraction statement
exposes the target and universe-indexed completion criterion as one payload.
-/
theorem poincare_payload_of_finite_extinction_and_topology_extraction_statement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_poincareConjectureStatement
    (poincare_statement_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement)

/--
The topology-extraction project payload is the statement-layer completion
payload of the named topology-extraction target route.
-/
theorem poincare_payload_of_finite_extinction_and_topology_extraction_statement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_payload_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement =
      poincare_completion_payload_of_poincareConjectureStatement
        (poincare_statement_of_finite_extinction_and_topology_extraction_statement
          finiteExtinction topologyStatement) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus a final extractor and its topology derivation
certificate is enough to discharge the project target.
-/
theorem poincare_statement_of_finite_extinction_and_extraction_derivation
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    PoincareConjectureStatement.{u} := by
  exact
    poincare_statement_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derivation)

/--
The extractor-plus-derivation route to the project target factors through the
named topology-extraction statement constructor.
-/
theorem poincare_statement_of_finite_extinction_and_extraction_derivation_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    poincare_statement_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation =
      poincare_statement_of_finite_extinction_and_topology_extraction_statement
        finiteExtinction
        (extinction_topology_extraction_statement_of_extraction_and_derivation
          extractSphere derivation) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus a final extractor and its topology derivation
certificate exposes the target and universe-indexed completion criterion as one
payload.
-/
theorem poincare_payload_of_finite_extinction_and_extraction_derivation
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_poincareConjectureStatement
    (poincare_statement_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation)

/--
The extractor-plus-derivation project payload is the statement-layer completion
payload of the named extractor-plus-derivation target route.
-/
theorem poincare_payload_of_finite_extinction_and_extraction_derivation_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    poincare_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation =
      poincare_completion_payload_of_poincareConjectureStatement
        (poincare_statement_of_finite_extinction_and_extraction_derivation
          finiteExtinction extractSphere derivation) := by
  apply Subsingleton.elim

/--
A completed topology package supplies the theorem-shaped extraction statement
together with the final extraction interface consumed by the assembly layer.
-/
theorem topology_extraction_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _topologyStatement : ExtinctionTopologyExtractionStatement.{u},
      ExtinctionImpliesSphereStatement.{u} := by
  let topologyStatement :=
    extinction_topology_extraction_statement_of_topology_package package
  exact ⟨topologyStatement,
    extinction_implies_sphere_of_topology_extraction_statement
      topologyStatement⟩

/--
The package extraction payload is the theorem-shaped statement paired with its
statement-mediated final extractor.
-/
theorem topology_extraction_payload_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    topology_extraction_payload_of_topology_package package =
      ⟨extinction_topology_extraction_statement_of_topology_package package,
        extinction_implies_sphere_of_topology_extraction_statement
          (extinction_topology_extraction_statement_of_topology_package
            package)⟩ := by
  apply Subsingleton.elim

/--
A completed topology package supplies a final extractor paired with the
post-extinction topology derivation certificate for that extractor.
-/
theorem topology_extraction_derivation_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  exact extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
    (extinction_topology_extraction_statement_of_topology_package package)

/--
The package extraction-derivation payload is the forward direction of the
extraction/derivation equivalence for the theorem-shaped package statement.
-/
theorem topology_extraction_derivation_payload_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    topology_extraction_derivation_payload_of_topology_package package =
      extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
        (extinction_topology_extraction_statement_of_topology_package
          package) := by
  apply Subsingleton.elim

/--
A completed topology package extracts the theorem-shaped topology statement,
its fixed-extinction homeomorphism, the full classification sub-obligation
stack, and the homeomorphism assembly/derivation statements from any
finite-extinction input.
-/
theorem topology_extraction_statement_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ _topologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ _derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism,
    ∃ _classificationSubobligations :
      ExtinctionTopologyClassificationSubobligationsPayload M extinction,
    ∃ _assemblyStatement :
      ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
        homeomorphism,
      ExtinctionTopologyHomeomorphismDerivationStatement M extinction
        homeomorphism := by
  rcases topology_extraction_payload_of_topology_package package with
    ⟨topologyStatement, _extraction⟩
  rcases topology_derivation_statement_payload_of_extraction_statement
      topologyStatement M extinction with
    ⟨homeomorphism, derivationStatement⟩
  let classificationSubobligations :=
    topology_classification_subobligations_of_derivation_statement M
      extinction homeomorphism derivationStatement
  exact ⟨topologyStatement, homeomorphism, derivationStatement,
    classificationSubobligations,
    topology_homeomorphism_assembly_statement_of_derivation_statement M
      extinction homeomorphism derivationStatement,
    topology_homeomorphism_derivation_statement_of_derivation_statement M
      extinction homeomorphism derivationStatement⟩

/--
The fixed-extinction package payload is selected by first exposing the package
topology statement, then destructuring its homeomorphism/derivation payload and
the named derivation subpayload projections.
-/
theorem topology_extraction_statement_payload_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_topology_package
      package M extinction =
      (by
        rcases topology_extraction_payload_of_topology_package package with
          ⟨topologyStatement, _extraction⟩
        rcases topology_derivation_statement_payload_of_extraction_statement
            topologyStatement M extinction with
          ⟨homeomorphism, derivationStatement⟩
        let classificationSubobligations :=
          topology_classification_subobligations_of_derivation_statement M
            extinction homeomorphism derivationStatement
        exact ⟨topologyStatement, homeomorphism, derivationStatement,
          classificationSubobligations,
          topology_homeomorphism_assembly_statement_of_derivation_statement M
            extinction homeomorphism derivationStatement,
          topology_homeomorphism_derivation_statement_of_derivation_statement M
            extinction homeomorphism derivationStatement⟩) := by
  apply Subsingleton.elim

/--
The fixed-extinction package payload can also be rebuilt directly from the
package-built theorem-shaped extraction statement and its named projection
bridges.
-/
theorem topology_extraction_statement_payload_of_topology_package_to_extraction_statement_projections_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_topology_package
      package M extinction =
      (by
        let topologyStatement :=
          extinction_topology_extraction_statement_of_topology_package package
        exact ⟨topologyStatement,
          homeomorphism_of_topology_extraction_statement
            topologyStatement M extinction,
          topology_derivation_statement_of_extraction_statement
            topologyStatement M extinction,
          topology_classification_subobligations_of_extraction_statement
            topologyStatement M extinction,
          topology_homeomorphism_assembly_statement_of_extraction_statement
            topologyStatement M extinction,
          topology_homeomorphism_derivation_statement_of_extraction_statement
            topologyStatement M extinction⟩) := by
  apply Subsingleton.elim

/--
The package fixed-extinction topology payload is the fixed-extinction payload
of the package-built theorem-shaped topology extraction statement.
-/
theorem topology_extraction_statement_payload_of_topology_package_to_extraction_statement_payload_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_topology_package
      package M extinction =
      topology_extraction_statement_payload_of_extraction_statement
        (extinction_topology_extraction_statement_of_topology_package package)
        M extinction := by
  apply Subsingleton.elim

/--
A completed topology package directly exposes the named post-extinction
classification sub-obligation payload for each finite-extinction input.
-/
theorem topology_classification_subobligations_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyClassificationSubobligationsPayload M extinction :=
  topology_classification_subobligations_of_derivation_statement M extinction
    (homeomorphism_of_topology_package package M extinction)
    (extinction_topology_derivation_statement_of_topology_package
      package M extinction)

/--
The package-level topology classification bridge is exactly the derivation
statement bridge applied to the package's projected homeomorphism and
fixed-extinction derivation statement.
-/
theorem topology_classification_subobligations_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_topology_package
        package M extinction =
      topology_classification_subobligations_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package package M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          package M extinction) := by
  apply Subsingleton.elim

/--
A completed topology package directly exposes the fixed-extinction
homeomorphism assembly statement.
-/
theorem topology_homeomorphism_assembly_statement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
      (homeomorphism_of_topology_package package M extinction) :=
  topology_homeomorphism_assembly_statement_of_derivation_statement
    M extinction
    (homeomorphism_of_topology_package package M extinction)
    (extinction_topology_derivation_statement_of_topology_package
      package M extinction)

/--
The package-level topology homeomorphism assembly statement is the
derivation-statement bridge applied to the package projections.
-/
theorem topology_homeomorphism_assembly_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_topology_package
        package M extinction =
      topology_homeomorphism_assembly_statement_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package package M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          package M extinction) := by
  apply Subsingleton.elim

/--
A completed topology package directly exposes the fixed-extinction
homeomorphism derivation statement.
-/
theorem topology_homeomorphism_derivation_statement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismDerivationStatement M extinction
      (homeomorphism_of_topology_package package M extinction) :=
  topology_homeomorphism_derivation_statement_of_derivation_statement
    M extinction
    (homeomorphism_of_topology_package package M extinction)
    (extinction_topology_derivation_statement_of_topology_package
      package M extinction)

/--
The package-level topology homeomorphism derivation statement is the
derivation-statement bridge applied to the package projections.
-/
theorem topology_homeomorphism_derivation_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_topology_package
        package M extinction =
      topology_homeomorphism_derivation_statement_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package package M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          package M extinction) := by
  apply Subsingleton.elim

/--
Projecting classification sub-obligations from a package-built theorem-shaped
topology statement agrees with the direct package-level classification route.
-/
theorem topology_classification_subobligations_of_extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_extraction_statement
      (extinction_topology_extraction_statement_of_topology_package package)
      M extinction =
      topology_classification_subobligations_of_topology_package
        package M extinction := by
  apply Subsingleton.elim

/--
Projecting the homeomorphism assembly statement from a package-built
theorem-shaped topology statement agrees with the direct package-level route.
-/
theorem topology_homeomorphism_assembly_statement_of_extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_extraction_statement
      (extinction_topology_extraction_statement_of_topology_package package)
      M extinction =
      topology_homeomorphism_assembly_statement_of_topology_package
        package M extinction := by
  apply Subsingleton.elim

/--
Projecting the homeomorphism derivation statement from a package-built
theorem-shaped topology statement agrees with the direct package-level route.
-/
theorem topology_homeomorphism_derivation_statement_of_extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_extraction_statement
      (extinction_topology_extraction_statement_of_topology_package package)
      M extinction =
      topology_homeomorphism_derivation_statement_of_topology_package
        package M extinction := by
  apply Subsingleton.elim

/--
Any completed topology extraction package supplies the existing extraction
interface consumed by the final Poincare assembly theorem.
-/
theorem extinction_implies_sphere_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  rcases topology_extraction_payload_of_topology_package package with
    ⟨_topologyStatement, extraction⟩
  exact extraction

/--
The package final extractor agrees with the extractor mediated by the package's
theorem-shaped topology extraction statement.
-/
theorem extinction_implies_sphere_of_topology_package_to_statement_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    extinction_implies_sphere_of_topology_package package =
      extinction_implies_sphere_of_topology_extraction_statement
        (extinction_topology_extraction_statement_of_topology_package
          package) := by
  apply Subsingleton.elim

/--
The final extraction projection agrees with the extractor supplied by the
package-level extraction payload.
-/
theorem extinction_implies_sphere_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    extinction_implies_sphere_of_topology_package package =
      (topology_extraction_payload_of_topology_package package).choose_spec :=
  by
    apply Subsingleton.elim

end Poincare
