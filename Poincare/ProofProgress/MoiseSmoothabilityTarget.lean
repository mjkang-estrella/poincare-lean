/-
Moise-shaped smoothability target.

The previously recorded smoothability frontiers ask every chart of an
arbitrary topological atlas to be `C¹`-compatible with the transported
one-point atlas.  That statement is false for general topological charts and
is therefore not a provable frontier.  The correct target, matching Moise's
smoothing theorem for 3-manifolds, is the *existence* of some compatible
smooth structure.  This module records that existence-shaped target and
discharges the one-point-recognized case as a genuine theorem.
-/

import Poincare.ProofProgress.SmoothabilityOnePointRecognition

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Moise-shaped smoothability for a topological space: there exists some charted
structure over the project 3-manifold model for which the space is a `C¹`
manifold.  Unlike the all-charts compatibility payloads, this is existence of
one smooth structure, which is the actual content of Moise's theorem.
-/
def AdmitsSurgeryModelSmoothStructure (M : Type u) [TopologicalSpace M] :
    Prop :=
  ∃ _charted : ChartedSpace ThreeManifoldModel M,
    IsManifold ThreeManifoldModelWithCorners 1 M

/--
The corrected Moise smoothability target for the project: every compact
simply connected topological 3-manifold admits some `C¹` structure over the
surgery model.
-/
def MoiseSmoothabilityStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      AdmitsSurgeryModelSmoothStructure M

/--
The Moise target expands to the expected universal existence statement.
-/
theorem moiseSmoothabilityStatement_eq :
    MoiseSmoothabilityStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          AdmitsSurgeryModelSmoothStructure M) :=
  rfl

/--
The one-point-recognized case of the Moise target is a theorem: any space
homeomorphic to the one-point compactification of `ℝ³` admits a `C¹`
structure over the surgery model, by transporting the concrete
compactification atlas.
-/
theorem admitsSurgeryModelSmoothStructure_of_homeomorph_onePoint
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    AdmitsSurgeryModelSmoothStructure M := by
  obtain ⟨_t2, charted, _simple, _compact, smooth, _nonempty⟩ :=
    smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace h
  exact ⟨charted, smooth⟩

/--
The same Moise target is available from `ThreeSphere` recognition: the
recognized sphere is first converted to the one-point compactification route,
then the transported smooth compactification atlas supplies the surgery-model
smooth structure.
-/
theorem admitsSurgeryModelSmoothStructure_of_homeomorph_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    AdmitsSurgeryModelSmoothStructure M :=
  admitsSurgeryModelSmoothStructure_of_homeomorph_onePoint
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)

/--
The Moise target follows from one-point recognition of every compact simply
connected 3-manifold.  This isolates the genuinely open recognition input
from the already-proved transport step.
-/
theorem moiseSmoothabilityStatement_of_onePointRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    MoiseSmoothabilityStatement.{u} := by
  intro M _ _ _ _ _
  exact admitsSurgeryModelSmoothStructure_of_homeomorph_onePoint (recognize M)

/--
The Moise target also follows from `ThreeSphere` recognition of every compact
simply connected 3-manifold, matching the topology-extraction route whose
recognized output is stated as a sphere homeomorphism.
-/
theorem moiseSmoothabilityStatement_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    MoiseSmoothabilityStatement.{u} := by
  intro M _ _ _ _ _
  exact admitsSurgeryModelSmoothStructure_of_homeomorph_threeSphere (recognize M)

end Poincare
