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

import Poincare.DependencyCrosswalk
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

/--
`ThreeSphere` recognition supplies both the corrected Moise-shaped
smoothability statement and a recognized smooth-structure payload for every
target in the compact simply connected family.
-/
theorem moiseSmoothabilityStatement_and_recognized_smoothStructure_family_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    MoiseSmoothabilityStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            AdmitsSurgeryModelSmoothStructure M) := by
  exact
    ⟨ moiseSmoothabilityStatement_of_threeSphereRecognition recognize
    , fun M _top _t2 _charted _simple _compact =>
        let h := recognize M
        ⟨h, admitsSurgeryModelSmoothStructure_of_homeomorph_threeSphere h⟩
    ⟩

/--
`ThreeSphere` recognition exposes the corrected Moise statement, the recognized
smooth-structure payload, and the full transported surgery-prerequisite package
for every compact simply connected target.
-/
theorem moiseSmoothabilityStatement_recognized_smoothStructure_and_surgeryPrerequisites_family_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    MoiseSmoothabilityStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            AdmitsSurgeryModelSmoothStructure M ∧
            (∃ _t2 : T2Space M,
              ∃ _charted : ChartedSpace ThreeManifoldModel M,
              ∃ _simple : SimplyConnectedSpace M,
              ∃ _compact : CompactSpace M,
              ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                Nonempty M)) := by
  exact
    ⟨ moiseSmoothabilityStatement_of_threeSphereRecognition recognize
    , fun M _top _t2 _charted _simple _compact =>
        let h := recognize M
        ⟨ h
        , admitsSurgeryModelSmoothStructure_of_homeomorph_threeSphere h
        , smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
            (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)
        ⟩
    ⟩

/--
Moise-shaped `C∞` smoothability for a topological space: there exists some
charted structure over the project 3-manifold model for which the space is a
smooth 3-manifold.  This stronger witness lowers to the surgery-model `C¹`
target on the same transported charted structure.
-/
def AdmitsSmoothThreeManifoldStructure (M : Type u) [TopologicalSpace M] :
    Prop :=
  ∃ _charted : ChartedSpace ThreeManifoldModel M,
    IsManifold (𝓡 3) ∞ M

/--
The `C∞` Moise-shaped target for the project: every compact simply connected
topological 3-manifold admits some smooth structure over the project
3-manifold model.
-/
def MoiseSmoothThreeManifoldStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      AdmitsSmoothThreeManifoldStructure M

/--
A smooth 3-manifold witness lowers to the surgery-model smoothability witness
on the same charted-space structure.
-/
theorem admitsSurgeryModelSmoothStructure_of_admitsSmoothThreeManifoldStructure
    {M : Type u} [TopologicalSpace M]
    (h : AdmitsSmoothThreeManifoldStructure M) :
    AdmitsSurgeryModelSmoothStructure M := by
  rcases h with ⟨charted, smoothManifold⟩
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  exact surgeryModel_isManifold_of_smoothManifold M smoothManifold

/--
Any source recognized as the one-point compactification admits a transported
`C∞` smooth 3-manifold structure.
-/
theorem admitsSmoothThreeManifoldStructure_of_homeomorph_onePoint
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    AdmitsSmoothThreeManifoldStructure M := by
  rcases h with ⟨e⟩
  refine ⟨homeomorphToOnePoint_threeSpace_smoothChartedSpace e, ?_⟩
  exact homeomorphToOnePoint_threeSpace_smoothManifold e

/--
The transported `C∞` witness for `ThreeSphere`-recognized sources is obtained
by passing through the one-point compactification model.
-/
theorem admitsSmoothThreeManifoldStructure_of_homeomorph_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    AdmitsSmoothThreeManifoldStructure M :=
  admitsSmoothThreeManifoldStructure_of_homeomorph_onePoint
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)

/--
The `C∞` Moise target implies the surgery-model Moise target by regularity
lowering target-by-target.
-/
theorem moiseSmoothabilityStatement_of_moiseSmoothThreeManifoldStatement
    (smoothMoise : MoiseSmoothThreeManifoldStatement.{u}) :
    MoiseSmoothabilityStatement.{u} := by
  intro M _top _t2 _charted _simple _compact
  exact
    admitsSurgeryModelSmoothStructure_of_admitsSmoothThreeManifoldStructure
      (smoothMoise M)

/--
`ThreeSphere` recognition of every compact simply connected target proves the
stronger `C∞` Moise-shaped target.
-/
theorem moiseSmoothThreeManifoldStatement_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    MoiseSmoothThreeManifoldStatement.{u} := by
  intro M _top _t2 _charted _simple _compact
  exact admitsSmoothThreeManifoldStructure_of_homeomorph_threeSphere
    (recognize M)

/--
Structured assembly payload retained by downstream certificate code: from
`ThreeSphere` recognition it stores the stronger `C∞` smoothability target, the
surgery-model target obtained by lowering, the recognition witnesses in both
models, the per-target smooth witnesses, and the full surgery prerequisites.
-/
structure MoiseSmoothabilityRecognitionAssemblyPayload where
  smoothMoise : MoiseSmoothThreeManifoldStatement.{u}
  surgeryMoise : MoiseSmoothabilityStatement.{u}
  recognizedSphere :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)
  recognizedOnePoint :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  smoothStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        AdmitsSmoothThreeManifoldStructure M
  surgeryStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        AdmitsSurgeryModelSmoothStructure M
  surgeryPrerequisites :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M

/--
Target-family `ThreeSphere` recognition constructs the full Moise
smoothability assembly payload.
-/
theorem moiseSmoothabilityRecognitionAssemblyPayload_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    MoiseSmoothabilityRecognitionAssemblyPayload.{u} where
  smoothMoise :=
    moiseSmoothThreeManifoldStatement_of_threeSphereRecognition recognize
  surgeryMoise :=
    moiseSmoothabilityStatement_of_moiseSmoothThreeManifoldStatement
      (moiseSmoothThreeManifoldStatement_of_threeSphereRecognition recognize)
  recognizedSphere := recognize
  recognizedOnePoint := fun M _top _t2 _charted _simple _compact =>
    homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
      (recognize M)
  smoothStructure := fun M _top _t2 _charted _simple _compact =>
    admitsSmoothThreeManifoldStructure_of_homeomorph_threeSphere
      (recognize M)
  surgeryStructure := fun M _top _t2 _charted _simple _compact =>
    admitsSurgeryModelSmoothStructure_of_admitsSmoothThreeManifoldStructure
      (admitsSmoothThreeManifoldStructure_of_homeomorph_threeSphere
        (recognize M))
  surgeryPrerequisites := fun M _top _t2 _charted _simple _compact =>
    smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
        (recognize M))

/--
The assembly payload projects back to the two theorem-shaped Moise targets
used by the rest of the formalization.
-/
theorem moiseSmoothabilityRecognitionAssemblyPayload_targets
    (payload : MoiseSmoothabilityRecognitionAssemblyPayload.{u}) :
    MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} :=
  ⟨payload.smoothMoise, payload.surgeryMoise⟩

/--
The Moise smoothability assembly payload exposes, target-by-target, the
recognition witnesses in both sphere and one-point models, the stronger `C∞`
smoothability witness, the lowered surgery-model witness, and the transported
surgery prerequisites.
-/
theorem moiseSmoothabilityRecognitionAssemblyPayload_targetFamily
    (payload : MoiseSmoothabilityRecognitionAssemblyPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          AdmitsSmoothThreeManifoldStructure M ∧
          AdmitsSurgeryModelSmoothStructure M ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
              Nonempty M) := by
  intro M _top _t2 _charted _simple _compact
  exact
    ⟨ payload.recognizedSphere M
    , payload.recognizedOnePoint M
    , payload.smoothStructure M
    , payload.surgeryStructure M
    , payload.surgeryPrerequisites M
    ⟩

/--
`ThreeSphere` recognition constructs the full per-target Moise smoothability
family directly.
-/
theorem moiseSmoothability_targetFamily_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          AdmitsSmoothThreeManifoldStructure M ∧
          AdmitsSurgeryModelSmoothStructure M ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
              Nonempty M) :=
  moiseSmoothabilityRecognitionAssemblyPayload_targetFamily
    (moiseSmoothabilityRecognitionAssemblyPayload_of_threeSphereRecognition
      recognize)

/--
The field-based Moise smoothability assembly payload is equivalent to the
theorem-shaped `ThreeSphere` recognition input: the payload projects recognition
back out, and recognition constructs the full smoothability assembly payload.
-/
theorem nonempty_moiseSmoothabilityRecognitionAssemblyPayload_iff_threeSphereRecognition :
    Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u}) ↔
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) := by
  constructor
  · intro payload
    exact payload.some.recognizedSphere
  · intro recognize
    exact
      ⟨moiseSmoothabilityRecognitionAssemblyPayload_of_threeSphereRecognition
        recognize⟩

/--
Any inhabited Moise smoothability assembly payload supplies the two Moise
targets and the full target-by-target recognition/smoothability/prerequisite
family.
-/
theorem moiseSmoothability_targets_and_family_of_nonemptyAssemblyPayload
    (payload : Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u})) :
    MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            AdmitsSmoothThreeManifoldStructure M ∧
            AdmitsSurgeryModelSmoothStructure M ∧
            (∃ _t2 : T2Space M,
              ∃ _charted : ChartedSpace ThreeManifoldModel M,
              ∃ _simple : SimplyConnectedSpace M,
              ∃ _compact : CompactSpace M,
              ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                Nonempty M)) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.smoothMoise
    , payload.surgeryMoise
    , moiseSmoothabilityRecognitionAssemblyPayload_targetFamily payload
    ⟩

/--
An inhabited Moise smoothability assembly payload exposes the concrete payload
object together with the two theorem-shaped Moise targets and every per-target
recognition/smoothability/prerequisite field stored in that same object.
-/
theorem moiseSmoothability_payload_object_targets_and_family_of_nonemptyAssemblyPayload
    (payload : Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u})) :
    ∃ _assemblyPayload : MoiseSmoothabilityRecognitionAssemblyPayload.{u},
      MoiseSmoothThreeManifoldStatement.{u} ∧
        MoiseSmoothabilityStatement.{u} ∧
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            Nonempty (M ≃ₜ ThreeSphere) ∧
              Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
              AdmitsSmoothThreeManifoldStructure M ∧
              AdmitsSurgeryModelSmoothStructure M ∧
              (∃ _t2 : T2Space M,
                ∃ _charted : ChartedSpace ThreeManifoldModel M,
                ∃ _simple : SimplyConnectedSpace M,
                ∃ _compact : CompactSpace M,
                ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                  Nonempty M)) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload
    , payload.smoothMoise
    , payload.surgeryMoise
    , fun M _top _t2 _charted _simple _compact =>
        ⟨ payload.recognizedSphere M
        , payload.recognizedOnePoint M
        , payload.smoothStructure M
        , payload.surgeryStructure M
        , payload.surgeryPrerequisites M
        ⟩
    ⟩

/--
`ThreeSphere` recognition constructs an inhabited Moise assembly payload and
simultaneously exposes both Moise targets and the transported
recognition/smoothability/prerequisite family.
-/
theorem moiseSmoothability_nonemptyAssemblyPayload_targets_and_family_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            AdmitsSmoothThreeManifoldStructure M ∧
            AdmitsSurgeryModelSmoothStructure M ∧
            (∃ _t2 : T2Space M,
              ∃ _charted : ChartedSpace ThreeManifoldModel M,
              ∃ _simple : SimplyConnectedSpace M,
              ∃ _compact : CompactSpace M,
              ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                Nonempty M)) := by
  let payload :=
    moiseSmoothabilityRecognitionAssemblyPayload_of_threeSphereRecognition
      recognize
  exact
    ⟨ ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , moiseSmoothabilityRecognitionAssemblyPayload_targetFamily payload
    ⟩

/--
An inhabited Moise assembly payload projects to the theorem-shaped
`ThreeSphere` recognition input, both Moise targets, and the transported
recognition/smoothability/prerequisite family.
-/
theorem threeSphereRecognition_targets_and_family_of_nonemptyMoiseAssemblyPayload
    (payload : Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u})) :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            AdmitsSmoothThreeManifoldStructure M ∧
            AdmitsSurgeryModelSmoothStructure M ∧
            (∃ _t2 : T2Space M,
              ∃ _charted : ChartedSpace ThreeManifoldModel M,
              ∃ _simple : SimplyConnectedSpace M,
              ∃ _compact : CompactSpace M,
              ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                Nonempty M)) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.recognizedSphere
    , payload.smoothMoise
    , payload.surgeryMoise
    , moiseSmoothabilityRecognitionAssemblyPayload_targetFamily payload
    ⟩

/--
The exact smoothability package-layer requirement remains the full
`SmoothabilityPackage`; an inhabited Moise assembly payload can be carried
alongside that residual package input without weakening either boundary.
-/
theorem smoothabilityPackage_requirement_threeSphereRecognition_targets_and_family_of_smoothabilityPackage_and_nonemptyMoiseAssemblyPayload
    (smoothability : SmoothabilityPackage.{u})
    (payload : Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u})) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            AdmitsSmoothThreeManifoldStructure M ∧
            AdmitsSurgeryModelSmoothStructure M ∧
            (∃ _t2 : T2Space M,
              ∃ _charted : ChartedSpace ThreeManifoldModel M,
              ∃ _simple : SimplyConnectedSpace M,
              ∃ _compact : CompactSpace M,
              ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                Nonempty M)) :=
  ⟨ by
      simpa [dependencyPackageLayerRequirement] using smoothability
  , threeSphereRecognition_targets_and_family_of_nonemptyMoiseAssemblyPayload
      payload
  ⟩

/--
The residual full `SmoothabilityPackage` input and target-family
`ThreeSphere` recognition construct the Moise recognition assembly payload and
expose the exact package-layer requirement, both Moise targets, and the
transported recognition/smoothability/prerequisite family.  This is the
recognition-driven form of the smoothability boundary consumed by final
assembly: downstream code no longer has to separately build the Moise payload
before carrying the residual package input.
-/
theorem smoothabilityPackage_requirement_nonemptyMoiseAssemblyPayload_targets_and_family_of_smoothabilityPackage_and_threeSphereRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            AdmitsSmoothThreeManifoldStructure M ∧
            AdmitsSurgeryModelSmoothStructure M ∧
            (∃ _t2 : T2Space M,
              ∃ _charted : ChartedSpace ThreeManifoldModel M,
              ∃ _simple : SimplyConnectedSpace M,
              ∃ _compact : CompactSpace M,
              ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                Nonempty M)) := by
  let payload :=
    moiseSmoothabilityRecognitionAssemblyPayload_of_threeSphereRecognition
      recognize
  exact
    ⟨ by
        simpa [dependencyPackageLayerRequirement] using smoothability
    , ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , moiseSmoothabilityRecognitionAssemblyPayload_targetFamily payload
    ⟩

/--
Consumer payload for the smoothability/Moise pillar.  It retains the concrete
Moise recognition assembly payload, the residual smoothability package-layer
requirement, both theorem-shaped Moise targets, the `ThreeSphere` recognition
family, and the full target-by-target recognition/smoothability/prerequisite
family stored in that same payload.
-/
structure MoiseSmoothabilityCompleteConsumerPayload where
  detailedPayload : MoiseSmoothabilityRecognitionAssemblyPayload.{u}
  smoothabilityPackageRequirement :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage
  smoothMoise : MoiseSmoothThreeManifoldStatement.{u}
  surgeryMoise : MoiseSmoothabilityStatement.{u}
  recognizedSphereFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)
  targetFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          AdmitsSmoothThreeManifoldStructure M ∧
          AdmitsSurgeryModelSmoothStructure M ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
              Nonempty M)

/--
An inhabited Moise recognition assembly payload and the residual
`SmoothabilityPackage` construct the complete smoothability consumer payload,
so downstream certificate code can consume one object rather than rebuilding
the Moise assembly and package boundary separately.
-/
theorem moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_nonemptyAssemblyPayload
    (smoothability : SmoothabilityPackage.{u})
    (payload : Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u})) :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ { detailedPayload := payload
        smoothabilityPackageRequirement := by
          simpa [dependencyPackageLayerRequirement] using smoothability
        smoothMoise := payload.smoothMoise
        surgeryMoise := payload.surgeryMoise
        recognizedSphereFamily := payload.recognizedSphere
        targetFamily :=
          moiseSmoothabilityRecognitionAssemblyPayload_targetFamily
            payload } ⟩

/--
The residual `SmoothabilityPackage` and target-family `ThreeSphere`
recognition construct the complete smoothability consumer payload directly,
retaining the concrete Moise recognition assembly object for final-certificate
collapse.
-/
theorem moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_threeSphereRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) :=
  moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_nonemptyAssemblyPayload
    smoothability
    ⟨moiseSmoothabilityRecognitionAssemblyPayload_of_threeSphereRecognition
      recognize⟩

/--
The complete Moise smoothability consumer payload is equivalent to the residual
smoothability package requirement together with an inhabited concrete Moise
recognition assembly payload.  The forward direction projects both fields from
the consumer object; the reverse direction rebuilds the consumer object without
reconstructing recognition data.
-/
theorem nonempty_moiseSmoothabilityCompleteConsumerPayload_iff_smoothabilityPackage_and_nonemptyAssemblyPayload :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ↔
      dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage ∧
        Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u}) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.smoothabilityPackageRequirement
      , ⟨payload.detailedPayload⟩
      ⟩
  · rintro ⟨smoothability, payload⟩
    exact
      moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_nonemptyAssemblyPayload
        (by
          simpa [dependencyPackageLayerRequirement] using smoothability)
        payload

/--
The complete Moise smoothability consumer payload is equivalent to the residual
smoothability package requirement together with the target-family
`ThreeSphere` recognition input.  This composes the assembly-payload boundary
with the exact assembly/recognition equivalence, so downstream final-certificate
consumers can name the mathematical recognition input directly.
-/
theorem nonempty_moiseSmoothabilityCompleteConsumerPayload_iff_smoothabilityPackage_and_threeSphereRecognition :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ↔
      dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage ∧
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            Nonempty (M ≃ₜ ThreeSphere)) := by
  constructor
  · intro payload
    have projected :=
      (nonempty_moiseSmoothabilityCompleteConsumerPayload_iff_smoothabilityPackage_and_nonemptyAssemblyPayload).1
        payload
    exact
      ⟨ projected.1
      , (nonempty_moiseSmoothabilityRecognitionAssemblyPayload_iff_threeSphereRecognition).1
          projected.2
      ⟩
  · rintro ⟨smoothability, recognition⟩
    exact
      (nonempty_moiseSmoothabilityCompleteConsumerPayload_iff_smoothabilityPackage_and_nonemptyAssemblyPayload).2
        ⟨ smoothability
        , (nonempty_moiseSmoothabilityRecognitionAssemblyPayload_iff_threeSphereRecognition).2
            recognition
        ⟩

/--
The complete Moise smoothability consumer payload is also equivalent to the
residual smoothability package requirement together with the full
target-by-target recognition/smoothability/prerequisite family.  The reverse
direction extracts the `ThreeSphere` recognition component from that family and
rebuilds the concrete Moise recognition assembly payload.
-/
theorem nonempty_moiseSmoothabilityCompleteConsumerPayload_iff_smoothabilityPackage_and_targetFamily :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ↔
      dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage ∧
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            Nonempty (M ≃ₜ ThreeSphere) ∧
              Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
              AdmitsSmoothThreeManifoldStructure M ∧
              AdmitsSurgeryModelSmoothStructure M ∧
              (∃ _t2 : T2Space M,
                ∃ _charted : ChartedSpace ThreeManifoldModel M,
                ∃ _simple : SimplyConnectedSpace M,
                ∃ _compact : CompactSpace M,
                ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                  Nonempty M)) := by
  constructor
  · rintro ⟨payload⟩
    exact ⟨payload.smoothabilityPackageRequirement, payload.targetFamily⟩
  · rintro ⟨smoothabilityPackageRequirement, targetFamily⟩
    let recognizedSphereFamily :
        ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            Nonempty (M ≃ₜ ThreeSphere) := by
      intro M _top _t2 _charted _simple _compact
      exact (targetFamily M).1
    exact
      moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_threeSphereRecognition
        (by
          simpa [dependencyPackageLayerRequirement] using
            smoothabilityPackageRequirement)
        recognizedSphereFamily

/--
The complete Moise smoothability consumer payload is exactly a concrete
recognition assembly payload, the residual smoothability package requirement,
both theorem-shaped Moise targets, the `ThreeSphere` recognition family, and
the full target-by-target recognition/smoothability/prerequisite family.  The
reverse direction rebuilds the complete consumer payload from those explicit
fields.
-/
theorem nonempty_moiseSmoothabilityCompleteConsumerPayload_iff_fields :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ↔
      ∃ _assemblyPayload : MoiseSmoothabilityRecognitionAssemblyPayload.{u},
        dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.smoothabilityPackage ∧
          MoiseSmoothThreeManifoldStatement.{u} ∧
          MoiseSmoothabilityStatement.{u} ∧
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M],
              Nonempty (M ≃ₜ ThreeSphere)) ∧
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M],
              Nonempty (M ≃ₜ ThreeSphere) ∧
                Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
                AdmitsSmoothThreeManifoldStructure M ∧
                AdmitsSurgeryModelSmoothStructure M ∧
                (∃ _t2 : T2Space M,
                  ∃ _charted : ChartedSpace ThreeManifoldModel M,
                  ∃ _simple : SimplyConnectedSpace M,
                  ∃ _compact : CompactSpace M,
                  ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                    Nonempty M)) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.detailedPayload
      , payload.smoothabilityPackageRequirement
      , payload.smoothMoise
      , payload.surgeryMoise
      , payload.recognizedSphereFamily
      , payload.targetFamily
      ⟩
  · rintro
      ⟨ assemblyPayload
      , smoothabilityPackageRequirement
      , smoothMoise
      , surgeryMoise
      , recognizedSphereFamily
      , targetFamily
      ⟩
    exact
      ⟨ { detailedPayload := assemblyPayload
          smoothabilityPackageRequirement := smoothabilityPackageRequirement
          smoothMoise := smoothMoise
          surgeryMoise := surgeryMoise
          recognizedSphereFamily := recognizedSphereFamily
          targetFamily := targetFamily } ⟩

/--
An inhabited complete Moise smoothability consumer payload exposes the concrete
assembly object, both theorem-shaped Moise targets, and the target-family
recognition/smoothability/prerequisite payload carried by that same object.
-/
theorem moiseSmoothability_assembly_targets_and_family_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u})) :
    ∃ _assemblyPayload : MoiseSmoothabilityRecognitionAssemblyPayload.{u},
      MoiseSmoothThreeManifoldStatement.{u} ∧
        MoiseSmoothabilityStatement.{u} ∧
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            Nonempty (M ≃ₜ ThreeSphere) ∧
              Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
              AdmitsSmoothThreeManifoldStructure M ∧
              AdmitsSurgeryModelSmoothStructure M ∧
              (∃ _t2 : T2Space M,
                ∃ _charted : ChartedSpace ThreeManifoldModel M,
                ∃ _simple : SimplyConnectedSpace M,
                ∃ _compact : CompactSpace M,
                ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                  Nonempty M)) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.detailedPayload
    , payload.smoothMoise
    , payload.surgeryMoise
    , payload.targetFamily
    ⟩

/--
An inhabited complete Moise smoothability consumer payload exposes the
smoothability package requirement together with both recognition families
carried by the same detailed Moise assembly.
-/
theorem moiseSmoothability_package_recognition_and_targetFamily_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u})) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            AdmitsSmoothThreeManifoldStructure M ∧
            AdmitsSurgeryModelSmoothStructure M ∧
            (∃ _t2 : T2Space M,
              ∃ _charted : ChartedSpace ThreeManifoldModel M,
              ∃ _simple : SimplyConnectedSpace M,
              ∃ _compact : CompactSpace M,
              ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
                Nonempty M)) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , payload.recognizedSphereFamily
    , payload.targetFamily
    ⟩

/--
For a fixed compact simply connected target, a complete Moise smoothability
consumer payload exposes the concrete recognition data, both Moise-shaped
smoothability conclusions, and the surgery-model prerequisite package carried
by the target family.
-/
theorem moiseSmoothability_fixedTarget_recognition_and_smoothability_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      AdmitsSmoothThreeManifoldStructure M ∧
      AdmitsSurgeryModelSmoothStructure M ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) := by
  rcases payload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, hSmooth, hSurgery, hPrereqs⟩
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , hPrereqs
    ⟩

/--
For a fixed compact simply connected target, a complete Moise smoothability
consumer payload exposes the surgery-facing smoothability data: the residual
smoothability package requirement, the one-point model recognition, the
surgery-model smooth structure, and the concrete prerequisite package carrying
a `C¹` surgery-model manifold instance with a nonempty target.
-/
theorem moiseSmoothability_fixedTarget_surgeryModelPrerequisites_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      AdmitsSurgeryModelSmoothStructure M ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) := by
  rcases payload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨_hSphere, hOnePoint, _hSmooth, hSurgery, hPrereqs⟩
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , hOnePoint
    , hSurgery
    , hPrereqs
    ⟩

/--
For a fixed compact simply connected target, a complete Moise smoothability
consumer payload exposes the package requirement, both theorem-shaped Moise
statements, and the concrete recognition/smoothability target package.
-/
theorem moiseSmoothability_targets_and_fixedTarget_recognition_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      AdmitsSmoothThreeManifoldStructure M ∧
      AdmitsSurgeryModelSmoothStructure M ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) := by
  rcases payload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, hSmooth, hSurgery, hPrereqs⟩
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , payload.smoothMoise
    , payload.surgeryMoise
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , hPrereqs
    ⟩

end Poincare
