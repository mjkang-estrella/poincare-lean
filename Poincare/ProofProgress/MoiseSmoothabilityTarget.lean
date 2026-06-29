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
An inhabited Moise recognition assembly payload and the residual
`SmoothabilityPackage` select a complete consumer whose stored fields are the
expected projections from the same assembly payload.  This lets downstream
certificate code keep the complete consumer, the assembly object, both Moise
targets, the `ThreeSphere` recognition family, and the transported
target-family data synchronized without reselecting either payload.
-/
theorem moiseSmoothability_nonemptyAssemblyPayload_selected_completeConsumerPayload_fields
    (smoothability : SmoothabilityPackage.{u})
    (payload : Nonempty (MoiseSmoothabilityRecognitionAssemblyPayload.{u})) :
    ∃ selected : MoiseSmoothabilityCompleteConsumerPayload.{u},
    ∃ assemblyPayload : MoiseSmoothabilityRecognitionAssemblyPayload.{u},
      selected.detailedPayload = assemblyPayload ∧
        selected.smoothMoise = assemblyPayload.smoothMoise ∧
        selected.surgeryMoise = assemblyPayload.surgeryMoise ∧
        selected.recognizedSphereFamily =
          assemblyPayload.recognizedSphere ∧
        selected.targetFamily =
          moiseSmoothabilityRecognitionAssemblyPayload_targetFamily
            assemblyPayload ∧
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
  rcases payload with ⟨assemblyPayload⟩
  let smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage := by
    simpa [dependencyPackageLayerRequirement] using smoothability
  let targetFamily :=
    moiseSmoothabilityRecognitionAssemblyPayload_targetFamily
      assemblyPayload
  let selected : MoiseSmoothabilityCompleteConsumerPayload.{u} :=
    { detailedPayload := assemblyPayload
      smoothabilityPackageRequirement := smoothabilityRequirement
      smoothMoise := assemblyPayload.smoothMoise
      surgeryMoise := assemblyPayload.surgeryMoise
      recognizedSphereFamily := assemblyPayload.recognizedSphere
      targetFamily := targetFamily }
  exact
    ⟨ selected
    , assemblyPayload
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , selected.smoothabilityPackageRequirement
    , selected.smoothMoise
    , selected.surgeryMoise
    , selected.recognizedSphereFamily
    , selected.targetFamily
    ⟩

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
The residual `SmoothabilityPackage` and target-family recognition by the
one-point compactification model construct the complete smoothability consumer
payload directly.  The proof converts the one-point recognition family to the
existing `ThreeSphere` recognition route before building the Moise assembly
payload.
-/
theorem moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_onePointRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognizeOnePoint :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) := by
  let recognizeSphere :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) := by
    intro M _top _t2 _charted _simple _compact
    exact
      homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
        (recognizeOnePoint M)
  exact
    moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_threeSphereRecognition
      smoothability recognizeSphere

/--
The one-point recognition route can select a concrete complete Moise consumer
payload whose stored `ThreeSphere` recognition family is exactly the named
compactification-to-sphere conversion and whose detailed assembly retains the
original one-point recognition input.  This gives compactification-route
consumers a field-synchronized payload without reselecting the converted
recognition family.
-/
theorem moiseSmoothability_onePointRecognition_selected_completeConsumerPayload_fields
    (smoothability : SmoothabilityPackage.{u})
    (recognizeOnePoint :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ selected : MoiseSmoothabilityCompleteConsumerPayload.{u},
      selected.smoothabilityPackageRequirement =
          (by
            simpa [dependencyPackageLayerRequirement] using smoothability) ∧
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            selected.recognizedSphereFamily M =
              homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
                (recognizeOnePoint M)) ∧
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            selected.detailedPayload.recognizedOnePoint M =
              recognizeOnePoint M) ∧
        selected.targetFamily =
          moiseSmoothabilityRecognitionAssemblyPayload_targetFamily
            selected.detailedPayload := by
  let recognizeSphere :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere) := by
    intro M _top _t2 _charted _simple _compact
    exact
      homeomorph_to_threeSphere_of_homeomorph_to_onePoint_threeSpace
        (recognizeOnePoint M)
  let assemblyPayload :=
    moiseSmoothabilityRecognitionAssemblyPayload_of_threeSphereRecognition
      recognizeSphere
  let smoothabilityRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage := by
    simpa [dependencyPackageLayerRequirement] using smoothability
  let selected : MoiseSmoothabilityCompleteConsumerPayload.{u} :=
    { detailedPayload := assemblyPayload
      smoothabilityPackageRequirement := smoothabilityRequirement
      smoothMoise := assemblyPayload.smoothMoise
      surgeryMoise := assemblyPayload.surgeryMoise
      recognizedSphereFamily := assemblyPayload.recognizedSphere
      targetFamily :=
        moiseSmoothabilityRecognitionAssemblyPayload_targetFamily
          assemblyPayload }
  refine ⟨selected, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro M _top _t2 _charted _simple _compact
    rfl
  · intro M _top _t2 _charted _simple _compact
    apply Subsingleton.elim
  · rfl

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
The complete Moise smoothability consumer payload is equivalent to the residual
smoothability package requirement together with target-family recognition by
the one-point compactification model.  The forward direction projects the
stored one-point recognition field from the complete target family; the reverse
direction uses the proved conversion from one-point recognition to the
`ThreeSphere` assembly route.
-/
theorem nonempty_moiseSmoothabilityCompleteConsumerPayload_iff_smoothabilityPackage_and_onePointRecognition :
    Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ↔
      dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage ∧
        (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M],
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.smoothabilityPackageRequirement
      , fun M _top _t2 _charted _simple _compact =>
          (payload.targetFamily M).2.1
      ⟩
  · rintro ⟨smoothability, recognizeOnePoint⟩
    exact
      moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_onePointRecognition
        (by
          simpa [dependencyPackageLayerRequirement] using smoothability)
        recognizeOnePoint

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

/--
For a fixed compact simply connected target, the complete Moise consumer
payload can be unpacked all the way to concrete charted-space witnesses: one
for the transported `C∞` smooth structure, one for the lowered surgery-model
`C¹` structure, and the full surgery-prerequisite package carried by the same
target family.
-/
theorem moiseSmoothability_fixedTarget_concrete_smooth_and_surgery_structures_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      (∃ _smoothCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _smooth : IsManifold (𝓡 3) ∞ M,
        ∃ _surgeryCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _surgerySmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smoothPrereq : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) := by
  rcases payload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, hSmooth, hSurgery, hPrereqs⟩
  rcases hSmooth with ⟨smoothCharted, smoothManifold⟩
  rcases hSurgery with ⟨surgeryCharted, surgerySmooth⟩
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , hSphere
    , hOnePoint
    , smoothCharted
    , smoothManifold
    , surgeryCharted
    , surgerySmooth
    , hPrereqs
    ⟩

/--
For a fixed compact simply connected target, the complete Moise consumer
payload also exposes the opening Moise package fields from the stored
`SmoothabilityPackage`, together with the same recognition and transported
smooth/surgery structures.  This ties the package-layer requirement to
concrete package data instead of only to theorem-shaped smoothability targets.
-/
theorem moiseSmoothability_fixedTarget_packageMoisePrefix_and_concrete_structures_of_completeConsumerPayload
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
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
        ∃ _locallyFinite :
          HasMoiseLocallyFiniteCoverRefinement M localCharts,
        ∃ simplicial :
          HasMoiseSimplicialComplex M localCharts,
        ∃ _compatible :
          HasMoiseCompatibleChartTriangulations M localCharts simplicial,
          HasMoiseTriangulation M) ∧
      (∃ _smoothCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _smooth : IsManifold (𝓡 3) ∞ M,
        ∃ _surgeryCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _surgerySmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smoothPrereq : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) := by
  rcases payload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, hSmooth, hSurgery, hPrereqs⟩
  let package : SmoothabilityPackage.{u} :=
    payload.smoothabilityPackageRequirement
  let localCharts : HasMoiseLocalTriangulationCharts M :=
    moise_local_charts_of_smoothability_package package M
  have _locallyFinite :
      HasMoiseLocallyFiniteCoverRefinement M localCharts := by
    simpa [localCharts] using
      moise_locally_finite_cover_refinement_of_smoothability_package
        package M
  let simplicial : HasMoiseSimplicialComplex M localCharts :=
    moise_simplicial_complex_of_smoothability_package package M
  have _compatible :
      HasMoiseCompatibleChartTriangulations M localCharts simplicial := by
    simpa [localCharts, simplicial] using
      moise_compatible_chart_triangulations_of_smoothability_package
        package M
  let triangulation :=
    moise_triangulation_of_smoothability_package package M
  rcases hSmooth with ⟨smoothCharted, smoothManifold⟩
  rcases hSurgery with ⟨surgeryCharted, surgerySmooth⟩
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , hSphere
    , hOnePoint
    , ⟨smoothCharted, smoothManifold⟩
    , ⟨surgeryCharted, surgerySmooth⟩
    , ⟨localCharts, _locallyFinite, simplicial, _compatible, triangulation⟩
    , ⟨smoothCharted, smoothManifold, surgeryCharted, surgerySmooth, hPrereqs⟩
    ⟩

/--
For a fixed compact simply connected target, the complete Moise consumer
payload projects the actual package-level smooth-structure derivation
statement, while preserving the same transported smooth and surgery-model
witnesses needed by downstream Ricci-flow consumers.
-/
theorem moiseSmoothability_fixedTarget_derivation_statement_and_concrete_structures_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        SmoothStructureDerivationStatement M smoothStructure) ∧
      (∃ _smoothCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _smooth : IsManifold (𝓡 3) ∞ M,
        ∃ _surgeryCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _surgerySmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smoothPrereq : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) := by
  rcases payload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, hSmooth, hSurgery, hPrereqs⟩
  let package : SmoothabilityPackage.{u} :=
    payload.smoothabilityPackageRequirement
  let smoothStructure : HasThreeManifoldSmoothStructure M :=
    smooth_structure_of_smoothability_package package M
  have smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure := by
    simpa [smoothStructure] using
      smooth_structure_derivation_statement_of_smoothability_package
        package M
  rcases hSmooth with ⟨smoothCharted, smoothManifold⟩
  rcases hSurgery with ⟨surgeryCharted, surgerySmooth⟩
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , hSphere
    , hOnePoint
    , ⟨smoothStructure, smoothDerivationStatement⟩
    , ⟨smoothCharted, smoothManifold, surgeryCharted, surgerySmooth, hPrereqs⟩
    ⟩

/--
For a fixed compact simply connected target, the complete Moise consumer
payload exposes the package bridge tail: the smooth-structure derivation
statement, the resulting surgery-model manifold evidence, and the bridge,
model, and chart compatibility certificates from the same package.
-/
theorem moiseSmoothability_fixedTarget_bridge_tail_of_completeConsumerPayload
    (payload : Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) := by
  rcases payload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, _hSmooth, _hSurgery, _hPrereqs⟩
  let package : SmoothabilityPackage.{u} :=
    payload.smoothabilityPackageRequirement
  let smoothStructure : HasThreeManifoldSmoothStructure M :=
    package.smoothStructure M
  let smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure :=
    smooth_structure_derivation_statement_of_components M
      (package.moiseLocalCharts M)
      (package.moiseLocallyFiniteCoverRefinement M)
      (package.moiseSimplicialComplex M)
      (package.moiseCompatibleChartTriangulations M)
      (package.moiseTriangulation M)
      (package.moiseSimplicialApproximation M)
      (package.moiseStarNeighborhoodBasis M)
      (package.moiseBarycentricSubdivision M)
      (package.moiseRegularNeighborhoodCompatibility M)
      (package.moiseTriangulationLocalFiniteness M)
      (package.moiseLinkCompatibility M)
      (package.moisePLManifoldRecognition M)
      (package.moiseTriangulationHomeomorphism M)
      (package.moiseCompatibility M)
      (package.moiseTriangulationUniqueness M)
      (package.moiseHauptvermutungDimensionThree M)
      (package.plStructure M)
      (package.plTransitionCompatibility M)
      (package.plAtlas M)
      (package.plManifoldAtlas M)
      (package.plCollarNeighborhoodCompatibility M)
      (package.plHomeomorphismCompatibility M)
      (package.plAtlasMaximality M)
      (package.plSmoothingExistence M)
      (package.plSmoothingObstructionVanishing M)
      (package.plMicrobundleSmoothing M)
      (package.plSmoothing M)
      (package.plSmoothingCompatibility M)
      (package.plSmoothingUniqueness M)
      (package.plSmoothingLocalModelCompatibility M)
      (package.smoothStructure M)
      (package.smoothAtlasConstruction M)
      (package.smoothAtlasPLCompatibility M)
      (package.smoothAtlasMaximality M)
      (package.smoothAtlasUniqueness M)
      (package.smoothStructureUniquenessUpToDiffeomorphism M)
      (package.smoothTransitionCompatibility M)
      (package.smoothAtlasTransitionSmoothness M)
      (package.smoothStructureDerivation M)
  let manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M :=
    package.bridge M smoothStructure smoothDerivationStatement
  have bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence := by
    simpa [package, smoothStructure, smoothDerivationStatement,
      manifoldEvidence] using package.bridgeDerivation M
  have modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation := by
    simpa [package, smoothStructure, smoothDerivationStatement,
      manifoldEvidence, bridgeDerivation] using
        package.smoothModelCompatibility M
  have chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility := by
    simpa [package, smoothStructure, smoothDerivationStatement,
      manifoldEvidence, bridgeDerivation, modelCompatibility] using
        package.chartCompatibility M
  exact
    ⟨ payload.smoothabilityPackageRequirement
    , hSphere
    , hOnePoint
    , smoothStructure
    , smoothDerivationStatement
    , manifoldEvidence
    , bridgeDerivation
    , modelCompatibility
    , chartCompatibility
    ⟩

/--
For a fixed compact simply connected target, the complete Moise consumer
payload exposes the package Moise prefix, the transported concrete
smooth/surgery witnesses, the full surgery-prerequisite package, and the
smoothability bridge tail from one selected consumer.  This keeps the
transported witness data needed by surgery consumers synchronized with the
bridge-compatibility certificates produced by the residual smoothability
package.
-/
theorem moiseSmoothability_fixedTarget_packageMoisePrefix_concrete_structures_and_bridge_tail_of_completeConsumerPayload
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
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
        ∃ _locallyFinite :
          HasMoiseLocallyFiniteCoverRefinement M localCharts,
        ∃ simplicial :
          HasMoiseSimplicialComplex M localCharts,
        ∃ _compatible :
          HasMoiseCompatibleChartTriangulations M localCharts simplicial,
          HasMoiseTriangulation M) ∧
      (∃ _smoothCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _smooth : IsManifold (𝓡 3) ∞ M,
        ∃ _surgeryCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _surgerySmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smoothPrereq : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) ∧
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothDerivationStatement :
        SmoothStructureDerivationStatement M smoothStructure,
      ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ bridgeDerivation :
        HasSmoothabilityBridgeDerivation
          M smoothStructure smoothDerivationStatement manifoldEvidence,
      ∃ modelCompatibility :
        HasSmoothManifoldModelCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation,
        HasSmoothChartCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation modelCompatibility := by
  rcases
    moiseSmoothability_fixedTarget_packageMoisePrefix_and_concrete_structures_of_completeConsumerPayload
      payload M with
    ⟨ smoothabilityRequirement
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , concretePrereqs
    ⟩
  rcases
    moiseSmoothability_fixedTarget_bridge_tail_of_completeConsumerPayload
      payload M with
    ⟨ _smoothabilityRequirementBridge
    , _hSphereBridge
    , _hOnePointBridge
    , bridgeTail
    ⟩
  exact
    ⟨ smoothabilityRequirement
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , concretePrereqs
    , bridgeTail
    ⟩

/--
`ThreeSphere` recognition plus the residual smoothability package constructs
the complete Moise consumer payload and, for a fixed target, exposes the same
package bridge tail: smooth-structure derivation, surgery-model manifold
evidence, bridge derivation, model compatibility, and chart compatibility.
-/
theorem smoothabilityPackage_requirement_completeMoiseConsumer_and_fixedTarget_bridge_tail_of_smoothabilityPackage_and_threeSphereRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognizeSphere :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) := by
  let completePayload :=
    moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_threeSphereRecognition
      smoothability recognizeSphere
  rcases completePayload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, _hSmooth, _hSurgery, _hPrereqs⟩
  rcases
    moiseSmoothability_fixedTarget_bridge_tail_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨smoothabilityRequirement, _hSphereBridge, _hOnePointBridge,
      bridgeTail⟩
  exact
    ⟨ smoothabilityRequirement
    , ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , hSphere
    , hOnePoint
    , bridgeTail
    ⟩

/--
One-point recognition plus the residual smoothability package constructs the
complete Moise consumer payload and, for a fixed target, exposes the same
package bridge tail: smooth-structure derivation, surgery-model manifold
evidence, bridge derivation, model compatibility, and chart compatibility.
-/
theorem smoothabilityPackage_requirement_completeMoiseConsumer_and_fixedTarget_bridge_tail_of_smoothabilityPackage_and_onePointRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognizeOnePoint :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) := by
  let completePayload :=
    moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_onePointRecognition
      smoothability recognizeOnePoint
  rcases completePayload with ⟨payload⟩
  rcases payload.targetFamily M with
    ⟨hSphere, hOnePoint, _hSmooth, _hSurgery, _hPrereqs⟩
  rcases
    moiseSmoothability_fixedTarget_bridge_tail_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨smoothabilityRequirement, _hSphereBridge, _hOnePointBridge,
      bridgeTail⟩
  exact
    ⟨ smoothabilityRequirement
    , ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , hSphere
    , hOnePoint
    , bridgeTail
    ⟩

/--
`ThreeSphere` recognition plus the residual smoothability package constructs
the complete Moise consumer payload and keeps the fixed-target Moise package
prefix synchronized with the bridge tail.  Downstream certificate assembly can
therefore consume the triangulation prefix, transported smooth/surgery
structures, and smoothability bridge compatibility data from one endpoint.
-/
theorem smoothabilityPackage_requirement_completeMoiseConsumer_fixedTarget_packageMoisePrefix_and_bridge_tail_of_smoothabilityPackage_and_threeSphereRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognizeSphere :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      AdmitsSmoothThreeManifoldStructure M ∧
      AdmitsSurgeryModelSmoothStructure M ∧
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
        ∃ _locallyFinite :
          HasMoiseLocallyFiniteCoverRefinement M localCharts,
        ∃ simplicial :
          HasMoiseSimplicialComplex M localCharts,
        ∃ _compatible :
          HasMoiseCompatibleChartTriangulations M localCharts simplicial,
          HasMoiseTriangulation M) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) := by
  let completePayload :=
    moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_threeSphereRecognition
      smoothability recognizeSphere
  rcases completePayload with ⟨payload⟩
  rcases
    moiseSmoothability_fixedTarget_packageMoisePrefix_and_concrete_structures_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨ smoothabilityRequirement
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , _concretePrereqs
    ⟩
  rcases
    moiseSmoothability_fixedTarget_bridge_tail_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨_smoothabilityRequirementBridge, _hSphereBridge, _hOnePointBridge,
      bridgeTail⟩
  exact
    ⟨ smoothabilityRequirement
    , ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , bridgeTail
    ⟩

/--
`ThreeSphere` recognition plus the residual smoothability package also
preserves the transported concrete smooth/surgery prerequisite tuple while
exposing the Moise package prefix and bridge tail.  This is the stronger
direct-recognition endpoint for consumers that need the actual transported
smooth and surgery-model witnesses, not only the theorem-shaped smoothability
conclusions.
-/
theorem smoothabilityPackage_requirement_completeMoiseConsumer_fixedTarget_packageMoisePrefix_concrete_structures_and_bridge_tail_of_smoothabilityPackage_and_threeSphereRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognizeSphere :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      AdmitsSmoothThreeManifoldStructure M ∧
      AdmitsSurgeryModelSmoothStructure M ∧
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
        ∃ _locallyFinite :
          HasMoiseLocallyFiniteCoverRefinement M localCharts,
        ∃ simplicial :
          HasMoiseSimplicialComplex M localCharts,
        ∃ _compatible :
          HasMoiseCompatibleChartTriangulations M localCharts simplicial,
          HasMoiseTriangulation M) ∧
      (∃ _smoothCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _smooth : IsManifold (𝓡 3) ∞ M,
        ∃ _surgeryCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _surgerySmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smoothPrereq : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) := by
  let completePayload :=
    moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_threeSphereRecognition
      smoothability recognizeSphere
  rcases completePayload with ⟨payload⟩
  rcases
    moiseSmoothability_fixedTarget_packageMoisePrefix_concrete_structures_and_bridge_tail_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨ smoothabilityRequirement
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , concretePrereqs
    , bridgeTail
    ⟩
  exact
    ⟨ smoothabilityRequirement
    , ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , concretePrereqs
    , bridgeTail
    ⟩

/--
One-point recognition plus the residual smoothability package constructs the
complete Moise consumer payload and keeps the fixed-target Moise package prefix
synchronized with the bridge tail.  This is the one-point compactification
counterpart of the `ThreeSphere` endpoint above, so downstream consumers that
already operate on the compactification recognition route do not need to
reconstruct the complete payload before accessing the triangulation prefix and
smoothability bridge compatibility data.
-/
theorem smoothabilityPackage_requirement_completeMoiseConsumer_fixedTarget_packageMoisePrefix_and_bridge_tail_of_smoothabilityPackage_and_onePointRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognizeOnePoint :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      AdmitsSmoothThreeManifoldStructure M ∧
      AdmitsSurgeryModelSmoothStructure M ∧
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
        ∃ _locallyFinite :
          HasMoiseLocallyFiniteCoverRefinement M localCharts,
        ∃ simplicial :
          HasMoiseSimplicialComplex M localCharts,
        ∃ _compatible :
          HasMoiseCompatibleChartTriangulations M localCharts simplicial,
          HasMoiseTriangulation M) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) := by
  let completePayload :=
    moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_onePointRecognition
      smoothability recognizeOnePoint
  rcases completePayload with ⟨payload⟩
  rcases
    moiseSmoothability_fixedTarget_packageMoisePrefix_and_concrete_structures_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨ smoothabilityRequirement
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , _concretePrereqs
    ⟩
  rcases
    moiseSmoothability_fixedTarget_bridge_tail_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨_smoothabilityRequirementBridge, _hSphereBridge, _hOnePointBridge,
      bridgeTail⟩
  exact
    ⟨ smoothabilityRequirement
    , ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , bridgeTail
    ⟩

/--
One-point recognition plus the residual smoothability package also preserves
the transported concrete smooth/surgery prerequisite tuple while exposing the
Moise package prefix and bridge tail.  This is the stronger one-point
compactification endpoint for consumers that need the actual prerequisite
witnesses, not only the theorem-shaped smoothability conclusions.
-/
theorem smoothabilityPackage_requirement_completeMoiseConsumer_fixedTarget_packageMoisePrefix_concrete_structures_and_bridge_tail_of_smoothabilityPackage_and_onePointRecognition
    (smoothability : SmoothabilityPackage.{u})
    (recognizeOnePoint :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      Nonempty (MoiseSmoothabilityCompleteConsumerPayload.{u}) ∧
      MoiseSmoothThreeManifoldStatement.{u} ∧
      MoiseSmoothabilityStatement.{u} ∧
      Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      AdmitsSmoothThreeManifoldStructure M ∧
      AdmitsSurgeryModelSmoothStructure M ∧
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
        ∃ _locallyFinite :
          HasMoiseLocallyFiniteCoverRefinement M localCharts,
        ∃ simplicial :
          HasMoiseSimplicialComplex M localCharts,
        ∃ _compatible :
          HasMoiseCompatibleChartTriangulations M localCharts simplicial,
          HasMoiseTriangulation M) ∧
      (∃ _smoothCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _smooth : IsManifold (𝓡 3) ∞ M,
        ∃ _surgeryCharted : ChartedSpace ThreeManifoldModel M,
        ∃ _surgerySmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smoothPrereq : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) ∧
      (∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) := by
  let completePayload :=
    moiseSmoothability_completeConsumerPayload_of_smoothabilityPackage_and_onePointRecognition
      smoothability recognizeOnePoint
  rcases completePayload with ⟨payload⟩
  rcases
    moiseSmoothability_fixedTarget_packageMoisePrefix_concrete_structures_and_bridge_tail_of_completeConsumerPayload
      ⟨payload⟩ M with
    ⟨ smoothabilityRequirement
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , concretePrereqs
    , bridgeTail
    ⟩
  exact
    ⟨ smoothabilityRequirement
    , ⟨payload⟩
    , payload.smoothMoise
    , payload.surgeryMoise
    , hSphere
    , hOnePoint
    , hSmooth
    , hSurgery
    , packagePrefix
    , concretePrereqs
    , bridgeTail
    ⟩

end Poincare
