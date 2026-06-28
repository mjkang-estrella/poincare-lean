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

end Poincare
