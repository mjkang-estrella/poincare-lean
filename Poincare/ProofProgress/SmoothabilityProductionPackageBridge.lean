import Poincare.ProofProgress.SmoothabilityOnePointRecognition
import Poincare.ProofProgress.SmoothabilityProductionPackageBlocker

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Uniform access to the existing smoothability sub-obligation payload for every
compact simply connected charted target.
-/
def UniformSmoothabilitySubobligationsPayload : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      SmoothabilitySubobligationsPayload M

/--
The first package field is already present in any completed smooth-structure
derivation statement.
-/
theorem moiseLocalCharts_of_smoothStructureDerivationStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (derivation : SmoothStructureDerivationStatement M smoothStructure) :
    HasMoiseLocalTriangulationCharts M := by
  rcases derivation with ⟨localCharts, _⟩
  exact localCharts

/-- Transparent projection of the first Moise field from the full payload. -/
def moiseLocalChartsOfSmoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    HasMoiseLocalTriangulationCharts M := by
  rcases payload with ⟨localCharts, _⟩
  exact localCharts

/--
The full smoothability sub-obligation payload closes the first
`SmoothabilityPackage` field.
-/
theorem moiseLocalCharts_of_smoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    HasMoiseLocalTriangulationCharts M :=
  moiseLocalChartsOfSmoothabilitySubobligationsPayload M payload

/--
The same payload also closes the next package field, once the local chart field
is chosen by the payload projection above.
-/
def moiseLocallyFiniteCoverRefinementOfSmoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    HasMoiseLocallyFiniteCoverRefinement M
      (moiseLocalChartsOfSmoothabilitySubobligationsPayload M payload) := by
  rcases payload with ⟨localCharts, locallyFiniteCoverRefinement, _⟩
  simpa [moiseLocalChartsOfSmoothabilitySubobligationsPayload]
    using locallyFiniteCoverRefinement

/--
The full smoothability sub-obligation payload advances the package frontier from
local charts to locally finite cover refinement.
-/
theorem moiseLocallyFiniteCoverRefinement_of_smoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    HasMoiseLocallyFiniteCoverRefinement M
      (moiseLocalChartsOfSmoothabilitySubobligationsPayload M payload) :=
  moiseLocallyFiniteCoverRefinementOfSmoothabilitySubobligationsPayload M payload

/-- The initial Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageInitialMoiseFields where
  moiseLocalCharts :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLocalTriangulationCharts M
  moiseLocallyFiniteCoverRefinement :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLocallyFiniteCoverRefinement M (moiseLocalCharts M)

/--
A uniform smoothability sub-obligation payload constructs the first two Moise
fields of `SmoothabilityPackage`.
-/
def smoothabilityPackageInitialMoiseFieldsOfSubobligationsPayload
    (payload : UniformSmoothabilitySubobligationsPayload.{u}) :
    SmoothabilityPackageInitialMoiseFields.{u} where
  moiseLocalCharts := fun M _ _ _ _ _ =>
    moiseLocalChartsOfSmoothabilitySubobligationsPayload M (payload M)
  moiseLocallyFiniteCoverRefinement := fun M _ _ _ _ _ =>
    moiseLocallyFiniteCoverRefinementOfSmoothabilitySubobligationsPayload
      M (payload M)

/--
The existing full payload is enough to advance past the first
constructor-free field and close the locally finite refinement field.
-/
theorem smoothabilityPackage_firstTwoMoiseFields_of_subobligationsPayload
    (payload : UniformSmoothabilitySubobligationsPayload.{u}) :
    SmoothabilityPackageInitialMoiseFields.{u} :=
  smoothabilityPackageInitialMoiseFieldsOfSubobligationsPayload payload

/--
A completed smoothability package projects to the same first-two-Moise-field
prefix used by this bridge file.  This identifies the local frontier object as
the actual opening segment of `SmoothabilityPackage`.
-/
def smoothabilityPackageInitialMoiseFieldsOfSmoothabilityPackage
    (package : SmoothabilityPackage.{u}) :
    SmoothabilityPackageInitialMoiseFields.{u} where
  moiseLocalCharts := fun M _ _ _ _ _ =>
    moise_local_charts_of_smoothability_package package M
  moiseLocallyFiniteCoverRefinement := fun M _ _ _ _ _ =>
    moise_locally_finite_cover_refinement_of_smoothability_package package M

/--
The package projection supplies exactly the local-chart and locally finite
cover-refinement fields stored in `SmoothabilityPackage`.
-/
theorem smoothabilityPackageInitialMoiseFieldsOfSmoothabilityPackage_fields
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    (smoothabilityPackageInitialMoiseFieldsOfSmoothabilityPackage
        package).moiseLocalCharts M =
        moise_local_charts_of_smoothability_package package M ∧
      (smoothabilityPackageInitialMoiseFieldsOfSmoothabilityPackage
        package).moiseLocallyFiniteCoverRefinement M =
        moise_locally_finite_cover_refinement_of_smoothability_package
          package M := by
  constructor <;> rfl

/--
Both available routes to the initial Moise frontier are exposed together:
completed smoothability packages project to the prefix, while a uniform
sub-obligation payload constructs that same prefix directly.
-/
theorem smoothabilityPackage_initialMoiseFields_package_and_subobligationsPayload
    (package : SmoothabilityPackage.{u})
    (payload : UniformSmoothabilitySubobligationsPayload.{u}) :
    SmoothabilityPackageInitialMoiseFields.{u} ∧
      SmoothabilityPackageInitialMoiseFields.{u} :=
  ⟨ smoothabilityPackageInitialMoiseFieldsOfSmoothabilityPackage package
  , smoothabilityPackageInitialMoiseFieldsOfSubobligationsPayload payload
  ⟩

/--
One-point recognition plus the smoothability sub-obligation payload supplies
the first Moise field on the recognized source.
-/
def OnePointRecognitionSmoothabilitySubobligationsPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
      ∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
        SmoothabilitySubobligationsPayload M

/--
The one-point recognition layer can expose the first package field exactly when
its recognized source is equipped with the smoothability payload.
-/
theorem moiseLocalCharts_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
      HasMoiseLocalTriangulationCharts M := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  exact
    ⟨t2, charted, simple, compact,
      moiseLocalChartsOfSmoothabilitySubobligationsPayload
        M subobligations⟩

/--
With the same recognized-source payload, the next Moise field is available too.
-/
theorem moiseInitialFields_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
      HasMoiseLocallyFiniteCoverRefinement M localCharts := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  let localCharts :=
    moiseLocalChartsOfSmoothabilitySubobligationsPayload M subobligations
  let locallyFiniteCoverRefinement :=
    moiseLocallyFiniteCoverRefinementOfSmoothabilitySubobligationsPayload
      M subobligations
  exact
    ⟨t2, charted, simple, compact, localCharts,
      locallyFiniteCoverRefinement⟩

/--
One-point recognition already supplies the surgery prerequisites; the remaining
extra input for the package frontier is the smoothability payload carrying Moise
local charts.
-/
theorem onePointRecognition_surgeryPrerequisites_and_moiseLocalCharts
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        Nonempty M) ∧
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
        HasMoiseLocalTriangulationCharts M) := by
  exact
    ⟨smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace h,
      moiseLocalCharts_of_onePointRecognition_subobligationsPayload payload h⟩

/--
One-point recognition plus the recognized-source payload supplies the surgery
prerequisites and the first two Moise package fields together.
-/
theorem onePointRecognition_surgeryPrerequisites_and_moiseInitialFields
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        Nonempty M) ∧
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ localCharts : HasMoiseLocalTriangulationCharts M,
        HasMoiseLocallyFiniteCoverRefinement M localCharts) := by
  exact
    ⟨smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace h,
      moiseInitialFields_of_onePointRecognition_subobligationsPayload payload h⟩

/--
One-point recognition plus the recognized-source payload also exposes the
smoothability bridge tail: the chosen smooth structure, derivation statement,
surgery-model manifold evidence, and model/chart compatibility witnesses.
-/
theorem smoothabilityBridgeTail_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
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
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases
    smoothability_bridge_tail_payload_of_subobligations_payload
      M subobligations with
    ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility⟩
  exact
    ⟨t2, charted, simple, compact, smoothStructure,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility⟩

/--
Target-family one-point recognition plus the recognized-source smoothability
payload exposes the bridge-tail smoothability witnesses for every compact
simply connected target.
-/
theorem onePointRecognition_bridgeTail_family
    (recognizeOnePoint :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
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
  intro M _top _t2 _charted _simple _compact
  exact
    smoothabilityBridgeTail_of_onePointRecognition_subobligationsPayload
      payload (recognizeOnePoint M)

/--
A single one-point recognition witness and the recognized-source
smoothability payload expose the fixed-target smoothability assembly prefix:
the recognition witness, transported surgery prerequisites, the first two
Moise package fields, and the bridge-tail smooth-structure/model/chart
compatibility witnesses all come from the same recognized source.
-/
theorem onePointRecognition_smoothabilityAssemblyPrefix_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ localCharts : HasMoiseLocalTriangulationCharts M,
          HasMoiseLocallyFiniteCoverRefinement M localCharts) ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence :
          IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) :=
  ⟨ h
  , (onePointRecognition_surgeryPrerequisites_and_moiseInitialFields
      payload h).1
  , (onePointRecognition_surgeryPrerequisites_and_moiseInitialFields
      payload h).2
  , smoothabilityBridgeTail_of_onePointRecognition_subobligationsPayload
      payload h
  ⟩

/--
Target-family one-point recognition plus the recognized-source smoothability
payload exposes the full smoothability assembly prefix for every compact
simply connected target: the one-point recognition witness, transported surgery
prerequisites, the first two Moise package fields, and the bridge-tail smooth
structure/model/chart-compatibility witnesses produced from the same payload.
-/
theorem onePointRecognition_smoothabilityAssemblyPrefix_family
    (recognizeOnePoint :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
              Nonempty M) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ localCharts : HasMoiseLocalTriangulationCharts M,
              HasMoiseLocallyFiniteCoverRefinement M localCharts) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
            ∃ smoothDerivationStatement :
              SmoothStructureDerivationStatement M smoothStructure,
            ∃ manifoldEvidence :
              IsManifold ThreeManifoldModelWithCorners 1 M,
            ∃ bridgeDerivation :
              HasSmoothabilityBridgeDerivation
                M smoothStructure smoothDerivationStatement
                manifoldEvidence,
            ∃ modelCompatibility :
              HasSmoothManifoldModelCompatibility
                M smoothStructure smoothDerivationStatement manifoldEvidence
                bridgeDerivation,
              HasSmoothChartCompatibility
                M smoothStructure smoothDerivationStatement manifoldEvidence
                bridgeDerivation modelCompatibility) := by
  intro M _top _t2 _charted _simple _compact
  exact
    onePointRecognition_smoothabilityAssemblyPrefix_of_subobligationsPayload
      payload (recognizeOnePoint M)

/--
Uniform smoothability sub-obligation payload for sources recognized as
`ThreeSphere`, matching the topology-recognition output form.
-/
def ThreeSphereRecognitionSmoothabilitySubobligationsPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
    Nonempty (M ≃ₜ ThreeSphere) →
      ∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
        SmoothabilitySubobligationsPayload M

/--
`ThreeSphere` recognition plus its recognized-source payload exposes the first
Moise package field on the source.
-/
theorem moiseLocalCharts_of_threeSphereRecognition_subobligationsPayload
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
      HasMoiseLocalTriangulationCharts M := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  exact
    ⟨t2, charted, simple, compact,
      moiseLocalChartsOfSmoothabilitySubobligationsPayload
        M subobligations⟩

/--
The same `ThreeSphere` recognized-source payload exposes the first two Moise
package fields on the source.
-/
theorem moiseInitialFields_of_threeSphereRecognition_subobligationsPayload
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
      HasMoiseLocallyFiniteCoverRefinement M localCharts := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  let localCharts :=
    moiseLocalChartsOfSmoothabilitySubobligationsPayload M subobligations
  let locallyFiniteCoverRefinement :=
    moiseLocallyFiniteCoverRefinementOfSmoothabilitySubobligationsPayload
      M subobligations
  exact
    ⟨t2, charted, simple, compact, localCharts,
      locallyFiniteCoverRefinement⟩

/--
For the topology route stated as `ThreeSphere` recognition, the transported
one-point smooth atlas supplies surgery prerequisites while the
recognized-source payload supplies the first Moise package field.
-/
theorem threeSphereRecognition_surgeryPrerequisites_and_moiseLocalCharts
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        Nonempty M) ∧
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
        HasMoiseLocalTriangulationCharts M) := by
  exact
    ⟨smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
        (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h),
      moiseLocalCharts_of_threeSphereRecognition_subobligationsPayload
        payload h⟩

/--
For the topology route stated as `ThreeSphere` recognition, the transported
smooth atlas supplies surgery prerequisites while the recognized-source payload
supplies the first two Moise package fields.
-/
theorem threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        Nonempty M) ∧
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ localCharts : HasMoiseLocalTriangulationCharts M,
        HasMoiseLocallyFiniteCoverRefinement M localCharts) := by
  exact
    ⟨smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
        (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h),
      moiseInitialFields_of_threeSphereRecognition_subobligationsPayload
        payload h⟩

/--
Target-family topology recognition plus recognized-source smoothability
sub-obligations expose the transported surgery prerequisites and the first two
Moise package fields for every compact simply connected target.
-/
theorem threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields_family
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere))
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
              Nonempty M) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ localCharts : HasMoiseLocalTriangulationCharts M,
              HasMoiseLocallyFiniteCoverRefinement M localCharts) := by
  intro M _top _t2 _charted _simple _compact
  let h := recognize M
  exact
    ⟨ h
    , (threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields
        payload h).1
    , (threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields
        payload h).2
    ⟩

/--
The same target-family recognition and recognized-source smoothability payload
can be split into the three component families consumed independently by later
smoothability assembly: topology recognition, transported surgery
prerequisites, and the first two Moise package fields.
-/
theorem threeSphereRecognition_componentFamilies_of_recognition_and_subobligationsPayload
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere))
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u}) :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          ∃ _t2 : T2Space M,
          ∃ _charted : ChartedSpace ThreeManifoldModel M,
          ∃ _simple : SimplyConnectedSpace M,
          ∃ _compact : CompactSpace M,
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
            Nonempty M) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          ∃ _t2 : T2Space M,
          ∃ _charted : ChartedSpace ThreeManifoldModel M,
          ∃ _simple : SimplyConnectedSpace M,
          ∃ _compact : CompactSpace M,
          ∃ localCharts : HasMoiseLocalTriangulationCharts M,
            HasMoiseLocallyFiniteCoverRefinement M localCharts) := by
  constructor
  · exact recognize
  constructor
  · intro M _top _t2 _charted _simple _compact
    exact
      (threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields
        payload (recognize M)).1
  · intro M _top _t2 _charted _simple _compact
    exact
      (threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields
        payload (recognize M)).2

/--
For a source recognized as `ThreeSphere`, the recognized-source
smoothability payload reaches the actual bridge tail: the produced smooth
structure, its derivation statement, the surgery-model manifold evidence, and
the bridge/model/chart compatibility witnesses.  This uses the full
`SmoothabilitySubobligationsPayload`, not just its first Moise fields.
-/
theorem smoothabilityBridgeTail_of_threeSphereRecognition_subobligationsPayload
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
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
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases
    smoothability_bridge_tail_payload_of_subobligations_payload
      M subobligations with
    ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility⟩
  exact
    ⟨t2, charted, simple, compact, smoothStructure,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility⟩

/--
Target-family recognition plus recognized-source smoothability payload exposes
the bridge-tail smoothability witnesses for every compact simply connected
target.
-/
theorem threeSphereRecognition_bridgeTail_family
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere))
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        ∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
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
  intro M _top _t2 _charted _simple _compact
  exact
    smoothabilityBridgeTail_of_threeSphereRecognition_subobligationsPayload
      payload (recognize M)

/--
A single `ThreeSphere` recognition witness and the recognized-source
smoothability payload expose the fixed-target smoothability assembly prefix:
recognition, transported surgery prerequisites, the first two Moise fields, and
the bridge-tail smooth-structure/model/chart compatibility witnesses are all
retained for the same source.
-/
theorem threeSphereRecognition_smoothabilityAssemblyPrefix_of_subobligationsPayload
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    Nonempty (M ≃ₜ ThreeSphere) ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          Nonempty M) ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ localCharts : HasMoiseLocalTriangulationCharts M,
          HasMoiseLocallyFiniteCoverRefinement M localCharts) ∧
      (∃ _t2 : T2Space M,
        ∃ _charted : ChartedSpace ThreeManifoldModel M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
        ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ manifoldEvidence :
          IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation,
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation modelCompatibility) :=
  ⟨ h
  , (threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields
      payload h).1
  , (threeSphereRecognition_surgeryPrerequisites_and_moiseInitialFields
      payload h).2
  , smoothabilityBridgeTail_of_threeSphereRecognition_subobligationsPayload
      payload h
  ⟩

/--
Target-family `ThreeSphere` recognition plus the recognized-source
smoothability payload exposes the full smoothability assembly prefix for every
compact simply connected target: the recognition witness, transported surgery
prerequisites, the first two Moise package fields, and the bridge-tail smooth
structure/model/chart-compatibility witnesses produced from the same payload.
-/
theorem threeSphereRecognition_smoothabilityAssemblyPrefix_family
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere))
    (payload : ThreeSphereRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
              Nonempty M) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ localCharts : HasMoiseLocalTriangulationCharts M,
              HasMoiseLocallyFiniteCoverRefinement M localCharts) ∧
          (∃ _t2 : T2Space M,
            ∃ _charted : ChartedSpace ThreeManifoldModel M,
            ∃ _simple : SimplyConnectedSpace M,
            ∃ _compact : CompactSpace M,
            ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
            ∃ smoothDerivationStatement :
              SmoothStructureDerivationStatement M smoothStructure,
            ∃ manifoldEvidence :
              IsManifold ThreeManifoldModelWithCorners 1 M,
            ∃ bridgeDerivation :
              HasSmoothabilityBridgeDerivation
                M smoothStructure smoothDerivationStatement
                manifoldEvidence,
            ∃ modelCompatibility :
              HasSmoothManifoldModelCompatibility
                M smoothStructure smoothDerivationStatement manifoldEvidence
                bridgeDerivation,
              HasSmoothChartCompatibility
                M smoothStructure smoothDerivationStatement manifoldEvidence
                bridgeDerivation modelCompatibility) := by
  intro M _top _t2 _charted _simple _compact
  exact
    threeSphereRecognition_smoothabilityAssemblyPrefix_of_subobligationsPayload
      payload (recognize M)

end Poincare
