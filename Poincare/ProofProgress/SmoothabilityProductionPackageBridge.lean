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

end Poincare
