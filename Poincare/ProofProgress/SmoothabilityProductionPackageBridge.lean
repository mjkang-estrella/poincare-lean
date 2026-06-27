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
The same recognized-source payload reaches the third Moise field, so the
one-point recognition route now exposes local charts, the locally finite cover
refinement, and the simplicial-complex witness together.
-/
theorem moiseSimplicialFields_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
      HasMoiseSimplicialComplex M localCharts := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases subobligations with
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex, _rest⟩
  exact
    ⟨t2, charted, simple, compact, localCharts,
      locallyFiniteCoverRefinement, simplicialComplex⟩

/-- Theorem contract for `moiseSimplicialFields_of_onePointRecognition_subobligationsPayload`. -/
theorem moiseSimplicialFields_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.moiseSimplicialFields_of_onePointRecognition_subobligationsPayload =
      @Poincare.moiseSimplicialFields_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The recognized-source payload advances beyond the first three Moise fields:
it also exposes compatible chart triangulations and a global Moise
triangulation witness tied to those same local charts and simplicial complex.
-/
theorem moiseChartTriangulationFields_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts simplicialComplex,
      HasMoiseTriangulation M := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases subobligations with
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation, _rest⟩
  exact
    ⟨t2, charted, simple, compact, localCharts,
      locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation⟩

/-- Theorem contract for `moiseChartTriangulationFields_of_onePointRecognition_subobligationsPayload`. -/
theorem moiseChartTriangulationFields_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.moiseChartTriangulationFields_of_onePointRecognition_subobligationsPayload =
      @Poincare.moiseChartTriangulationFields_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The full smoothability sub-obligation payload projects the Moise-to-PL frontier
from local charts through compatible PL atlas construction.
-/
theorem moiseToPLFrontier_of_smoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ triangulationUniqueness : HasMoiseTriangulationUniqueness M triangulation,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
      HasMoiseLocallyFiniteCoverRefinement M localCharts ∧
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex ∧
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility ∧
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation ∧
      HasMoiseTriangulationCompatibility M
        localCharts triangulation ∧
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness ∧
      HasPLTransitionCompatibility M triangulation plStructure ∧
      HasCompatiblePLAtlas M triangulation plStructure := by
  rcases payload with
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation,
      _simplicialApproximation, _starNeighborhoodBasis,
      _barycentricSubdivision, _regularNeighborhoodCompatibility,
      _triangulationLocalFiniteness, linkCompatibility,
      plManifoldRecognition, triangulationHomeomorphism,
      moiseCompatibility, triangulationUniqueness,
      hauptvermutungDimensionThree, plStructure,
      plTransitionCompatibility, plAtlas, _rest⟩
  exact
    ⟨localCharts, simplicialComplex, triangulation, linkCompatibility,
      triangulationUniqueness, plStructure, locallyFiniteCoverRefinement,
      compatibleChartTriangulations, plManifoldRecognition,
      triangulationHomeomorphism, moiseCompatibility,
      hauptvermutungDimensionThree, plTransitionCompatibility, plAtlas⟩

/--
The full smoothability sub-obligation payload also projects the PL-to-smooth
frontier: smoothing existence and obstruction-vanishing data lead through the
PL smoothing theorem to a smooth structure, compatible smooth atlas, uniqueness
data, and transition-map smoothness.
-/
theorem plToSmoothFrontier_of_smoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing ∧
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing ∧
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing ∧
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction ∧
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
      HasSmoothAtlasUniqueness M smoothStructure ∧
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility := by
  rcases payload with
    ⟨_localCharts, _locallyFiniteCoverRefinement, _simplicialComplex,
      _compatibleChartTriangulations, triangulation,
      _simplicialApproximation, _starNeighborhoodBasis,
      _barycentricSubdivision, _regularNeighborhoodCompatibility,
      _triangulationLocalFiniteness, _linkCompatibility,
      _plManifoldRecognition, _triangulationHomeomorphism,
      _moiseCompatibility, _triangulationUniqueness,
      _hauptvermutungDimensionThree, plStructure,
      _plTransitionCompatibility, plAtlas, _plManifoldAtlas,
      _plCollarNeighborhoodCompatibility, _plHomeomorphismCompatibility,
      _plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing,
      plSmoothing, plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothAtlasUniqueness,
      smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, _rest⟩
  exact
    ⟨triangulation, plStructure, plAtlas, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing,
      plSmoothing, smoothStructure, smoothAtlasConstruction,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothAtlasUniqueness,
      smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness⟩

/--
The full smoothability payload keeps the actual smooth-structure derivation
witness and the smooth atlas/transition witnesses available before the bridge
tail packages them for the surgery interface.
-/
theorem smoothability_derivation_and_transition_payload_of_subobligations_payload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation,
    ∃ starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility,
    ∃ triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation,
    ∃ moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas,
    ∃ plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing,
    ∃ plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
    ∃ smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
    ∃ smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
    ∃ smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility,
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation
        M localCharts locallyFiniteCoverRefinement simplicialComplex
        compatibleChartTriangulations triangulation simplicialApproximation
        starNeighborhoodBasis barycentricSubdivision
        regularNeighborhoodCompatibility triangulationLocalFiniteness
        linkCompatibility plManifoldRecognition triangulationHomeomorphism
        moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
        plStructure plTransitionCompatibility plAtlas plManifoldAtlas
        plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
        plAtlasMaximality plSmoothingExistence
        plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
        plSmoothingCompatibility plSmoothingUniqueness
        plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness,
      SmoothStructureDerivationStatement M smoothStructure := by
  rcases payload with
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation, simplicialApproximation,
      starNeighborhoodBasis, barycentricSubdivision,
      regularNeighborhoodCompatibility, triangulationLocalFiniteness,
      linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
      moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
      plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
      plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
      plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing, plSmoothing,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivation, smoothDerivationStatement, _manifoldEvidence,
      _bridgeDerivation, _modelCompatibility, _chartCompatibility⟩
  exact
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation, simplicialApproximation,
      starNeighborhoodBasis, barycentricSubdivision,
      regularNeighborhoodCompatibility, triangulationLocalFiniteness,
      linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
      moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
      plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
      plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
      plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing, plSmoothing,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivation, smoothDerivationStatement⟩

/--
The smoothability payload also exposes the one-point-recognition coherence
carried by the terminal smooth transition data: the smooth structure,
transition compatibility, and transition-smoothness witnesses are all tied to
one recognition input.
-/
theorem smoothability_transition_recognition_coherence_of_subobligations_payload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility,
      SmoothStructureDerivationStatement M smoothStructure ∧
        ∃ h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))),
        ∃ hSmooth :
          smoothStructure =
            HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
          smoothTransitionCompatibility =
            HasSmoothTransitionCompatibility.ofOnePointRecognition h hSmooth ∧
          smoothAtlasTransitionSmoothness.onePointRecognition = h := by
  rcases smoothability_derivation_and_transition_payload_of_subobligations_payload
      M payload with
    ⟨_localCharts, _locallyFiniteCoverRefinement, _simplicialComplex,
      _compatibleChartTriangulations, _triangulation,
      _simplicialApproximation, _starNeighborhoodBasis,
      _barycentricSubdivision, _regularNeighborhoodCompatibility,
      _triangulationLocalFiniteness, _linkCompatibility,
      _plManifoldRecognition, _triangulationHomeomorphism,
      _moiseCompatibility, _triangulationUniqueness,
      _hauptvermutungDimensionThree, _plStructure,
      _plTransitionCompatibility, _plAtlas, _plManifoldAtlas,
      _plCollarNeighborhoodCompatibility, _plHomeomorphismCompatibility,
      _plAtlasMaximality, _plSmoothingExistence,
      _plSmoothingObstructionVanishing, _plMicrobundleSmoothing,
      _plSmoothing, _plSmoothingCompatibility, _plSmoothingUniqueness,
      _plSmoothingLocalModelCompatibility, smoothStructure,
      _smoothAtlasConstruction, _smoothAtlasPLCompatibility,
      _smoothAtlasMaximality, _smoothAtlasUniqueness,
      _smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, _smoothDerivation,
      derivationStatement⟩
  refine
    ⟨smoothStructure, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, derivationStatement,
      smoothAtlasTransitionSmoothness.onePointRecognition,
      smoothAtlasTransitionSmoothness.smoothStructure_eq, ?_, rfl⟩
  exact smoothAtlasTransitionSmoothness.smoothTransitionCompatibility_eq

/--
A recognized one-point source packages the smoothability derivation/transition
payload together with the recognition coherence payload under the same installed
sub-obligation witnesses.
-/
theorem smoothability_derivation_transition_and_recognition_coherence_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _subobligations : SmoothabilitySubobligationsPayload M,
    ∃ _derivationAndTransition :
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
      ∃ locallyFiniteCoverRefinement :
        HasMoiseLocallyFiniteCoverRefinement M localCharts,
      ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ compatibleChartTriangulations :
        HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ simplicialApproximation :
        HasMoiseSimplicialApproximation
          M localCharts simplicialComplex triangulation,
      ∃ starNeighborhoodBasis :
        HasMoiseStarNeighborhoodBasis M localCharts triangulation,
      ∃ barycentricSubdivision :
        HasMoiseBarycentricSubdivisionControl M triangulation,
      ∃ regularNeighborhoodCompatibility :
        HasMoiseRegularNeighborhoodCompatibility M triangulation,
      ∃ triangulationLocalFiniteness :
        HasMoiseTriangulationLocalFiniteness M triangulation,
      ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
      ∃ plManifoldRecognition :
        HasMoisePLManifoldRecognition M triangulation linkCompatibility,
      ∃ triangulationHomeomorphism :
        HasMoiseTriangulationHomeomorphism M localCharts triangulation,
      ∃ moiseCompatibility :
        HasMoiseTriangulationCompatibility M localCharts triangulation,
      ∃ triangulationUniqueness :
        HasMoiseTriangulationUniqueness M triangulation,
      ∃ hauptvermutungDimensionThree :
        HasMoiseHauptvermutungDimensionThree
          M triangulation triangulationUniqueness,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plTransitionCompatibility :
        HasPLTransitionCompatibility M triangulation plStructure,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plManifoldAtlas :
        HasPLManifoldAtlas M triangulation plStructure plAtlas,
      ∃ plCollarNeighborhoodCompatibility :
        HasPLCollarNeighborhoodCompatibility
          M triangulation plStructure plAtlas,
      ∃ plHomeomorphismCompatibility :
        HasPLHomeomorphismCompatibility
          M localCharts triangulation plStructure plAtlas,
      ∃ plAtlasMaximality :
        HasPLAtlasMaximality M triangulation plStructure plAtlas,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
          plSmoothingExistence plSmoothingObstructionVanishing,
      ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ plSmoothingCompatibility :
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingUniqueness :
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingLocalModelCompatibility :
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasPLCompatibility :
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction,
      ∃ smoothAtlasMaximality :
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
      ∃ smoothStructureUniqueness :
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
      ∃ _smoothDerivation :
        HasSmoothStructureDerivation
          M localCharts locallyFiniteCoverRefinement simplicialComplex
          compatibleChartTriangulations triangulation simplicialApproximation
          starNeighborhoodBasis barycentricSubdivision
          regularNeighborhoodCompatibility triangulationLocalFiniteness
          linkCompatibility plManifoldRecognition triangulationHomeomorphism
          moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
          plStructure plTransitionCompatibility plAtlas plManifoldAtlas
          plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
          plAtlasMaximality plSmoothingExistence
          plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
          plSmoothingCompatibility plSmoothingUniqueness
          plSmoothingLocalModelCompatibility smoothStructure
          smoothAtlasConstruction smoothAtlasPLCompatibility
          smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
          smoothTransitionCompatibility smoothAtlasTransitionSmoothness,
        SmoothStructureDerivationStatement M smoothStructure),
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
        SmoothStructureDerivationStatement M smoothStructure ∧
          ∃ h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))),
          ∃ hSmooth :
            smoothStructure =
              HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
            smoothTransitionCompatibility =
              HasSmoothTransitionCompatibility.ofOnePointRecognition h hSmooth ∧
            smoothAtlasTransitionSmoothness.onePointRecognition = h := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  exact
    ⟨t2, charted, simple, compact, subobligations,
      smoothability_derivation_and_transition_payload_of_subobligations_payload
        M subobligations,
      smoothability_transition_recognition_coherence_of_subobligations_payload
        M subobligations⟩

/-- One-point-recognition subobligations project the Moise-to-PL frontier. -/
theorem moiseToPLFrontier_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ triangulationUniqueness : HasMoiseTriangulationUniqueness M triangulation,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
      HasMoiseLocallyFiniteCoverRefinement M localCharts ∧
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex ∧
      HasMoisePLManifoldRecognition M triangulation linkCompatibility ∧
      HasMoiseTriangulationHomeomorphism M localCharts triangulation ∧
      HasMoiseTriangulationCompatibility M localCharts triangulation ∧
      HasMoiseHauptvermutungDimensionThree M triangulation triangulationUniqueness ∧
      HasPLTransitionCompatibility M triangulation plStructure ∧
      HasCompatiblePLAtlas M triangulation plStructure := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases moiseToPLFrontier_of_smoothabilitySubobligationsPayload
      M subobligations with
    ⟨localCharts, simplicialComplex, triangulation, linkCompatibility,
      triangulationUniqueness, plStructure, frontier⟩
  exact
    ⟨t2, charted, simple, compact, localCharts, simplicialComplex,
      triangulation, linkCompatibility, triangulationUniqueness,
      plStructure, frontier⟩

/--
One-point-recognition subobligations also project the downstream PL-to-smooth
frontier: after installing the recognized source's topology, charted, simple
connectivity, and compactness witnesses, the full smoothability payload
provides smoothing existence, obstruction vanishing, a smooth structure,
smooth-atlas construction, uniqueness data, and transition-map smoothness.
-/
theorem plToSmoothFrontier_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing ∧
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing ∧
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing ∧
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction ∧
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
      HasSmoothAtlasUniqueness M smoothStructure ∧
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases plToSmoothFrontier_of_smoothabilitySubobligationsPayload
      M subobligations with
    ⟨triangulation, plStructure, plAtlas, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing,
      plSmoothing, smoothStructure, smoothAtlasConstruction, frontier⟩
  exact
    ⟨t2, charted, simple, compact, triangulation, plStructure,
      plAtlas, plSmoothingExistence, plSmoothingObstructionVanishing,
      plMicrobundleSmoothing, plSmoothing, smoothStructure,
      smoothAtlasConstruction, frontier⟩

/--
One-point-recognition subobligations expose the complete chart-level Moise
triangulation frontier and the downstream PL-to-smooth frontier from the same
recognized source payload.
-/
theorem onePointRecognition_moiseChartTriangulationFields_and_plToSmoothFrontier_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ localCharts : HasMoiseLocalTriangulationCharts M,
      ∃ _locallyFiniteCoverRefinement :
        HasMoiseLocallyFiniteCoverRefinement M localCharts,
      ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ _compatibleChartTriangulations :
        HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
        HasMoiseTriangulation M) ∧
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ _plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
          plSmoothingExistence plSmoothingObstructionVanishing,
      ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction ∧
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
        HasSmoothAtlasUniqueness M smoothStructure ∧
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
        ∃ smoothTransitionCompatibility :
          HasSmoothTransitionCompatibility M smoothStructure,
          HasSmoothAtlasTransitionSmoothness
            M smoothStructure smoothTransitionCompatibility) := by
  exact
    ⟨moiseChartTriangulationFields_of_onePointRecognition_subobligationsPayload
        payload h,
      plToSmoothFrontier_of_onePointRecognition_subobligationsPayload
        payload h⟩

/--
Theorem contract for
`onePointRecognition_moiseChartTriangulationFields_and_plToSmoothFrontier_of_subobligationsPayload`.
-/
theorem onePointRecognition_moiseChartTriangulationFields_and_plToSmoothFrontier_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_moiseChartTriangulationFields_and_plToSmoothFrontier_of_subobligationsPayload =
      @Poincare.onePointRecognition_moiseChartTriangulationFields_and_plToSmoothFrontier_of_subobligationsPayload :=
  rfl

/--
One-point-recognition subobligations project the bridge tail consumed by the
smoothability interface: smooth structure, smooth-structure derivation,
manifold evidence, bridge derivation, model compatibility, and chart
compatibility.
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
  rcases smoothability_bridge_tail_payload_of_subobligations_payload
      M subobligations with
    ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility⟩
  exact
    ⟨t2, charted, simple, compact, smoothStructure,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility⟩

/--
The smoothability payload does not merely name the bridge tail: its bridge,
model, and chart compatibility records expose the same derivation and manifold
evidence needed by the surgery-facing smooth manifold interface.
-/
theorem smoothabilityBridgeModelChartWitnesses_of_subobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
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
    ∃ _chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility,
      (SmoothStructureDerivationStatement M smoothStructure ∧
        IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      (SmoothStructureDerivationStatement M smoothStructure ∧
        IsManifold ThreeManifoldModelWithCorners 1 M ∧
        HasSmoothabilityBridgeDerivation
          M smoothStructure smoothDerivationStatement manifoldEvidence) ∧
      (SmoothStructureDerivationStatement M smoothStructure ∧
        IsManifold ThreeManifoldModelWithCorners 1 M ∧
        HasSmoothabilityBridgeDerivation
          M smoothStructure smoothDerivationStatement manifoldEvidence ∧
        HasSmoothManifoldModelCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation) ∧
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility := by
  rcases smoothability_bridge_tail_payload_of_subobligations_payload
      M payload with
    ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility⟩
  exact
    ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility,
      HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation,
      ⟨modelCompatibility.smoothStructureDerivationWitness,
        modelCompatibility.manifoldEvidenceWitness,
        modelCompatibility.bridgeDerivationWitness⟩,
      HasSmoothChartCompatibility.witnesses M chartCompatibility,
      chartCompatibility⟩

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
One-point recognition already supplies the surgery prerequisites; the remaining
extra input for the package frontier is the smoothability payload carrying the
first two Moise fields.
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
One-point recognition supplies the surgery prerequisites while the smoothability
payload advances the recognized source past the initial Moise fields to the
Moise-to-PL frontier.
-/
theorem onePointRecognition_surgeryPrerequisites_and_moiseToPLFrontier
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
      ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
      ∃ triangulationUniqueness : HasMoiseTriangulationUniqueness M triangulation,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
        HasMoiseLocallyFiniteCoverRefinement M localCharts ∧
        HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex ∧
        HasMoisePLManifoldRecognition M triangulation linkCompatibility ∧
        HasMoiseTriangulationHomeomorphism M localCharts triangulation ∧
        HasMoiseTriangulationCompatibility M localCharts triangulation ∧
        HasMoiseHauptvermutungDimensionThree M triangulation triangulationUniqueness ∧
        HasPLTransitionCompatibility M triangulation plStructure ∧
        HasCompatiblePLAtlas M triangulation plStructure) := by
  exact
    ⟨smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace h,
      moiseToPLFrontier_of_onePointRecognition_subobligationsPayload payload h⟩

/--
One-point recognition supplies the surgery prerequisites while the smoothability
payload advances the recognized source through the PL-to-smooth frontier.
-/
theorem onePointRecognition_surgeryPrerequisites_and_plToSmoothFrontier
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
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ _plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
          plSmoothingExistence plSmoothingObstructionVanishing,
      ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction ∧
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
        HasSmoothAtlasUniqueness M smoothStructure ∧
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
        ∃ smoothTransitionCompatibility :
          HasSmoothTransitionCompatibility M smoothStructure,
          HasSmoothAtlasTransitionSmoothness
            M smoothStructure smoothTransitionCompatibility) := by
  exact
    ⟨smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace h,
      plToSmoothFrontier_of_onePointRecognition_subobligationsPayload payload h⟩

/--
One-point recognition supplies the surgery prerequisites while the recognized
source smoothability payload exposes the bridge tail used by the smooth
manifold interface.
-/
theorem onePointRecognition_surgeryPrerequisites_and_bridgeTailWitnesses
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
      ∃ _chartCompatibility :
        HasSmoothChartCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation modelCompatibility,
        (SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M) ∧
        (SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M ∧
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence ∧
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation)) := by
  refine
    ⟨smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace h,
      ?_⟩
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases smoothability_bridge_tail_payload_of_subobligations_payload
      M subobligations with
    ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility⟩
  exact
    ⟨t2, charted, simple, compact, smoothStructure,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility,
      HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation,
      HasSmoothChartCompatibility.witnesses M chartCompatibility⟩

/--
The one-point-recognition payload can be consumed once to expose the
smoothability derivation/transition and recognition coherence endpoint, while
the same recognized source also supplies the surgery prerequisites and the
bridge-tail witnesses used by the smooth manifold interface.
-/
theorem onePointRecognition_smoothabilityDerivation_transition_recognition_surgeryPrerequisites_and_bridgeTailWitnesses
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    (∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _subobligations : SmoothabilitySubobligationsPayload M,
    ∃ _derivationAndTransition :
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
      ∃ locallyFiniteCoverRefinement :
        HasMoiseLocallyFiniteCoverRefinement M localCharts,
      ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ compatibleChartTriangulations :
        HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ simplicialApproximation :
        HasMoiseSimplicialApproximation
          M localCharts simplicialComplex triangulation,
      ∃ starNeighborhoodBasis :
        HasMoiseStarNeighborhoodBasis M localCharts triangulation,
      ∃ barycentricSubdivision :
        HasMoiseBarycentricSubdivisionControl M triangulation,
      ∃ regularNeighborhoodCompatibility :
        HasMoiseRegularNeighborhoodCompatibility M triangulation,
      ∃ triangulationLocalFiniteness :
        HasMoiseTriangulationLocalFiniteness M triangulation,
      ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
      ∃ plManifoldRecognition :
        HasMoisePLManifoldRecognition M triangulation linkCompatibility,
      ∃ triangulationHomeomorphism :
        HasMoiseTriangulationHomeomorphism M localCharts triangulation,
      ∃ moiseCompatibility :
        HasMoiseTriangulationCompatibility M localCharts triangulation,
      ∃ triangulationUniqueness :
        HasMoiseTriangulationUniqueness M triangulation,
      ∃ hauptvermutungDimensionThree :
        HasMoiseHauptvermutungDimensionThree
          M triangulation triangulationUniqueness,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plTransitionCompatibility :
        HasPLTransitionCompatibility M triangulation plStructure,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plManifoldAtlas :
        HasPLManifoldAtlas M triangulation plStructure plAtlas,
      ∃ plCollarNeighborhoodCompatibility :
        HasPLCollarNeighborhoodCompatibility
          M triangulation plStructure plAtlas,
      ∃ plHomeomorphismCompatibility :
        HasPLHomeomorphismCompatibility
          M localCharts triangulation plStructure plAtlas,
      ∃ plAtlasMaximality :
        HasPLAtlasMaximality M triangulation plStructure plAtlas,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
          plSmoothingExistence plSmoothingObstructionVanishing,
      ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ plSmoothingCompatibility :
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingUniqueness :
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingLocalModelCompatibility :
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasPLCompatibility :
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction,
      ∃ smoothAtlasMaximality :
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
      ∃ smoothStructureUniqueness :
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
      ∃ _smoothDerivation :
        HasSmoothStructureDerivation
          M localCharts locallyFiniteCoverRefinement simplicialComplex
          compatibleChartTriangulations triangulation simplicialApproximation
          starNeighborhoodBasis barycentricSubdivision
          regularNeighborhoodCompatibility triangulationLocalFiniteness
          linkCompatibility plManifoldRecognition triangulationHomeomorphism
          moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
          plStructure plTransitionCompatibility plAtlas plManifoldAtlas
          plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
          plAtlasMaximality plSmoothingExistence
          plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
          plSmoothingCompatibility plSmoothingUniqueness
          plSmoothingLocalModelCompatibility smoothStructure
          smoothAtlasConstruction smoothAtlasPLCompatibility
          smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
          smoothTransitionCompatibility smoothAtlasTransitionSmoothness,
        SmoothStructureDerivationStatement M smoothStructure),
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
        SmoothStructureDerivationStatement M smoothStructure ∧
          ∃ h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))),
          ∃ hSmooth :
            smoothStructure =
              HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
            smoothTransitionCompatibility =
              HasSmoothTransitionCompatibility.ofOnePointRecognition h hSmooth ∧
            smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
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
      ∃ _chartCompatibility :
        HasSmoothChartCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation modelCompatibility,
        (SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M) ∧
        (SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M ∧
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence ∧
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation)) := by
  rcases
      smoothability_derivation_transition_and_recognition_coherence_of_onePointRecognition_subobligationsPayload
        payload h with
    ⟨t2, charted, simple, compact, subobligations,
      derivationAndTransition, recognitionCoherence⟩
  rcases onePointRecognition_surgeryPrerequisites_and_bridgeTailWitnesses
      payload h with
    ⟨surgeryPrerequisites, bridgeTailWitnesses⟩
  exact
    ⟨⟨t2, charted, simple, compact, subobligations,
        derivationAndTransition, recognitionCoherence⟩,
      surgeryPrerequisites, bridgeTailWitnesses⟩

/--
The recognized one-point source exposes a reusable smoothability package bundle:
transition recognition coherence, surgery prerequisites, initial Moise package
fields, the PL-to-smooth frontier, and the bridge-tail witnesses are all
produced from the same smoothability sub-obligation payload.
-/
theorem onePointRecognition_smoothabilityPackageBundle_of_transition_surgery_frontier_and_bridgeTail
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ _subobligations : SmoothabilitySubobligationsPayload M,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
        SmoothStructureDerivationStatement M smoothStructure ∧
          ∃ h' : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))),
          ∃ hSmooth :
            smoothStructure =
              HasThreeManifoldSmoothStructure.ofOnePointRecognition h',
            smoothTransitionCompatibility =
              HasSmoothTransitionCompatibility.ofOnePointRecognition
                h' hSmooth ∧
            smoothAtlasTransitionSmoothness.onePointRecognition = h') ∧
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
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ _plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
          plSmoothingExistence plSmoothingObstructionVanishing,
      ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction ∧
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
        HasSmoothAtlasUniqueness M smoothStructure ∧
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
        ∃ smoothTransitionCompatibility :
          HasSmoothTransitionCompatibility M smoothStructure,
          HasSmoothAtlasTransitionSmoothness
            M smoothStructure smoothTransitionCompatibility) ∧
    (∃ _t2 : T2Space M,
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
      ∃ _chartCompatibility :
        HasSmoothChartCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation modelCompatibility,
        (SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M) ∧
        (SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M ∧
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement manifoldEvidence ∧
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement manifoldEvidence
            bridgeDerivation)) := by
  rcases
      smoothability_derivation_transition_and_recognition_coherence_of_onePointRecognition_subobligationsPayload
        payload h with
    ⟨t2, charted, simple, compact, subobligations,
      _derivationAndTransition, smoothStructure,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      recognitionCoherence⟩
  rcases onePointRecognition_surgeryPrerequisites_and_bridgeTailWitnesses
      payload h with
    ⟨surgeryPrerequisites, bridgeTailWitnesses⟩
  exact
    ⟨⟨t2, charted, simple, compact, subobligations,
        smoothStructure, smoothTransitionCompatibility,
        smoothAtlasTransitionSmoothness, recognitionCoherence⟩,
      surgeryPrerequisites,
      moiseInitialFields_of_onePointRecognition_subobligationsPayload payload h,
      plToSmoothFrontier_of_onePointRecognition_subobligationsPayload payload h,
      bridgeTailWitnesses⟩

/--
The terminal one-point smoothability certificate keeps the PL-to-smooth
frontier and the bridge tail on the same smooth structure, pins transition
smoothness back to the input recognition proof, and exposes the bridge/model/
chart witness equalities used by downstream surgery-facing certificates.
-/
theorem onePointRecognition_terminalSmoothabilityBridgeCertificate
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _subobligations : SmoothabilitySubobligationsPayload M,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility,
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
    ∃ chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility,
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing ∧
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction ∧
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
      HasSmoothAtlasUniqueness M smoothStructure ∧
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
      (∃ hSmooth :
        smoothStructure =
          HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
        smoothTransitionCompatibility =
          HasSmoothTransitionCompatibility.ofOnePointRecognition h hSmooth ∧
        smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
      bridgeDerivation.smoothStructureDerivationWitness =
        smoothDerivationStatement ∧
      bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
      modelCompatibility.smoothStructureDerivationWitness =
        smoothDerivationStatement ∧
      modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
      modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
      chartCompatibility.smoothStructureDerivationWitness =
        smoothDerivationStatement ∧
      chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
      chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
      chartCompatibility.modelCompatibilityWitness = modelCompatibility := by
  rcases payload h with ⟨t2, charted, simple, compact, subobligations⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  rcases subobligations with
    ⟨_localCharts, _locallyFiniteCoverRefinement, _simplicialComplex,
      _compatibleChartTriangulations, triangulation,
      _simplicialApproximation, _starNeighborhoodBasis,
      _barycentricSubdivision, _regularNeighborhoodCompatibility,
      _triangulationLocalFiniteness, _linkCompatibility,
      _plManifoldRecognition, _triangulationHomeomorphism,
      _moiseCompatibility, _triangulationUniqueness,
      _hauptvermutungDimensionThree, plStructure,
      _plTransitionCompatibility, plAtlas, _plManifoldAtlas,
      _plCollarNeighborhoodCompatibility, _plHomeomorphismCompatibility,
      _plAtlasMaximality, _plSmoothingExistence,
      _plSmoothingObstructionVanishing, _plMicrobundleSmoothing,
      plSmoothing, plSmoothingCompatibility, _plSmoothingUniqueness,
      _plSmoothingLocalModelCompatibility, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothAtlasUniqueness,
      smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, _smoothDerivation,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility⟩
  have hRecognition :
      smoothAtlasTransitionSmoothness.onePointRecognition = h :=
    Subsingleton.elim _ _
  let hSmooth :
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition h :=
    Subsingleton.elim _ _
  have hTransition :
      smoothTransitionCompatibility =
        HasSmoothTransitionCompatibility.ofOnePointRecognition h hSmooth :=
    Subsingleton.elim _ _
  exact
    ⟨t2, charted, simple, compact, ⟨_localCharts,
      _locallyFiniteCoverRefinement, _simplicialComplex,
      _compatibleChartTriangulations, triangulation,
      _simplicialApproximation, _starNeighborhoodBasis,
      _barycentricSubdivision, _regularNeighborhoodCompatibility,
      _triangulationLocalFiniteness, _linkCompatibility,
      _plManifoldRecognition, _triangulationHomeomorphism,
      _moiseCompatibility, _triangulationUniqueness,
      _hauptvermutungDimensionThree, plStructure,
      _plTransitionCompatibility, plAtlas, _plManifoldAtlas,
      _plCollarNeighborhoodCompatibility, _plHomeomorphismCompatibility,
      _plAtlasMaximality, _plSmoothingExistence,
      _plSmoothingObstructionVanishing, _plMicrobundleSmoothing,
      plSmoothing, plSmoothingCompatibility, _plSmoothingUniqueness,
      _plSmoothingLocalModelCompatibility, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothAtlasUniqueness,
      smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, _smoothDerivation,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility⟩, triangulation, plStructure,
      plAtlas, plSmoothing, smoothStructure, smoothAtlasConstruction,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility, plSmoothingCompatibility,
      smoothAtlasPLCompatibility, smoothAtlasMaximality,
      smoothAtlasUniqueness, smoothStructureUniqueness,
      ⟨hSmooth, hTransition, hRecognition⟩,
      Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/--
The terminal smoothability bridge route can be read together with the broader
package-frontier route, while retaining researcher-checkable witness coherence:
the same bridge, model, and chart records recover the terminal derivation,
manifold evidence, and compatibility records exposed by the certificate.
-/
theorem onePointRecognition_terminalSmoothabilityBridgeCertificate_with_packageFrontier_and_witness_coherence
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ _subobligations : SmoothabilitySubobligationsPayload M,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
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
      ∃ chartCompatibility :
        HasSmoothChartCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation modelCompatibility,
        SmoothStructureDerivationStatement M smoothStructure ∧
        IsManifold ThreeManifoldModelWithCorners 1 M ∧
        (∃ hSmooth :
          smoothStructure =
            HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
          smoothTransitionCompatibility =
            HasSmoothTransitionCompatibility.ofOnePointRecognition
              h hSmooth ∧
          smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
        HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
          ⟨smoothDerivationStatement, manifoldEvidence⟩ ∧
        HasSmoothChartCompatibility.witnesses M chartCompatibility =
          ⟨smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
            modelCompatibility⟩ ∧
        bridgeDerivation.smoothStructureDerivationWitness =
          smoothDerivationStatement ∧
        bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
        modelCompatibility.smoothStructureDerivationWitness =
          smoothDerivationStatement ∧
        modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
        modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
        chartCompatibility.smoothStructureDerivationWitness =
          smoothDerivationStatement ∧
        chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
        chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
        chartCompatibility.modelCompatibilityWitness = modelCompatibility) ∧
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
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ _plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
          plSmoothingExistence plSmoothingObstructionVanishing,
      ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction ∧
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
        HasSmoothAtlasUniqueness M smoothStructure ∧
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
        ∃ smoothTransitionCompatibility :
          HasSmoothTransitionCompatibility M smoothStructure,
          HasSmoothAtlasTransitionSmoothness
            M smoothStructure smoothTransitionCompatibility) := by
  rcases onePointRecognition_terminalSmoothabilityBridgeCertificate
      payload h with
    ⟨t2, charted, simple, compact, subobligations, _triangulation,
      _plStructure, _plAtlas, _plSmoothing, smoothStructure,
      _smoothAtlasConstruction, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, smoothDerivationStatement,
      manifoldEvidence, bridgeDerivation, modelCompatibility,
      chartCompatibility, _plSmoothingCompatibility,
      _smoothAtlasPLCompatibility, _smoothAtlasMaximality,
      _smoothAtlasUniqueness, _smoothStructureUniqueness,
      recognitionCoherence, bridgeDerivationStatement_eq,
      bridgeManifold_eq, modelDerivationStatement_eq, modelManifold_eq,
      modelBridge_eq, chartDerivationStatement_eq, chartManifold_eq,
      chartBridge_eq, chartModel_eq⟩
  refine
    ⟨?_, moiseInitialFields_of_onePointRecognition_subobligationsPayload
      payload h,
      plToSmoothFrontier_of_onePointRecognition_subobligationsPayload
        payload h⟩
  exact
    ⟨t2, charted, simple, compact, subobligations, smoothStructure,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility, smoothDerivationStatement,
      manifoldEvidence, recognitionCoherence, Subsingleton.elim _ _,
      Subsingleton.elim _ _, bridgeDerivationStatement_eq,
      bridgeManifold_eq, modelDerivationStatement_eq, modelManifold_eq,
      modelBridge_eq, chartDerivationStatement_eq, chartManifold_eq,
      chartBridge_eq, chartModel_eq⟩

/--
Theorem contract for
`onePointRecognition_terminalSmoothabilityBridgeCertificate_with_packageFrontier_and_witness_coherence`.
-/
theorem onePointRecognition_terminalSmoothabilityBridgeCertificate_with_packageFrontier_and_witness_coherence_eq :
    @Poincare.onePointRecognition_terminalSmoothabilityBridgeCertificate_with_packageFrontier_and_witness_coherence =
      @Poincare.onePointRecognition_terminalSmoothabilityBridgeCertificate_with_packageFrontier_and_witness_coherence :=
  rfl

/--
Named terminal smoothability package-frontier and witness-coherence payload for
final-certificate consumers. This is the proposition proved by
`onePointRecognition_terminalSmoothabilityBridgeCertificate_with_packageFrontier_and_witness_coherence`.
-/
abbrev OnePointRecognitionTerminalSmoothabilityPackageFrontierAndWitnessCoherencePayload
    (_payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) : Prop :=
    (∃ _t2 : T2Space M,
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
      ∃ _subobligations : SmoothabilitySubobligationsPayload M,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
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
      ∃ chartCompatibility :
        HasSmoothChartCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation modelCompatibility,
        SmoothStructureDerivationStatement M smoothStructure ∧
        IsManifold ThreeManifoldModelWithCorners 1 M ∧
        (∃ hSmooth :
          smoothStructure =
            HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
          smoothTransitionCompatibility =
            HasSmoothTransitionCompatibility.ofOnePointRecognition
              h hSmooth ∧
          smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
        HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
          ⟨smoothDerivationStatement, manifoldEvidence⟩ ∧
        HasSmoothChartCompatibility.witnesses M chartCompatibility =
          ⟨smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
            modelCompatibility⟩ ∧
        bridgeDerivation.smoothStructureDerivationWitness =
          smoothDerivationStatement ∧
        bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
        modelCompatibility.smoothStructureDerivationWitness =
          smoothDerivationStatement ∧
        modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
        modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
        chartCompatibility.smoothStructureDerivationWitness =
          smoothDerivationStatement ∧
        chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
        chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
        chartCompatibility.modelCompatibilityWitness = modelCompatibility) ∧
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
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ _plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
          plSmoothingExistence plSmoothingObstructionVanishing,
      ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing ∧
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing ∧
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction ∧
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
        HasSmoothAtlasUniqueness M smoothStructure ∧
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
        ∃ smoothTransitionCompatibility :
          HasSmoothTransitionCompatibility M smoothStructure,
          HasSmoothAtlasTransitionSmoothness
            M smoothStructure smoothTransitionCompatibility)

/--
The one-point smoothability payload proves the transported surgery-model
smoothability bridge directly: for every recognized one-point target, it
produces the charted-space witness and the corresponding `C¹` manifold
evidence consumed by the surgery layer.
-/
theorem transportedSmoothabilityBridgeStatement_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    SmoothabilityTransportedBridgeStatement.{u} := by
  intro M _top _t2 _simple _compact h
  rcases onePointRecognition_terminalSmoothabilityBridgeCertificate
      payload h with
    ⟨_payloadT2, charted, _payloadSimple, _payloadCompact,
      _subobligations, _triangulation, _plStructure, _plAtlas,
      _plSmoothing, _smoothStructure, _smoothAtlasConstruction,
      _smoothTransitionCompatibility, _smoothAtlasTransitionSmoothness,
      _smoothDerivationStatement, manifoldEvidence, _bridgeDerivation,
      _modelCompatibility, _chartCompatibility, _plSmoothingCompatibility,
      _smoothAtlasPLCompatibility, _smoothAtlasMaximality,
      _smoothAtlasUniqueness, _smoothStructureUniqueness,
      _recognitionCoherence, _bridgeDerivationStatement_eq,
      _bridgeManifold_eq, _modelDerivationStatement_eq,
      _modelManifold_eq, _modelBridge_eq, _chartDerivationStatement_eq,
      _chartManifold_eq, _chartBridge_eq, _chartModel_eq⟩
  exact ⟨charted, manifoldEvidence⟩

/--
Theorem contract for
`transportedSmoothabilityBridgeStatement_of_onePointRecognition_subobligationsPayload`.
-/
theorem transportedSmoothabilityBridgeStatement_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.transportedSmoothabilityBridgeStatement_of_onePointRecognition_subobligationsPayload =
      @Poincare.transportedSmoothabilityBridgeStatement_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The transported bridge statement is now bundled with the downstream
smoothability frontier certificate: consumers get the global transported
charted-space bridge and, for each recognized source, the terminal bridge
witnesses together with the initial Moise fields and PL-to-smooth frontier.
-/
theorem transportedSmoothabilityBridgeStatement_with_packageFrontier_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    SmoothabilityTransportedBridgeStatement.{u} ∧
      ∀ {M : Type u} [TopologicalSpace M]
        (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))),
        (∃ _t2 : T2Space M,
          ∃ _charted : ChartedSpace ThreeManifoldModel M,
          ∃ _simple : SimplyConnectedSpace M,
          ∃ _compact : CompactSpace M,
          ∃ _subobligations : SmoothabilitySubobligationsPayload M,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothTransitionCompatibility :
            HasSmoothTransitionCompatibility M smoothStructure,
          ∃ smoothAtlasTransitionSmoothness :
            HasSmoothAtlasTransitionSmoothness
              M smoothStructure smoothTransitionCompatibility,
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
          ∃ chartCompatibility :
            HasSmoothChartCompatibility
              M smoothStructure smoothDerivationStatement manifoldEvidence
              bridgeDerivation modelCompatibility,
            SmoothStructureDerivationStatement M smoothStructure ∧
            IsManifold ThreeManifoldModelWithCorners 1 M ∧
            (∃ hSmooth :
              smoothStructure =
                HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
              smoothTransitionCompatibility =
                HasSmoothTransitionCompatibility.ofOnePointRecognition
                  h hSmooth ∧
              smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
            HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
              ⟨smoothDerivationStatement, manifoldEvidence⟩ ∧
            HasSmoothChartCompatibility.witnesses M chartCompatibility =
              ⟨smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
                modelCompatibility⟩ ∧
            bridgeDerivation.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.modelCompatibilityWitness = modelCompatibility) ∧
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
          ∃ triangulation : HasMoiseTriangulation M,
          ∃ plStructure : HasCompatiblePLStructure M triangulation,
          ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
          ∃ plSmoothingExistence :
            HasPLSmoothingExistence M triangulation plStructure plAtlas,
          ∃ plSmoothingObstructionVanishing :
            HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
          ∃ _plMicrobundleSmoothing :
            HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
              plSmoothingExistence plSmoothingObstructionVanishing,
          ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothAtlasConstruction :
            HasSmoothAtlasConstruction
              M triangulation plStructure plAtlas plSmoothing smoothStructure,
            HasPLSmoothingCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingUniqueness
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingLocalModelCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasSmoothAtlasPLCompatibility
              M triangulation plStructure plAtlas plSmoothing smoothStructure
              smoothAtlasConstruction ∧
            HasSmoothAtlasMaximality
              M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
            HasSmoothAtlasUniqueness M smoothStructure ∧
            HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
            ∃ smoothTransitionCompatibility :
              HasSmoothTransitionCompatibility M smoothStructure,
              HasSmoothAtlasTransitionSmoothness
                M smoothStructure smoothTransitionCompatibility) := by
  exact
    ⟨transportedSmoothabilityBridgeStatement_of_onePointRecognition_subobligationsPayload
        payload,
      fun h =>
        onePointRecognition_terminalSmoothabilityBridgeCertificate_with_packageFrontier_and_witness_coherence
          payload h⟩

/--
Theorem contract for
`transportedSmoothabilityBridgeStatement_with_packageFrontier_of_onePointRecognition_subobligationsPayload`.
-/
theorem transportedSmoothabilityBridgeStatement_with_packageFrontier_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.transportedSmoothabilityBridgeStatement_with_packageFrontier_of_onePointRecognition_subobligationsPayload =
      @Poincare.transportedSmoothabilityBridgeStatement_with_packageFrontier_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The same one-point smoothability payload also exposes the transported
smooth-manifold endpoint.  This is stronger than the surgery-model bridge:
downstream consumers receive a transported charted-space witness carrying
`IsManifold (𝓡 3) ∞ M`.
-/
theorem transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    SmoothabilityTransportedSmoothManifoldStatement.{u} := by
  intro M _top _t2 _simple _compact h
  rcases payload h with
    ⟨_payloadT2, _payloadCharted, _payloadSimple, _payloadCompact,
      _subobligations⟩
  rcases h with ⟨e⟩
  let charted : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  exact homeomorphToOnePoint_threeSpace_smoothManifold e

/--
Theorem contract for
`transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload`.
-/
theorem transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload =
      @Poincare.transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The transported smooth-manifold endpoint is bundled with the earlier
transported bridge statement and the full per-target package frontier.  A
single one-point smoothability payload now supplies both downstream smooth
manifold evidence and the terminal bridge/frontier certificate for every
recognized one-point target.
-/
theorem transportedSmoothManifoldStatement_with_bridgePackageFrontier_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    SmoothabilityTransportedSmoothManifoldStatement.{u} ∧
      SmoothabilityTransportedBridgeStatement.{u} ∧
      ∀ {M : Type u} [TopologicalSpace M]
        (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))),
        (∃ _t2 : T2Space M,
          ∃ _charted : ChartedSpace ThreeManifoldModel M,
          ∃ _simple : SimplyConnectedSpace M,
          ∃ _compact : CompactSpace M,
          ∃ _subobligations : SmoothabilitySubobligationsPayload M,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothTransitionCompatibility :
            HasSmoothTransitionCompatibility M smoothStructure,
          ∃ smoothAtlasTransitionSmoothness :
            HasSmoothAtlasTransitionSmoothness
              M smoothStructure smoothTransitionCompatibility,
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
          ∃ chartCompatibility :
            HasSmoothChartCompatibility
              M smoothStructure smoothDerivationStatement manifoldEvidence
              bridgeDerivation modelCompatibility,
            SmoothStructureDerivationStatement M smoothStructure ∧
            IsManifold ThreeManifoldModelWithCorners 1 M ∧
            (∃ hSmooth :
              smoothStructure =
                HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
              smoothTransitionCompatibility =
                HasSmoothTransitionCompatibility.ofOnePointRecognition
                  h hSmooth ∧
              smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
            HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
              ⟨smoothDerivationStatement, manifoldEvidence⟩ ∧
            HasSmoothChartCompatibility.witnesses M chartCompatibility =
              ⟨smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
                modelCompatibility⟩ ∧
            bridgeDerivation.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.modelCompatibilityWitness = modelCompatibility) ∧
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
          ∃ triangulation : HasMoiseTriangulation M,
          ∃ plStructure : HasCompatiblePLStructure M triangulation,
          ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
          ∃ plSmoothingExistence :
            HasPLSmoothingExistence M triangulation plStructure plAtlas,
          ∃ plSmoothingObstructionVanishing :
            HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
          ∃ _plMicrobundleSmoothing :
            HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
              plSmoothingExistence plSmoothingObstructionVanishing,
          ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothAtlasConstruction :
            HasSmoothAtlasConstruction
              M triangulation plStructure plAtlas plSmoothing smoothStructure,
            HasPLSmoothingCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingUniqueness
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingLocalModelCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasSmoothAtlasPLCompatibility
              M triangulation plStructure plAtlas plSmoothing smoothStructure
              smoothAtlasConstruction ∧
            HasSmoothAtlasMaximality
              M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
            HasSmoothAtlasUniqueness M smoothStructure ∧
            HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
            ∃ smoothTransitionCompatibility :
              HasSmoothTransitionCompatibility M smoothStructure,
              HasSmoothAtlasTransitionSmoothness
                M smoothStructure smoothTransitionCompatibility) := by
  rcases
    transportedSmoothabilityBridgeStatement_with_packageFrontier_of_onePointRecognition_subobligationsPayload
      payload with
    ⟨bridgeStatement, packageFrontier⟩
  exact
    ⟨transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload
        payload,
      bridgeStatement, packageFrontier⟩

/--
Theorem contract for
`transportedSmoothManifoldStatement_with_bridgePackageFrontier_of_onePointRecognition_subobligationsPayload`.
-/
theorem transportedSmoothManifoldStatement_with_bridgePackageFrontier_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.transportedSmoothManifoldStatement_with_bridgePackageFrontier_of_onePointRecognition_subobligationsPayload =
      @Poincare.transportedSmoothManifoldStatement_with_bridgePackageFrontier_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The one-point payload now also produces package-field structures for the
transported smooth-manifold theorem and the transported bridge theorem.  The
bridge package is pinned to the canonical bridge obtained by lowering the
transported `C∞` smooth-manifold endpoint, while retaining the full per-target
bridge/frontier certificate.
-/
theorem transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∃ smoothManifoldPackage :
        SmoothabilityTransportedSmoothManifoldPackageField.{u},
    ∃ bridgePackage : SmoothabilityTransportedBridgePackageField.{u},
      smoothManifoldPackage.transportedSmoothManifold =
        transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload
          payload ∧
      bridgePackage.transportedBridge =
        smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
          smoothManifoldPackage.transportedSmoothManifold ∧
      ∀ {M : Type u} [TopologicalSpace M]
        (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))),
        (∃ _t2 : T2Space M,
          ∃ _charted : ChartedSpace ThreeManifoldModel M,
          ∃ _simple : SimplyConnectedSpace M,
          ∃ _compact : CompactSpace M,
          ∃ _subobligations : SmoothabilitySubobligationsPayload M,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothTransitionCompatibility :
            HasSmoothTransitionCompatibility M smoothStructure,
          ∃ smoothAtlasTransitionSmoothness :
            HasSmoothAtlasTransitionSmoothness
              M smoothStructure smoothTransitionCompatibility,
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
          ∃ chartCompatibility :
            HasSmoothChartCompatibility
              M smoothStructure smoothDerivationStatement manifoldEvidence
              bridgeDerivation modelCompatibility,
            SmoothStructureDerivationStatement M smoothStructure ∧
            IsManifold ThreeManifoldModelWithCorners 1 M ∧
            (∃ hSmooth :
              smoothStructure =
                HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
              smoothTransitionCompatibility =
                HasSmoothTransitionCompatibility.ofOnePointRecognition
                  h hSmooth ∧
              smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
            HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
              ⟨smoothDerivationStatement, manifoldEvidence⟩ ∧
            HasSmoothChartCompatibility.witnesses M chartCompatibility =
              ⟨smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
                modelCompatibility⟩ ∧
            bridgeDerivation.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.modelCompatibilityWitness = modelCompatibility) ∧
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
          ∃ triangulation : HasMoiseTriangulation M,
          ∃ plStructure : HasCompatiblePLStructure M triangulation,
          ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
          ∃ plSmoothingExistence :
            HasPLSmoothingExistence M triangulation plStructure plAtlas,
          ∃ plSmoothingObstructionVanishing :
            HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
          ∃ _plMicrobundleSmoothing :
            HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
              plSmoothingExistence plSmoothingObstructionVanishing,
          ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothAtlasConstruction :
            HasSmoothAtlasConstruction
              M triangulation plStructure plAtlas plSmoothing smoothStructure,
            HasPLSmoothingCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingUniqueness
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingLocalModelCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasSmoothAtlasPLCompatibility
              M triangulation plStructure plAtlas plSmoothing smoothStructure
              smoothAtlasConstruction ∧
            HasSmoothAtlasMaximality
              M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
            HasSmoothAtlasUniqueness M smoothStructure ∧
            HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
            ∃ smoothTransitionCompatibility :
              HasSmoothTransitionCompatibility M smoothStructure,
              HasSmoothAtlasTransitionSmoothness
                M smoothStructure smoothTransitionCompatibility) := by
  rcases
    transportedSmoothManifoldStatement_with_bridgePackageFrontier_of_onePointRecognition_subobligationsPayload
      payload with
    ⟨smoothManifoldStatement, _bridgeStatement, packageFrontier⟩
  exact
    ⟨⟨smoothManifoldStatement⟩,
      ⟨smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
        smoothManifoldStatement⟩,
      rfl, rfl, packageFrontier⟩

/--
Theorem contract for
`transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_of_onePointRecognition_subobligationsPayload`.
-/
theorem transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_of_onePointRecognition_subobligationsPayload =
      @Poincare.transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The transported package fields can be read with their explicit theorem-shaped
smooth-manifold and bridge statements, and the same charted-space witness gives
both the transported `C∞` manifold evidence and the lowered surgery-layer
`C¹` manifold evidence for every recognized one-point target.
-/
theorem transportedSmoothManifoldPackageField_with_canonicalBridge_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∃ smoothManifoldStatement :
        SmoothabilityTransportedSmoothManifoldStatement.{u},
    ∃ bridgeStatement : SmoothabilityTransportedBridgeStatement.{u},
    ∃ smoothManifoldPackage :
        SmoothabilityTransportedSmoothManifoldPackageField.{u},
    ∃ bridgePackage : SmoothabilityTransportedBridgePackageField.{u},
      smoothManifoldStatement =
        transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload
          payload ∧
      bridgeStatement =
        smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
          smoothManifoldStatement ∧
      smoothManifoldPackage.transportedSmoothManifold =
        smoothManifoldStatement ∧
      bridgePackage.transportedBridge = bridgeStatement ∧
      bridgePackage.transportedBridge =
        smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
          smoothManifoldPackage.transportedSmoothManifold ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
          ∃ charted : ChartedSpace ThreeManifoldModel M,
            letI : ChartedSpace ThreeManifoldModel M := charted
            IsManifold (𝓡 3) ∞ M ∧
              IsManifold ThreeManifoldModelWithCorners 1 M := by
  let smoothManifoldStatement :
      SmoothabilityTransportedSmoothManifoldStatement.{u} :=
    transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload
      payload
  let bridgeStatement : SmoothabilityTransportedBridgeStatement.{u} :=
    smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
      smoothManifoldStatement
  refine
    ⟨smoothManifoldStatement, bridgeStatement,
      ⟨smoothManifoldStatement⟩, ⟨bridgeStatement⟩,
      rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro M _top _t2 _simple _compact h
  rcases smoothManifoldStatement M h with ⟨charted, smoothManifold⟩
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  exact
    ⟨smoothManifold,
      surgeryModel_isManifold_of_smoothManifold M smoothManifold⟩

/--
Theorem contract for
`transportedSmoothManifoldPackageField_with_canonicalBridge_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload`.
-/
theorem transportedSmoothManifoldPackageField_with_canonicalBridge_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.transportedSmoothManifoldPackageField_with_canonicalBridge_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload =
      @Poincare.transportedSmoothManifoldPackageField_with_canonicalBridge_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
The canonical transported package route retains both payloads at once: the full
per-target bridge/frontier data from the package-frontier theorem and the
same-chart `C∞`/lowered `C¹` manifold witness from the canonical bridge theorem.
-/
theorem transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u}) :
    ∃ smoothManifoldStatement :
        SmoothabilityTransportedSmoothManifoldStatement.{u},
    ∃ bridgeStatement : SmoothabilityTransportedBridgeStatement.{u},
    ∃ smoothManifoldPackage :
        SmoothabilityTransportedSmoothManifoldPackageField.{u},
    ∃ bridgePackage : SmoothabilityTransportedBridgePackageField.{u},
      smoothManifoldStatement =
        transportedSmoothManifoldStatement_of_onePointRecognition_subobligationsPayload
          payload ∧
      bridgeStatement =
        smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
          smoothManifoldStatement ∧
      smoothManifoldPackage.transportedSmoothManifold =
        smoothManifoldStatement ∧
      bridgePackage.transportedBridge = bridgeStatement ∧
      bridgePackage.transportedBridge =
        smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
          smoothManifoldPackage.transportedSmoothManifold ∧
      (∀ {M : Type u} [TopologicalSpace M]
        (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))),
        (∃ _t2 : T2Space M,
          ∃ _charted : ChartedSpace ThreeManifoldModel M,
          ∃ _simple : SimplyConnectedSpace M,
          ∃ _compact : CompactSpace M,
          ∃ _subobligations : SmoothabilitySubobligationsPayload M,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothTransitionCompatibility :
            HasSmoothTransitionCompatibility M smoothStructure,
          ∃ smoothAtlasTransitionSmoothness :
            HasSmoothAtlasTransitionSmoothness
              M smoothStructure smoothTransitionCompatibility,
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
          ∃ chartCompatibility :
            HasSmoothChartCompatibility
              M smoothStructure smoothDerivationStatement manifoldEvidence
              bridgeDerivation modelCompatibility,
            SmoothStructureDerivationStatement M smoothStructure ∧
            IsManifold ThreeManifoldModelWithCorners 1 M ∧
            (∃ hSmooth :
              smoothStructure =
                HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
              smoothTransitionCompatibility =
                HasSmoothTransitionCompatibility.ofOnePointRecognition
                  h hSmooth ∧
              smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
            HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
              ⟨smoothDerivationStatement, manifoldEvidence⟩ ∧
            HasSmoothChartCompatibility.witnesses M chartCompatibility =
              ⟨smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
                modelCompatibility⟩ ∧
            bridgeDerivation.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.modelCompatibilityWitness = modelCompatibility) ∧
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
          ∃ triangulation : HasMoiseTriangulation M,
          ∃ plStructure : HasCompatiblePLStructure M triangulation,
          ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
          ∃ plSmoothingExistence :
            HasPLSmoothingExistence M triangulation plStructure plAtlas,
          ∃ plSmoothingObstructionVanishing :
            HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
          ∃ _plMicrobundleSmoothing :
            HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
              plSmoothingExistence plSmoothingObstructionVanishing,
          ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothAtlasConstruction :
            HasSmoothAtlasConstruction
              M triangulation plStructure plAtlas plSmoothing smoothStructure,
            HasPLSmoothingCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingUniqueness
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingLocalModelCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasSmoothAtlasPLCompatibility
              M triangulation plStructure plAtlas plSmoothing smoothStructure
              smoothAtlasConstruction ∧
            HasSmoothAtlasMaximality
              M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
            HasSmoothAtlasUniqueness M smoothStructure ∧
            HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
            ∃ smoothTransitionCompatibility :
              HasSmoothTransitionCompatibility M smoothStructure,
              HasSmoothAtlasTransitionSmoothness
                M smoothStructure smoothTransitionCompatibility)) ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
          ∃ charted : ChartedSpace ThreeManifoldModel M,
            letI : ChartedSpace ThreeManifoldModel M := charted
            IsManifold (𝓡 3) ∞ M ∧
              IsManifold ThreeManifoldModelWithCorners 1 M := by
  rcases
    transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_of_onePointRecognition_subobligationsPayload
      payload with
    ⟨_frontierSmoothManifoldPackage, _frontierBridgePackage,
      _frontierSmoothManifoldPackage_eq, _frontierBridgePackage_eq,
      bridgePackageFrontier⟩
  rcases
    transportedSmoothManifoldPackageField_with_canonicalBridge_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload
      payload with
    ⟨smoothManifoldStatement, bridgeStatement, smoothManifoldPackage,
      bridgePackage, smoothManifoldStatement_eq, bridgeStatement_eq,
      smoothManifoldPackage_eq, bridgePackage_eq, canonicalBridge_eq,
      sameChartManifoldWitness⟩
  exact
    ⟨smoothManifoldStatement, bridgeStatement, smoothManifoldPackage,
      bridgePackage, smoothManifoldStatement_eq, bridgeStatement_eq,
      smoothManifoldPackage_eq, bridgePackage_eq, canonicalBridge_eq,
      bridgePackageFrontier, sameChartManifoldWitness⟩

/--
Theorem contract for
`transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload`.
-/
theorem transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload_eq :
    @Poincare.transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload =
      @Poincare.transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload :=
  rfl

/--
Per-target projection of the canonical package/frontier route: every recognized
one-point target receives one same charted-space witness carrying both the
transported `C∞` manifold evidence and the lowered surgery-layer `C¹` manifold
evidence, together with the full bridge/frontier certificate for that target.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldWitness_with_canonicalBridgePackageFrontier_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      letI : ChartedSpace ThreeManifoldModel M := charted
      IsManifold (𝓡 3) ∞ M ∧
        IsManifold ThreeManifoldModelWithCorners 1 M ∧
        ((∃ _t2 : T2Space M,
          ∃ _charted : ChartedSpace ThreeManifoldModel M,
          ∃ _simple : SimplyConnectedSpace M,
          ∃ _compact : CompactSpace M,
          ∃ _subobligations : SmoothabilitySubobligationsPayload M,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothTransitionCompatibility :
            HasSmoothTransitionCompatibility M smoothStructure,
          ∃ smoothAtlasTransitionSmoothness :
            HasSmoothAtlasTransitionSmoothness
              M smoothStructure smoothTransitionCompatibility,
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
          ∃ chartCompatibility :
            HasSmoothChartCompatibility
              M smoothStructure smoothDerivationStatement manifoldEvidence
              bridgeDerivation modelCompatibility,
            SmoothStructureDerivationStatement M smoothStructure ∧
            IsManifold ThreeManifoldModelWithCorners 1 M ∧
            (∃ hSmooth :
              smoothStructure =
                HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
              smoothTransitionCompatibility =
                HasSmoothTransitionCompatibility.ofOnePointRecognition
                  h hSmooth ∧
              smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
            HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
              ⟨smoothDerivationStatement, manifoldEvidence⟩ ∧
            HasSmoothChartCompatibility.witnesses M chartCompatibility =
              ⟨smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
                modelCompatibility⟩ ∧
            bridgeDerivation.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            bridgeDerivation.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            modelCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            modelCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.smoothStructureDerivationWitness =
              smoothDerivationStatement ∧
            chartCompatibility.manifoldEvidenceWitness = manifoldEvidence ∧
            chartCompatibility.bridgeDerivationWitness = bridgeDerivation ∧
            chartCompatibility.modelCompatibilityWitness = modelCompatibility) ∧
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
          ∃ triangulation : HasMoiseTriangulation M,
          ∃ plStructure : HasCompatiblePLStructure M triangulation,
          ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
          ∃ plSmoothingExistence :
            HasPLSmoothingExistence M triangulation plStructure plAtlas,
          ∃ plSmoothingObstructionVanishing :
            HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
          ∃ _plMicrobundleSmoothing :
            HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
              plSmoothingExistence plSmoothingObstructionVanishing,
          ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
          ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
          ∃ smoothAtlasConstruction :
            HasSmoothAtlasConstruction
              M triangulation plStructure plAtlas plSmoothing smoothStructure,
            HasPLSmoothingCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingUniqueness
              M triangulation plStructure plAtlas plSmoothing ∧
            HasPLSmoothingLocalModelCompatibility
              M triangulation plStructure plAtlas plSmoothing ∧
            HasSmoothAtlasPLCompatibility
              M triangulation plStructure plAtlas plSmoothing smoothStructure
              smoothAtlasConstruction ∧
            HasSmoothAtlasMaximality
              M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
            HasSmoothAtlasUniqueness M smoothStructure ∧
            HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
            ∃ smoothTransitionCompatibility :
              HasSmoothTransitionCompatibility M smoothStructure,
              HasSmoothAtlasTransitionSmoothness
                M smoothStructure smoothTransitionCompatibility)) := by
  rcases
    transportedSmoothManifoldPackageField_with_canonicalBridgePackageFrontier_and_sameChartManifoldWitness_of_onePointRecognition_subobligationsPayload
      payload with
    ⟨_smoothManifoldStatement, _bridgeStatement, _smoothManifoldPackage,
      _bridgePackage, _smoothManifoldStatement_eq, _bridgeStatement_eq,
      _smoothManifoldPackage_eq, _bridgePackage_eq, _canonicalBridge_eq,
      bridgePackageFrontier, sameChartManifoldWitness⟩
  rcases sameChartManifoldWitness M h with
    ⟨charted, smoothManifold, loweredManifold⟩
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  exact ⟨smoothManifold, loweredManifold, bridgePackageFrontier h⟩

/--
Theorem contract for
`onePointRecognition_sameChartTransportedSmoothManifoldWitness_with_canonicalBridgePackageFrontier_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldWitness_with_canonicalBridgePackageFrontier_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldWitness_with_canonicalBridgePackageFrontier_of_subobligationsPayload =
      @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldWitness_with_canonicalBridgePackageFrontier_of_subobligationsPayload :=
  rfl

/--
Named per-target bundle for the same-chart transported smooth-manifold endpoint
and the bridge/frontier witnesses extracted from the canonical certificate.
-/
structure OnePointRecognitionSameChartCanonicalBridgePackageFrontierBundle
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M] where
  sameCharted : ChartedSpace ThreeManifoldModel M
  transportedSmoothManifold :
    letI : ChartedSpace ThreeManifoldModel M := sameCharted
    IsManifold (𝓡 3) ∞ M
  loweredManifold :
    letI : ChartedSpace ThreeManifoldModel M := sameCharted
    IsManifold ThreeManifoldModelWithCorners 1 M
  bridgeT2 : T2Space M
  bridgeCharted : ChartedSpace ThreeManifoldModel M
  bridgeSimple : SimplyConnectedSpace M
  bridgeCompact : CompactSpace M
  subobligations :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    SmoothabilitySubobligationsPayload M
  smoothStructure :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    HasThreeManifoldSmoothStructure M
  smoothDerivationStatement :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    SmoothStructureDerivationStatement M smoothStructure
  bridgeManifoldEvidence :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    IsManifold ThreeManifoldModelWithCorners 1 M
  bridgeDerivation :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    HasSmoothabilityBridgeDerivation
      M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
  modelCompatibility :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    HasSmoothManifoldModelCompatibility
      M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
      bridgeDerivation
  chartCompatibility :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    HasSmoothChartCompatibility
      M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
      bridgeDerivation modelCompatibility
  bridgeDerivation_witnesses_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
      ⟨smoothDerivationStatement, bridgeManifoldEvidence⟩
  chartCompatibility_witnesses_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    HasSmoothChartCompatibility.witnesses M chartCompatibility =
      ⟨smoothDerivationStatement, bridgeManifoldEvidence, bridgeDerivation,
        modelCompatibility⟩
  bridgeDerivationStatement_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    bridgeDerivation.smoothStructureDerivationWitness =
      smoothDerivationStatement
  bridgeManifold_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    bridgeDerivation.manifoldEvidenceWitness = bridgeManifoldEvidence
  modelDerivationStatement_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    modelCompatibility.smoothStructureDerivationWitness =
      smoothDerivationStatement
  modelManifold_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    modelCompatibility.manifoldEvidenceWitness = bridgeManifoldEvidence
  modelBridge_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    modelCompatibility.bridgeDerivationWitness = bridgeDerivation
  chartDerivationStatement_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    chartCompatibility.smoothStructureDerivationWitness =
      smoothDerivationStatement
  chartManifold_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    chartCompatibility.manifoldEvidenceWitness = bridgeManifoldEvidence
  chartBridge_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    chartCompatibility.bridgeDerivationWitness = bridgeDerivation
  chartModel_eq :
    letI : T2Space M := bridgeT2
    letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
    letI : SimplyConnectedSpace M := bridgeSimple
    letI : CompactSpace M := bridgeCompact
    chartCompatibility.modelCompatibilityWitness = modelCompatibility

/--
Reusable named-bundle projection of
`onePointRecognition_sameChartTransportedSmoothManifoldWitness_with_canonicalBridgePackageFrontier_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    Nonempty
      (OnePointRecognitionSameChartCanonicalBridgePackageFrontierBundle M) := by
  rcases
    onePointRecognition_sameChartTransportedSmoothManifoldWitness_with_canonicalBridgePackageFrontier_of_subobligationsPayload
      payload M h with
    ⟨sameCharted, transportedSmoothManifold, loweredManifold,
      bridgePackageFrontier⟩
  rcases bridgePackageFrontier with
    ⟨bridgeCertificate, _moiseInitialFields, _plToSmoothFrontier⟩
  rcases bridgeCertificate with
    ⟨bridgeT2, bridgeCharted, bridgeSimple, bridgeCompact, subobligations,
      smoothStructure, _smoothTransitionCompatibility,
      _smoothAtlasTransitionSmoothness, smoothDerivationStatement,
      bridgeManifoldEvidence, bridgeDerivation, modelCompatibility,
      chartCompatibility, _smoothDerivationStatementWitness,
      _bridgeManifoldEvidenceWitness, _recognitionCoherence,
      bridgeDerivation_witnesses_eq, chartCompatibility_witnesses_eq,
      bridgeDerivationStatement_eq, bridgeManifold_eq,
      modelDerivationStatement_eq, modelManifold_eq, modelBridge_eq,
      chartDerivationStatement_eq, chartManifold_eq, chartBridge_eq,
      chartModel_eq⟩
  exact
    ⟨({ sameCharted := sameCharted
        transportedSmoothManifold := transportedSmoothManifold
        loweredManifold := loweredManifold
        bridgeT2 := bridgeT2
        bridgeCharted := bridgeCharted
        bridgeSimple := bridgeSimple
        bridgeCompact := bridgeCompact
        subobligations := subobligations
        smoothStructure := smoothStructure
        smoothDerivationStatement := smoothDerivationStatement
        bridgeManifoldEvidence := bridgeManifoldEvidence
        bridgeDerivation := bridgeDerivation
        modelCompatibility := modelCompatibility
        chartCompatibility := chartCompatibility
        bridgeDerivation_witnesses_eq := bridgeDerivation_witnesses_eq
        chartCompatibility_witnesses_eq := chartCompatibility_witnesses_eq
        bridgeDerivationStatement_eq := bridgeDerivationStatement_eq
        bridgeManifold_eq := bridgeManifold_eq
        modelDerivationStatement_eq := modelDerivationStatement_eq
        modelManifold_eq := modelManifold_eq
        modelBridge_eq := modelBridge_eq
        chartDerivationStatement_eq := chartDerivationStatement_eq
        chartManifold_eq := chartManifold_eq
        chartBridge_eq := chartBridge_eq
        chartModel_eq := chartModel_eq } :
      OnePointRecognitionSameChartCanonicalBridgePackageFrontierBundle M)⟩

/--
Theorem contract for
`onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload =
      @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload :=
  rfl

/--
Concrete field projection of the same-chart canonical bridge/frontier bundle:
from a one-point recognition smoothability payload and target homeomorphism,
choose the chart carrying both transported smooth-manifold witnesses and the
bridge-side derivation/model/chart compatibility evidence.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_evidence_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold (𝓡 3) ∞ M ∧
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      ∃ bridgeT2 : T2Space M,
      ∃ bridgeCharted : ChartedSpace ThreeManifoldModel M,
      ∃ bridgeSimple : SimplyConnectedSpace M,
      ∃ bridgeCompact : CompactSpace M,
        letI : T2Space M := bridgeT2
        letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
        letI : SimplyConnectedSpace M := bridgeSimple
        letI : CompactSpace M := bridgeCompact
        ∃ _subobligations : SmoothabilitySubobligationsPayload M,
        ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ bridgeManifoldEvidence :
          IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation,
        ∃ chartCompatibility :
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation modelCompatibility,
          HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence⟩ ∧
          HasSmoothChartCompatibility.witnesses M chartCompatibility =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence,
              bridgeDerivation, modelCompatibility⟩ := by
  rcases
    onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload
      payload M h with
    ⟨bundle⟩
  refine
    ⟨bundle.sameCharted, ?_, bundle.bridgeT2, bundle.bridgeCharted,
      bundle.bridgeSimple, bundle.bridgeCompact, ?_⟩
  · letI : ChartedSpace ThreeManifoldModel M := bundle.sameCharted
    exact ⟨bundle.transportedSmoothManifold, bundle.loweredManifold⟩
  · exact
      ⟨bundle.subobligations, bundle.smoothStructure,
        bundle.smoothDerivationStatement, bundle.bridgeManifoldEvidence,
        bundle.bridgeDerivation, bundle.modelCompatibility,
        bundle.chartCompatibility, bundle.bridgeDerivation_witnesses_eq,
        bundle.chartCompatibility_witnesses_eq⟩

/--
Theorem contract for
`onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_evidence_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_evidence_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_evidence_of_subobligationsPayload =
      @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_evidence_of_subobligationsPayload :=
  rfl

/--
Coherence projection for the same canonical bridge/frontier bundle: the selected
bridge, model, and chart witnesses expose the definitional payload equalities
needed by downstream consumers without unpacking the entire bundle structure.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_coherence_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ bundle : OnePointRecognitionSameChartCanonicalBridgePackageFrontierBundle M,
      (letI : ChartedSpace ThreeManifoldModel M := bundle.sameCharted
       IsManifold (𝓡 3) ∞ M ∧
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      (letI : T2Space M := bundle.bridgeT2
       letI : ChartedSpace ThreeManifoldModel M := bundle.bridgeCharted
       letI : SimplyConnectedSpace M := bundle.bridgeSimple
       letI : CompactSpace M := bundle.bridgeCompact
       bundle.bridgeDerivation.smoothStructureDerivationWitness =
         bundle.smoothDerivationStatement ∧
       bundle.bridgeDerivation.manifoldEvidenceWitness =
         bundle.bridgeManifoldEvidence ∧
       bundle.modelCompatibility.smoothStructureDerivationWitness =
         bundle.smoothDerivationStatement ∧
       bundle.modelCompatibility.manifoldEvidenceWitness =
         bundle.bridgeManifoldEvidence ∧
       bundle.modelCompatibility.bridgeDerivationWitness =
         bundle.bridgeDerivation ∧
       bundle.chartCompatibility.smoothStructureDerivationWitness =
         bundle.smoothDerivationStatement ∧
       bundle.chartCompatibility.manifoldEvidenceWitness =
         bundle.bridgeManifoldEvidence ∧
       bundle.chartCompatibility.bridgeDerivationWitness =
         bundle.bridgeDerivation ∧
       bundle.chartCompatibility.modelCompatibilityWitness =
         bundle.modelCompatibility) := by
  rcases
    onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload
      payload M h with
    ⟨bundle⟩
  refine ⟨bundle, ?_, ?_⟩
  · letI : ChartedSpace ThreeManifoldModel M := bundle.sameCharted
    exact ⟨bundle.transportedSmoothManifold, bundle.loweredManifold⟩
  · exact
      ⟨bundle.bridgeDerivationStatement_eq, bundle.bridgeManifold_eq,
        bundle.modelDerivationStatement_eq, bundle.modelManifold_eq,
        bundle.modelBridge_eq, bundle.chartDerivationStatement_eq,
        bundle.chartManifold_eq, bundle.chartBridge_eq, bundle.chartModel_eq⟩

/--
Theorem contract for
`onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_coherence_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_coherence_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_coherence_of_subobligationsPayload =
      @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_projection_with_bridge_model_chart_coherence_of_subobligationsPayload :=
  rfl

/--
Compact downstream-consumer projection for the one-point smoothability payload:
choose the chart carrying the transported smoothability conclusion, expose the
bridge/model/chart derivation evidence, and keep the key witness/coherence
equations in the same endpoint.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold (𝓡 3) ∞ M ∧
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      ∃ bridgeT2 : T2Space M,
      ∃ bridgeCharted : ChartedSpace ThreeManifoldModel M,
      ∃ bridgeSimple : SimplyConnectedSpace M,
      ∃ bridgeCompact : CompactSpace M,
        letI : T2Space M := bridgeT2
        letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
        letI : SimplyConnectedSpace M := bridgeSimple
        letI : CompactSpace M := bridgeCompact
        ∃ _subobligations : SmoothabilitySubobligationsPayload M,
        ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ bridgeManifoldEvidence :
          IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation,
        ∃ chartCompatibility :
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation modelCompatibility,
          HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence⟩ ∧
          HasSmoothChartCompatibility.witnesses M chartCompatibility =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence,
              bridgeDerivation, modelCompatibility⟩ ∧
          bridgeDerivation.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          bridgeDerivation.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          modelCompatibility.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          modelCompatibility.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          modelCompatibility.bridgeDerivationWitness =
            bridgeDerivation ∧
          chartCompatibility.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          chartCompatibility.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          chartCompatibility.bridgeDerivationWitness =
            bridgeDerivation ∧
          chartCompatibility.modelCompatibilityWitness =
            modelCompatibility := by
  rcases
    onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload
      payload M h with
    ⟨bundle⟩
  refine
    ⟨bundle.sameCharted, ?_, bundle.bridgeT2, bundle.bridgeCharted,
      bundle.bridgeSimple, bundle.bridgeCompact, ?_⟩
  · letI : ChartedSpace ThreeManifoldModel M := bundle.sameCharted
    exact ⟨bundle.transportedSmoothManifold, bundle.loweredManifold⟩
  · exact
      ⟨bundle.subobligations, bundle.smoothStructure,
        bundle.smoothDerivationStatement, bundle.bridgeManifoldEvidence,
        bundle.bridgeDerivation, bundle.modelCompatibility,
        bundle.chartCompatibility, bundle.bridgeDerivation_witnesses_eq,
        bundle.chartCompatibility_witnesses_eq,
        bundle.bridgeDerivationStatement_eq, bundle.bridgeManifold_eq,
        bundle.modelDerivationStatement_eq, bundle.modelManifold_eq,
        bundle.modelBridge_eq, bundle.chartDerivationStatement_eq,
        bundle.chartManifold_eq, bundle.chartBridge_eq, bundle.chartModel_eq⟩

/--
Theorem contract for
`onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_of_subobligationsPayload =
      @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_of_subobligationsPayload :=
  rfl

/--
Final-certificate-facing projection of the one-point smoothability payload:
choose the transported same-chart smooth-manifold endpoint and, in the same
consumer bundle, expose the terminal bridge/model/chart witnesses together with
the recognition coherence pinning the smooth structure to the supplied one-point
homeomorphism.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_with_recognition_coherence_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold (𝓡 3) ∞ M ∧
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      ∃ bridgeT2 : T2Space M,
      ∃ bridgeCharted : ChartedSpace ThreeManifoldModel M,
      ∃ bridgeSimple : SimplyConnectedSpace M,
      ∃ bridgeCompact : CompactSpace M,
        letI : T2Space M := bridgeT2
        letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
        letI : SimplyConnectedSpace M := bridgeSimple
        letI : CompactSpace M := bridgeCompact
        ∃ _subobligations : SmoothabilitySubobligationsPayload M,
        ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothTransitionCompatibility :
          HasSmoothTransitionCompatibility M smoothStructure,
        ∃ smoothAtlasTransitionSmoothness :
          HasSmoothAtlasTransitionSmoothness
            M smoothStructure smoothTransitionCompatibility,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ bridgeManifoldEvidence :
          IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation,
        ∃ chartCompatibility :
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation modelCompatibility,
          SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M ∧
          (∃ hSmooth :
            smoothStructure =
              HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
            smoothTransitionCompatibility =
              HasSmoothTransitionCompatibility.ofOnePointRecognition
                h hSmooth ∧
            smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
          HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence⟩ ∧
          HasSmoothChartCompatibility.witnesses M chartCompatibility =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence,
              bridgeDerivation, modelCompatibility⟩ ∧
          bridgeDerivation.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          bridgeDerivation.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          modelCompatibility.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          modelCompatibility.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          modelCompatibility.bridgeDerivationWitness =
            bridgeDerivation ∧
          chartCompatibility.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          chartCompatibility.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          chartCompatibility.bridgeDerivationWitness =
            bridgeDerivation ∧
          chartCompatibility.modelCompatibilityWitness =
            modelCompatibility := by
  rcases
    onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload
      payload M h with
    ⟨bundle⟩
  rcases onePointRecognition_terminalSmoothabilityBridgeCertificate
      payload h with
    ⟨bridgeT2, bridgeCharted, bridgeSimple, bridgeCompact, subobligations,
      _triangulation, _plStructure, _plAtlas, _plSmoothing,
      smoothStructure, _smoothAtlasConstruction,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivationStatement, bridgeManifoldEvidence, bridgeDerivation,
      modelCompatibility, chartCompatibility, _plSmoothingCompatibility,
      _smoothAtlasPLCompatibility, _smoothAtlasMaximality,
      _smoothAtlasUniqueness, _smoothStructureUniqueness,
      recognitionCoherence, bridgeDerivationStatement_eq,
      bridgeManifold_eq, modelDerivationStatement_eq, modelManifold_eq,
      modelBridge_eq, chartDerivationStatement_eq, chartManifold_eq,
      chartBridge_eq, chartModel_eq⟩
  refine
    ⟨bundle.sameCharted, ?_, bridgeT2, bridgeCharted, bridgeSimple,
      bridgeCompact, ?_⟩
  · letI : ChartedSpace ThreeManifoldModel M := bundle.sameCharted
    exact ⟨bundle.transportedSmoothManifold, bundle.loweredManifold⟩
  · exact
      ⟨subobligations, smoothStructure, smoothTransitionCompatibility,
        smoothAtlasTransitionSmoothness, smoothDerivationStatement,
        bridgeManifoldEvidence, bridgeDerivation, modelCompatibility,
        chartCompatibility, smoothDerivationStatement, bridgeManifoldEvidence,
        recognitionCoherence, Subsingleton.elim _ _, Subsingleton.elim _ _,
        bridgeDerivationStatement_eq, bridgeManifold_eq,
        modelDerivationStatement_eq, modelManifold_eq, modelBridge_eq,
        chartDerivationStatement_eq, chartManifold_eq, chartBridge_eq,
        chartModel_eq⟩

/--
Theorem contract for
`onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_with_recognition_coherence_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_with_recognition_coherence_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_with_recognition_coherence_of_subobligationsPayload =
      @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_coreSmoothabilityConsumerProjection_with_recognition_coherence_of_subobligationsPayload :=
  rfl

/--
Named proposition for the terminal-frontier projection used by
final-certificate consumers.
-/
abbrev OnePointRecognitionTerminalSmoothabilityBridgeCertificateProjection
    (_payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    Prop :=
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold (𝓡 3) ∞ M ∧
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      ∃ bridgeT2 : T2Space M,
      ∃ bridgeCharted : ChartedSpace ThreeManifoldModel M,
      ∃ bridgeSimple : SimplyConnectedSpace M,
      ∃ bridgeCompact : CompactSpace M,
        letI : T2Space M := bridgeT2
        letI : ChartedSpace ThreeManifoldModel M := bridgeCharted
        letI : SimplyConnectedSpace M := bridgeSimple
        letI : CompactSpace M := bridgeCompact
        ∃ _subobligations : SmoothabilitySubobligationsPayload M,
        ∃ triangulation : HasMoiseTriangulation M,
        ∃ plStructure : HasCompatiblePLStructure M triangulation,
        ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
        ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
        ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
        ∃ smoothAtlasConstruction :
          HasSmoothAtlasConstruction
            M triangulation plStructure plAtlas plSmoothing smoothStructure,
        ∃ smoothTransitionCompatibility :
          HasSmoothTransitionCompatibility M smoothStructure,
        ∃ smoothAtlasTransitionSmoothness :
          HasSmoothAtlasTransitionSmoothness
            M smoothStructure smoothTransitionCompatibility,
        ∃ smoothDerivationStatement :
          SmoothStructureDerivationStatement M smoothStructure,
        ∃ bridgeManifoldEvidence :
          IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ bridgeDerivation :
          HasSmoothabilityBridgeDerivation
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence,
        ∃ modelCompatibility :
          HasSmoothManifoldModelCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation,
        ∃ chartCompatibility :
          HasSmoothChartCompatibility
            M smoothStructure smoothDerivationStatement bridgeManifoldEvidence
            bridgeDerivation modelCompatibility,
          HasPLSmoothingCompatibility
            M triangulation plStructure plAtlas plSmoothing ∧
          HasSmoothAtlasPLCompatibility
            M triangulation plStructure plAtlas plSmoothing smoothStructure
            smoothAtlasConstruction ∧
          HasSmoothAtlasMaximality
            M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
          HasSmoothAtlasUniqueness M smoothStructure ∧
          HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
          SmoothStructureDerivationStatement M smoothStructure ∧
          IsManifold ThreeManifoldModelWithCorners 1 M ∧
          (∃ hSmooth :
            smoothStructure =
              HasThreeManifoldSmoothStructure.ofOnePointRecognition h,
            smoothTransitionCompatibility =
              HasSmoothTransitionCompatibility.ofOnePointRecognition
                h hSmooth ∧
            smoothAtlasTransitionSmoothness.onePointRecognition = h) ∧
          HasSmoothabilityBridgeDerivation.witnesses M bridgeDerivation =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence⟩ ∧
          HasSmoothChartCompatibility.witnesses M chartCompatibility =
            ⟨smoothDerivationStatement, bridgeManifoldEvidence,
              bridgeDerivation, modelCompatibility⟩ ∧
          bridgeDerivation.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          bridgeDerivation.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          modelCompatibility.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          modelCompatibility.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          modelCompatibility.bridgeDerivationWitness =
            bridgeDerivation ∧
          chartCompatibility.smoothStructureDerivationWitness =
            smoothDerivationStatement ∧
          chartCompatibility.manifoldEvidenceWitness =
            bridgeManifoldEvidence ∧
          chartCompatibility.bridgeDerivationWitness =
            bridgeDerivation ∧
          chartCompatibility.modelCompatibilityWitness =
            modelCompatibility

/--
Terminal-frontier projection for final-certificate consumers: the same-chart
transported/lowered manifold endpoint is kept together with the full
PL-to-smooth terminal certificate, transition smoothness, recognition coherence,
and the bridge/model/chart witness equalities.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_terminalSmoothabilityBridgeCertificateProjection_with_frontier_coherence_of_subobligationsPayload
    (payload : OnePointRecognitionSmoothabilitySubobligationsPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    OnePointRecognitionTerminalSmoothabilityBridgeCertificateProjection
      payload M h := by
  rcases
    onePointRecognition_sameChartTransportedSmoothManifoldBundle_with_canonicalBridgePackageFrontier_of_subobligationsPayload
      payload M h with
    ⟨bundle⟩
  rcases onePointRecognition_terminalSmoothabilityBridgeCertificate
      payload h with
    ⟨bridgeT2, bridgeCharted, bridgeSimple, bridgeCompact, subobligations,
      triangulation, plStructure, plAtlas, plSmoothing, smoothStructure,
      smoothAtlasConstruction, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, smoothDerivationStatement,
      bridgeManifoldEvidence, bridgeDerivation, modelCompatibility,
      chartCompatibility, plSmoothingCompatibility,
      smoothAtlasPLCompatibility, smoothAtlasMaximality,
      smoothAtlasUniqueness, smoothStructureUniqueness,
      recognitionCoherence, bridgeDerivationStatement_eq,
      bridgeManifold_eq, modelDerivationStatement_eq, modelManifold_eq,
      modelBridge_eq, chartDerivationStatement_eq, chartManifold_eq,
      chartBridge_eq, chartModel_eq⟩
  refine
    ⟨bundle.sameCharted, ?_, bridgeT2, bridgeCharted, bridgeSimple,
      bridgeCompact, ?_⟩
  · letI : ChartedSpace ThreeManifoldModel M := bundle.sameCharted
    exact ⟨bundle.transportedSmoothManifold, bundle.loweredManifold⟩
  · exact
      ⟨subobligations, triangulation, plStructure, plAtlas, plSmoothing,
        smoothStructure, smoothAtlasConstruction, smoothTransitionCompatibility,
        smoothAtlasTransitionSmoothness, smoothDerivationStatement,
        bridgeManifoldEvidence, bridgeDerivation, modelCompatibility,
        chartCompatibility, plSmoothingCompatibility,
        smoothAtlasPLCompatibility, smoothAtlasMaximality,
        smoothAtlasUniqueness, smoothStructureUniqueness,
        smoothDerivationStatement, bridgeManifoldEvidence,
        recognitionCoherence, Subsingleton.elim _ _, Subsingleton.elim _ _,
        bridgeDerivationStatement_eq, bridgeManifold_eq,
        modelDerivationStatement_eq, modelManifold_eq, modelBridge_eq,
        chartDerivationStatement_eq, chartManifold_eq, chartBridge_eq,
        chartModel_eq⟩

/--
Theorem contract for
`onePointRecognition_sameChartTransportedSmoothManifoldBundle_terminalSmoothabilityBridgeCertificateProjection_with_frontier_coherence_of_subobligationsPayload`.
-/
theorem onePointRecognition_sameChartTransportedSmoothManifoldBundle_terminalSmoothabilityBridgeCertificateProjection_with_frontier_coherence_of_subobligationsPayload_eq :
    @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_terminalSmoothabilityBridgeCertificateProjection_with_frontier_coherence_of_subobligationsPayload =
      @Poincare.onePointRecognition_sameChartTransportedSmoothManifoldBundle_terminalSmoothabilityBridgeCertificateProjection_with_frontier_coherence_of_subobligationsPayload :=
  rfl

/-- Theorem contract for `onePointRecognition_terminalSmoothabilityBridgeCertificate`. -/
theorem onePointRecognition_terminalSmoothabilityBridgeCertificate_eq :
    @Poincare.onePointRecognition_terminalSmoothabilityBridgeCertificate =
      @Poincare.onePointRecognition_terminalSmoothabilityBridgeCertificate :=
  rfl

end Poincare
