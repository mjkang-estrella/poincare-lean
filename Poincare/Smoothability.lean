/-
Typed interface for the smoothability bridge.

The target Poincare statement is topological. The Ricci-flow-with-surgery spine
uses a smooth 3-manifold model. This module makes the bridge between those
surfaces explicit.
-/

import Poincare.Surgery

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Interface for the Moise-style triangulation input for topological
3-manifolds.
-/
inductive HasMoiseLocalTriangulationCharts
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop

/-- Interface for refining local topological charts to a locally finite cover. -/
inductive HasMoiseLocallyFiniteCoverRefinement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_localCharts : HasMoiseLocalTriangulationCharts M) : Prop

/-- Interface for the simplicial-complex data used in Moise triangulation. -/
inductive HasMoiseSimplicialComplex
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_localCharts : HasMoiseLocalTriangulationCharts M) : Prop

/-- Interface for making the local chart triangulations mutually compatible. -/
inductive HasMoiseCompatibleChartTriangulations
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (_simplicialComplex : HasMoiseSimplicialComplex M localCharts) : Prop

inductive HasMoiseTriangulation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop

/-- Interface for the simplicial-approximation step producing the global triangulation. -/
inductive HasMoiseSimplicialApproximation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for the star-neighborhood basis carried by a Moise triangulation. -/
inductive HasMoiseStarNeighborhoodBasis
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for barycentric subdivision control in the Moise triangulation. -/
inductive HasMoiseBarycentricSubdivisionControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for regular-neighborhood compatibility after subdivision. -/
inductive HasMoiseRegularNeighborhoodCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for local finiteness of the Moise triangulation. -/
inductive HasMoiseTriangulationLocalFiniteness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for the 3-manifold link condition in the Moise triangulation. -/
inductive HasMoiseLinkCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface recognizing the triangulation as a PL 3-manifold by its links. -/
inductive HasMoisePLManifoldRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (_linkCompatibility : HasMoiseLinkCompatibility M triangulation) : Prop

/-- Interface for the homeomorphism between the topological space and its triangulation. -/
inductive HasMoiseTriangulationHomeomorphism
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (_triangulation : HasMoiseTriangulation M) : Prop

/--
Interface for patching local Moise triangulations into the global
triangulation used by the bridge.
-/
inductive HasMoiseTriangulationCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_localCharts : HasMoiseLocalTriangulationCharts M)
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for uniqueness of the Moise PL structure induced by triangulation. -/
inductive HasMoiseTriangulationUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for the dimension-three Hauptvermutung input used by Moise uniqueness. -/
inductive HasMoiseHauptvermutungDimensionThree
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (_triangulationUniqueness : HasMoiseTriangulationUniqueness M triangulation) : Prop

/--
Interface for the PL structure compatible with the Moise triangulation.
-/
inductive HasCompatiblePLStructure
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop

/-- Interface for PL transition-map compatibility with the triangulation. -/
inductive HasPLTransitionCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (_plStructure : HasCompatiblePLStructure M triangulation) : Prop

/--
Interface for compatibility between the PL charts and the original topological
charted-space structure.
-/
inductive HasCompatiblePLAtlas
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (_plStructure : HasCompatiblePLStructure M triangulation) : Prop

/-- Interface for the PL-manifold atlas extracted from the triangulation. -/
inductive HasPLManifoldAtlas
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (_plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop

/-- Interface for PL collar-neighborhood compatibility in the produced atlas. -/
inductive HasPLCollarNeighborhoodCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (_plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop

/--
Interface for compatibility between the Moise homeomorphism and the produced PL
atlas.
-/
inductive HasPLHomeomorphismCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (_plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop

/-- Interface for maximality/completeness of the compatible PL atlas. -/
inductive HasPLAtlasMaximality
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (_plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop

/-- Interface for existence of a smoothing of the compatible PL atlas. -/
inductive HasPLSmoothingExistence
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (_plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop

/-- Interface for vanishing of the PL-smoothing obstruction in dimension three. -/
inductive HasPLSmoothingObstructionVanishing
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (_plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop

/-- Interface for reducing PL smoothing to the microbundle smoothing theorem. -/
inductive HasPLMicrobundleSmoothing
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (_plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas) : Prop

/-- Interface for the 3-dimensional PL-to-smooth smoothing theorem. -/
inductive HasPLSmoothingTheorem
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (_plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop

/-- Interface for compatibility/uniqueness of the PL smoothing theorem output. -/
inductive HasPLSmoothingCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (_smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas) : Prop

/-- Interface for uniqueness of the PL smoothing selected by the theorem. -/
inductive HasPLSmoothingUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (_smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas) : Prop

/-- Interface for compatibility of local smooth models supplied by PL smoothing. -/
inductive HasPLSmoothingLocalModelCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (_smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas) : Prop

/--
Interface asserting that a topological 3-manifold carries the smooth structure
needed by the surgery layer.

This predicate has no constructors here. The bridge must come from a real
smoothability/compatibility theorem for 3-manifolds.
-/
inductive HasThreeManifoldSmoothStructure
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop

/-- Interface for constructing a smooth atlas from the PL smoothing theorem. -/
inductive HasSmoothAtlasConstruction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (_smoothStructure : HasThreeManifoldSmoothStructure M) : Prop

/-- Interface for compatibility between the smooth atlas and the PL atlas. -/
inductive HasSmoothAtlasPLCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (_smoothStructure : HasThreeManifoldSmoothStructure M) : Prop

/-- Interface for maximality of the produced smooth atlas. -/
inductive HasSmoothAtlasMaximality
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (_smoothStructure : HasThreeManifoldSmoothStructure M) : Prop

/-- Interface for uniqueness/compatibility of the produced smooth atlas. -/
inductive HasSmoothAtlasUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_smoothStructure : HasThreeManifoldSmoothStructure M) : Prop

/-- Interface for uniqueness of the smooth structure up to diffeomorphism. -/
inductive HasSmoothStructureUniquenessUpToDiffeomorphism
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_smoothStructure : HasThreeManifoldSmoothStructure M) : Prop

/-- Interface for smooth transition-map compatibility in the produced atlas. -/
inductive HasSmoothTransitionCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_smoothStructure : HasThreeManifoldSmoothStructure M) : Prop

/-- Interface for smoothness of all transition maps in the produced atlas. -/
inductive HasSmoothAtlasTransitionSmoothness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (_smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure) : Prop

/--
Interface certifying that the smooth structure was produced from the preceding
topological and PL inputs.
-/
inductive HasSmoothStructureDerivation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex)
    (triangulation : HasMoiseTriangulation M)
    (simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation)
    (starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation)
    (barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation)
    (regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation)
    (triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation)
    (linkCompatibility : HasMoiseLinkCompatibility M triangulation)
    (plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility)
    (triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation)
    (moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation)
    (triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation)
    (hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas)
    (plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas)
    (plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas)
    (plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas)
    (plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas smoothingTheorem)
    (plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas smoothingTheorem)
    (plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas smoothingTheorem)
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure)
    (smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure)
    (smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure)
    (_smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure)
    (_smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure)
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure)
    (_smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility) : Prop

/--
The proposition that the raw smooth-structure input has been derived from the
named Moise, PL, smoothing, and smooth-atlas sub-obligations.
-/
def SmoothStructureDerivationStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M) : Prop :=
  ∃ localCharts : HasMoiseLocalTriangulationCharts M,
  ∃ locallyFiniteCoverRefinement :
    HasMoiseLocallyFiniteCoverRefinement M localCharts,
  ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
  ∃ compatibleChartTriangulations :
    HasMoiseCompatibleChartTriangulations
      M localCharts simplicialComplex,
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
  ∃ linkCompatibility :
    HasMoiseLinkCompatibility M triangulation,
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
    HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
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
    HasPLMicrobundleSmoothing
      M triangulation plStructure plAtlas plSmoothingExistence
      plSmoothingObstructionVanishing,
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
  ∃ smoothAtlasConstruction :
    HasSmoothAtlasConstruction
      M triangulation plStructure plAtlas plSmoothing smoothStructure,
  ∃ smoothAtlasPLCompatibility :
    HasSmoothAtlasPLCompatibility
      M triangulation plStructure plAtlas plSmoothing smoothStructure,
  ∃ smoothAtlasMaximality :
    HasSmoothAtlasMaximality
      M triangulation plStructure plAtlas plSmoothing smoothStructure,
  ∃ smoothAtlasUniqueness :
    HasSmoothAtlasUniqueness M smoothStructure,
  ∃ smoothStructureUniqueness :
    HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
  ∃ smoothTransitionCompatibility :
    HasSmoothTransitionCompatibility M smoothStructure,
  ∃ smoothAtlasTransitionSmoothness :
    HasSmoothAtlasTransitionSmoothness
      M smoothStructure smoothTransitionCompatibility,
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
      smoothTransitionCompatibility smoothAtlasTransitionSmoothness

/--
The smooth-structure derivation statement is exactly the listed Moise, PL,
smoothing, smooth-atlas, transition, and derivation witness stack.
-/
theorem smoothStructureDerivationStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M) :
    SmoothStructureDerivationStatement M smoothStructure =
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
      ∃ locallyFiniteCoverRefinement :
        HasMoiseLocallyFiniteCoverRefinement M localCharts,
      ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ compatibleChartTriangulations :
        HasMoiseCompatibleChartTriangulations
          M localCharts simplicialComplex,
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
      ∃ linkCompatibility :
        HasMoiseLinkCompatibility M triangulation,
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
        HasPLMicrobundleSmoothing
          M triangulation plStructure plAtlas plSmoothingExistence
          plSmoothingObstructionVanishing,
      ∃ plSmoothing :
        HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ plSmoothingCompatibility :
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingUniqueness :
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingLocalModelCompatibility :
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasPLCompatibility :
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasMaximality :
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasUniqueness :
        HasSmoothAtlasUniqueness M smoothStructure,
      ∃ smoothStructureUniqueness :
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
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
          smoothTransitionCompatibility smoothAtlasTransitionSmoothness) :=
  rfl

/--
Assemble the packaged smooth-structure derivation statement from the named
Moise, PL, smoothing, and smooth-atlas components.
-/
theorem smooth_structure_derivation_statement_of_components
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex)
    (triangulation : HasMoiseTriangulation M)
    (simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation)
    (starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation)
    (barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation)
    (regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation)
    (triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation)
    (linkCompatibility : HasMoiseLinkCompatibility M triangulation)
    (plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility)
    (triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation)
    (moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation)
    (triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation)
    (hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas)
    (plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas)
    (plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas)
    (plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas)
    (plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing)
    (plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure)
    (smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure)
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure)
    (smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility)
    (smoothStructureDerivation :
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
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness) :
    SmoothStructureDerivationStatement M smoothStructure :=
  ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
    compatibleChartTriangulations, triangulation, simplicialApproximation,
    starNeighborhoodBasis, barycentricSubdivision,
    regularNeighborhoodCompatibility, triangulationLocalFiniteness,
    linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
    moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
    plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
    plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
    plAtlasMaximality, plSmoothingExistence, plSmoothingObstructionVanishing,
    plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
    plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
    smoothAtlasConstruction, smoothAtlasPLCompatibility,
    smoothAtlasMaximality, smoothAtlasUniqueness, smoothStructureUniqueness,
    smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
    smoothStructureDerivation⟩

/--
The smooth-structure derivation component assembler is exactly the tuple of
Moise, PL, smoothing, smooth-atlas, transition, and derivation witnesses.
-/
theorem smooth_structure_derivation_statement_of_components_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex)
    (triangulation : HasMoiseTriangulation M)
    (simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation)
    (starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation)
    (barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation)
    (regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation)
    (triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation)
    (linkCompatibility : HasMoiseLinkCompatibility M triangulation)
    (plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility)
    (triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation)
    (moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation)
    (triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation)
    (hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas)
    (plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas)
    (plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas)
    (plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas)
    (plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing)
    (plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure)
    (smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure)
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure)
    (smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility)
    (smoothStructureDerivation :
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
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness) :
    smooth_structure_derivation_statement_of_components M
        localCharts locallyFiniteCoverRefinement simplicialComplex
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
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness
        smoothStructureDerivation =
      (by
        exact ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
          compatibleChartTriangulations, triangulation, simplicialApproximation,
          starNeighborhoodBasis, barycentricSubdivision,
          regularNeighborhoodCompatibility, triangulationLocalFiniteness,
          linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
          moiseCompatibility, triangulationUniqueness,
          hauptvermutungDimensionThree, plStructure, plTransitionCompatibility,
          plAtlas, plManifoldAtlas, plCollarNeighborhoodCompatibility,
          plHomeomorphismCompatibility, plAtlasMaximality,
          plSmoothingExistence, plSmoothingObstructionVanishing,
          plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
          plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
          smoothAtlasConstruction, smoothAtlasPLCompatibility,
          smoothAtlasMaximality, smoothAtlasUniqueness,
          smoothStructureUniqueness, smoothTransitionCompatibility,
          smoothAtlasTransitionSmoothness, smoothStructureDerivation⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped interface that turns the topological smoothability predicate
into the `IsManifold` instance used by `Poincare.Surgery`.
-/
def SmoothabilityBridgeStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∀ smoothStructure : HasThreeManifoldSmoothStructure M,
        SmoothStructureDerivationStatement M smoothStructure →
          IsManifold ThreeManifoldModelWithCorners 1 M

/--
The theorem-shaped smoothability bridge is exactly the universal conversion from
the raw three-manifold smooth structure plus its derivation to the manifold
instance consumed by the surgery layer.
-/
theorem smoothabilityBridgeStatement_eq :
    SmoothabilityBridgeStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          ∀ smoothStructure : HasThreeManifoldSmoothStructure M,
            SmoothStructureDerivationStatement M smoothStructure →
              IsManifold ThreeManifoldModelWithCorners 1 M) :=
  rfl

/--
The theorem-shaped `C∞` smooth-manifold output consumed by the canonical smooth
Poincare statement.
-/
def SmoothabilitySmoothManifoldStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      IsManifold (𝓡 3) ∞ M

/--
The theorem-shaped smooth-manifold output is exactly the universal `C∞`
manifold instance for closed simply connected topological 3-manifolds.
-/
theorem smoothabilitySmoothManifoldStatement_eq :
    SmoothabilitySmoothManifoldStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M) :=
  rfl

/--
Interface certifying that the theorem-shaped smoothability bridge follows from
the constructed smooth atlas.
-/
inductive HasSmoothabilityBridgeDerivation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (_smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure)
    (_manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M) : Prop

/--
Interface certifying that the produced `IsManifold` instance uses the intended
Euclidean 3-manifold model-with-corners.
-/
inductive HasSmoothManifoldModelCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (_bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothStructureDerivation manifoldEvidence) : Prop

/--
Interface certifying that the produced smooth structure is compatible with the
charted-space model used by the surgery layer.
-/
inductive HasSmoothChartCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothStructureDerivation manifoldEvidence)
    (_modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothStructureDerivation manifoldEvidence
        bridgeDerivation) : Prop

/--
Semantic alias for the full smoothability sub-obligation payload exposed by a
smooth-structure derivation statement together with bridge compatibility
evidence.
-/
abbrev SmoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop :=
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ _simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts _simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts _simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ _linkCompatibility :
      HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation _linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation,
    ∃ _moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation,
    ∃ _triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation _triangulationUniqueness,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ _plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ _plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing
        M triangulation plStructure plAtlas _plSmoothingExistence
        _plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ _plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
    ∃ _smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
    ∃ _smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ _smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure _smoothTransitionCompatibility,
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation
        M localCharts _locallyFiniteCoverRefinement _simplicialComplex
        _compatibleChartTriangulations triangulation _simplicialApproximation
        _starNeighborhoodBasis _barycentricSubdivision
        _regularNeighborhoodCompatibility _triangulationLocalFiniteness
        _linkCompatibility _plManifoldRecognition
        _triangulationHomeomorphism _moiseCompatibility
        _triangulationUniqueness _hauptvermutungDimensionThree
        plStructure _plTransitionCompatibility plAtlas _plManifoldAtlas
        _plCollarNeighborhoodCompatibility _plHomeomorphismCompatibility
        _plAtlasMaximality _plSmoothingExistence
        _plSmoothingObstructionVanishing _plMicrobundleSmoothing
        plSmoothing _plSmoothingCompatibility _plSmoothingUniqueness
        _plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        _smoothAtlasMaximality smoothAtlasUniqueness
        _smoothStructureUniqueness _smoothTransitionCompatibility
        _smoothAtlasTransitionSmoothness,
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
        bridgeDerivation modelCompatibility

/--
The smoothability sub-obligation payload alias is definitionally the full
Moise, PL, smoothing, smooth-atlas, smooth-structure derivation, manifold,
bridge, model-compatibility, and chart-compatibility witness stack.
-/
theorem smoothabilitySubobligationsPayload_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothabilitySubobligationsPayload M =
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
      ∃ _locallyFiniteCoverRefinement :
        HasMoiseLocallyFiniteCoverRefinement M localCharts,
      ∃ _simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ _compatibleChartTriangulations :
        HasMoiseCompatibleChartTriangulations
          M localCharts _simplicialComplex,
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ _simplicialApproximation :
        HasMoiseSimplicialApproximation
          M localCharts _simplicialComplex triangulation,
      ∃ _starNeighborhoodBasis :
        HasMoiseStarNeighborhoodBasis M localCharts triangulation,
      ∃ _barycentricSubdivision :
        HasMoiseBarycentricSubdivisionControl M triangulation,
      ∃ _regularNeighborhoodCompatibility :
        HasMoiseRegularNeighborhoodCompatibility M triangulation,
      ∃ _triangulationLocalFiniteness :
        HasMoiseTriangulationLocalFiniteness M triangulation,
      ∃ _linkCompatibility :
        HasMoiseLinkCompatibility M triangulation,
      ∃ _plManifoldRecognition :
        HasMoisePLManifoldRecognition M triangulation _linkCompatibility,
      ∃ _triangulationHomeomorphism :
        HasMoiseTriangulationHomeomorphism M localCharts triangulation,
      ∃ _moiseCompatibility :
        HasMoiseTriangulationCompatibility M localCharts triangulation,
      ∃ _triangulationUniqueness :
        HasMoiseTriangulationUniqueness M triangulation,
      ∃ _hauptvermutungDimensionThree :
        HasMoiseHauptvermutungDimensionThree
          M triangulation _triangulationUniqueness,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ _plTransitionCompatibility :
        HasPLTransitionCompatibility M triangulation plStructure,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ _plManifoldAtlas :
        HasPLManifoldAtlas M triangulation plStructure plAtlas,
      ∃ _plCollarNeighborhoodCompatibility :
        HasPLCollarNeighborhoodCompatibility
          M triangulation plStructure plAtlas,
      ∃ _plHomeomorphismCompatibility :
        HasPLHomeomorphismCompatibility
          M localCharts triangulation plStructure plAtlas,
      ∃ _plAtlasMaximality :
        HasPLAtlasMaximality M triangulation plStructure plAtlas,
      ∃ _plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ _plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing
          M triangulation plStructure plAtlas,
      ∃ _plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing
          M triangulation plStructure plAtlas _plSmoothingExistence
          _plSmoothingObstructionVanishing,
      ∃ plSmoothing :
        HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ _plSmoothingCompatibility :
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ _plSmoothingUniqueness :
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing,
      ∃ _plSmoothingLocalModelCompatibility :
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasPLCompatibility :
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ _smoothAtlasMaximality :
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
      ∃ _smoothStructureUniqueness :
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
      ∃ _smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ _smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure _smoothTransitionCompatibility,
      ∃ _smoothDerivation :
        HasSmoothStructureDerivation
          M localCharts _locallyFiniteCoverRefinement _simplicialComplex
          _compatibleChartTriangulations triangulation _simplicialApproximation
          _starNeighborhoodBasis _barycentricSubdivision
          _regularNeighborhoodCompatibility _triangulationLocalFiniteness
          _linkCompatibility _plManifoldRecognition
          _triangulationHomeomorphism _moiseCompatibility
          _triangulationUniqueness _hauptvermutungDimensionThree
          plStructure _plTransitionCompatibility plAtlas _plManifoldAtlas
          _plCollarNeighborhoodCompatibility _plHomeomorphismCompatibility
          _plAtlasMaximality _plSmoothingExistence
          _plSmoothingObstructionVanishing _plMicrobundleSmoothing
          plSmoothing _plSmoothingCompatibility _plSmoothingUniqueness
          _plSmoothingLocalModelCompatibility smoothStructure
          smoothAtlasConstruction smoothAtlasPLCompatibility
          _smoothAtlasMaximality smoothAtlasUniqueness
          _smoothStructureUniqueness _smoothTransitionCompatibility
          _smoothAtlasTransitionSmoothness,
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
          bridgeDerivation modelCompatibility) :=
  rfl

/--
The smooth-structure derivation statement exposes the full Moise, PL,
smoothing, smooth-atlas, and bridge compatibility sub-obligation stack.
-/
theorem smoothability_subobligations_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence)
    (modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation)
    (chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ _simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts _simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts _simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ _linkCompatibility :
      HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation _linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation,
    ∃ _moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation,
    ∃ _triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation _triangulationUniqueness,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ _plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ _plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing
        M triangulation plStructure plAtlas _plSmoothingExistence
        _plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ _plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
    ∃ _smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
    ∃ _smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ _smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure _smoothTransitionCompatibility,
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation
        M localCharts _locallyFiniteCoverRefinement _simplicialComplex
        _compatibleChartTriangulations triangulation _simplicialApproximation
        _starNeighborhoodBasis _barycentricSubdivision
        _regularNeighborhoodCompatibility _triangulationLocalFiniteness
        _linkCompatibility _plManifoldRecognition
        _triangulationHomeomorphism _moiseCompatibility
        _triangulationUniqueness _hauptvermutungDimensionThree
        plStructure _plTransitionCompatibility plAtlas _plManifoldAtlas
        _plCollarNeighborhoodCompatibility _plHomeomorphismCompatibility
        _plAtlasMaximality _plSmoothingExistence
        _plSmoothingObstructionVanishing _plMicrobundleSmoothing
        plSmoothing _plSmoothingCompatibility _plSmoothingUniqueness
        _plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        _smoothAtlasMaximality smoothAtlasUniqueness
        _smoothStructureUniqueness _smoothTransitionCompatibility
        _smoothAtlasTransitionSmoothness,
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
  rcases smoothDerivationStatement with
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
      plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
      smoothAtlasPLCompatibility, smoothAtlasMaximality,
      smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivation⟩
  let smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure :=
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
      plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
      smoothAtlasPLCompatibility, smoothAtlasMaximality,
      smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivation⟩
  exact ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
    compatibleChartTriangulations, triangulation, simplicialApproximation,
    starNeighborhoodBasis, barycentricSubdivision,
    regularNeighborhoodCompatibility, triangulationLocalFiniteness,
    linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
    moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
    plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
    plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
    plAtlasMaximality, plSmoothingExistence, plSmoothingObstructionVanishing,
    plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
    plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
    smoothStructure, smoothAtlasConstruction, smoothAtlasPLCompatibility,
    smoothAtlasMaximality, smoothAtlasUniqueness, smoothStructureUniqueness,
    smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
    smoothDerivation, smoothDerivationStatement, manifoldEvidence,
    bridgeDerivation, modelCompatibility, chartCompatibility⟩

/--
The smoothability derivation statement bridge exposes exactly the Moise, PL,
smoothing, smooth-atlas, smooth-structure derivation, manifold, bridge, model,
and chart-compatibility witnesses stored in the theorem-shaped inputs.
-/
theorem smoothability_subobligations_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence)
    (modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation)
    (chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility) :
    smoothability_subobligations_of_derivation_statement
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility chartCompatibility =
      (by
        rcases smoothDerivationStatement with
          ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
            compatibleChartTriangulations, triangulation,
            simplicialApproximation, starNeighborhoodBasis,
            barycentricSubdivision, regularNeighborhoodCompatibility,
            triangulationLocalFiniteness, linkCompatibility,
            plManifoldRecognition, triangulationHomeomorphism,
            moiseCompatibility, triangulationUniqueness,
            hauptvermutungDimensionThree, plStructure,
            plTransitionCompatibility, plAtlas, plManifoldAtlas,
            plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
            plAtlasMaximality, plSmoothingExistence,
            plSmoothingObstructionVanishing, plMicrobundleSmoothing,
            plSmoothing, plSmoothingCompatibility, plSmoothingUniqueness,
            plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
            smoothAtlasPLCompatibility, smoothAtlasMaximality,
            smoothAtlasUniqueness, smoothStructureUniqueness,
            smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
            smoothDerivation⟩
        let smoothDerivationStatement :
            SmoothStructureDerivationStatement M smoothStructure :=
          ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
            compatibleChartTriangulations, triangulation,
            simplicialApproximation, starNeighborhoodBasis,
            barycentricSubdivision, regularNeighborhoodCompatibility,
            triangulationLocalFiniteness, linkCompatibility,
            plManifoldRecognition, triangulationHomeomorphism,
            moiseCompatibility, triangulationUniqueness,
            hauptvermutungDimensionThree, plStructure,
            plTransitionCompatibility, plAtlas, plManifoldAtlas,
            plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
            plAtlasMaximality, plSmoothingExistence,
            plSmoothingObstructionVanishing, plMicrobundleSmoothing,
            plSmoothing, plSmoothingCompatibility, plSmoothingUniqueness,
            plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
            smoothAtlasPLCompatibility, smoothAtlasMaximality,
            smoothAtlasUniqueness, smoothStructureUniqueness,
            smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
            smoothDerivation⟩
        exact ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
          compatibleChartTriangulations, triangulation,
          simplicialApproximation, starNeighborhoodBasis,
          barycentricSubdivision, regularNeighborhoodCompatibility,
          triangulationLocalFiniteness, linkCompatibility,
          plManifoldRecognition, triangulationHomeomorphism,
          moiseCompatibility, triangulationUniqueness,
          hauptvermutungDimensionThree, plStructure, plTransitionCompatibility,
          plAtlas, plManifoldAtlas, plCollarNeighborhoodCompatibility,
          plHomeomorphismCompatibility, plAtlasMaximality,
          plSmoothingExistence, plSmoothingObstructionVanishing,
          plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
          plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
          smoothStructure, smoothAtlasConstruction, smoothAtlasPLCompatibility,
          smoothAtlasMaximality, smoothAtlasUniqueness,
          smoothStructureUniqueness, smoothTransitionCompatibility,
          smoothAtlasTransitionSmoothness, smoothDerivation,
          smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
          modelCompatibility, chartCompatibility⟩) := by
  apply Subsingleton.elim

/--
A package for the smoothability input needed by the end-to-end conditional
assembly theorem.
-/
structure SmoothabilityPackage where
  /-- Local Moise triangulation charts for target topological 3-manifolds. -/
  moiseLocalCharts :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLocalTriangulationCharts M
  /-- Locally finite refinement of the local Moise chart cover. -/
  moiseLocallyFiniteCoverRefinement :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLocallyFiniteCoverRefinement M (moiseLocalCharts M)
  /-- Simplicial-complex data underlying the Moise triangulation. -/
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  /-- Compatibility of local chart triangulations before global assembly. -/
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  /-- Triangulation input for target topological 3-manifolds. -/
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  /-- Simplicial-approximation step producing the global triangulation. -/
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  /-- Star-neighborhood basis for the Moise triangulation. -/
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  /-- Barycentric subdivision control for the Moise triangulation. -/
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M (moiseTriangulation M)
  /-- Regular-neighborhood compatibility after subdivision. -/
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M (moiseTriangulation M)
  /-- Local finiteness of the Moise triangulation. -/
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M (moiseTriangulation M)
  /-- Link-compatibility condition for the 3-dimensional triangulation. -/
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M (moiseTriangulation M)
  /-- PL-manifold recognition from the Moise link condition. -/
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)
  /-- Homeomorphism between the topological space and the Moise triangulation. -/
  moiseTriangulationHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  /-- Compatibility between local and global Moise triangulation data. -/
  moiseCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  /-- Uniqueness of the PL structure induced by Moise triangulation. -/
  moiseTriangulationUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationUniqueness M (moiseTriangulation M)
  /-- Dimension-three Hauptvermutung input behind triangulation uniqueness. -/
  moiseHauptvermutungDimensionThree :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseHauptvermutungDimensionThree M
          (moiseTriangulation M)
          (moiseTriangulationUniqueness M)
  /-- Compatible PL structure from the triangulation input. -/
  plStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasCompatiblePLStructure M (moiseTriangulation M)
  /-- PL transition compatibility for the triangulated structure. -/
  plTransitionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLTransitionCompatibility M
          (moiseTriangulation M)
          (plStructure M)
  /-- Compatibility between PL charts and the original topological charts. -/
  plAtlas :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasCompatiblePLAtlas M
          (moiseTriangulation M)
          (plStructure M)
  /-- PL-manifold atlas extracted from the triangulation. -/
  plManifoldAtlas :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLManifoldAtlas M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- PL collar-neighborhood compatibility in the produced atlas. -/
  plCollarNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLCollarNeighborhoodCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Compatibility between the Moise homeomorphism and PL atlas. -/
  plHomeomorphismCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLHomeomorphismCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Maximality of the compatible PL atlas. -/
  plAtlasMaximality :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLAtlasMaximality M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Existence of a smoothing of the compatible PL atlas. -/
  plSmoothingExistence :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingExistence M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Vanishing of the 3-dimensional PL-smoothing obstruction. -/
  plSmoothingObstructionVanishing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingObstructionVanishing M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Microbundle smoothing reduction behind the PL smoothing theorem. -/
  plMicrobundleSmoothing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLMicrobundleSmoothing M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothingExistence M)
          (plSmoothingObstructionVanishing M)
  /-- The 3-dimensional PL-to-smooth smoothing theorem input. -/
  plSmoothing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingTheorem M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Compatibility/uniqueness of the PL smoothing output. -/
  plSmoothingCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
  /-- Uniqueness of the selected PL smoothing. -/
  plSmoothingUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingUniqueness M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
  /-- Compatibility of local smooth models supplied by PL smoothing. -/
  plSmoothingLocalModelCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingLocalModelCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
  /-- Every target topological 3-manifold has the required smooth structure. -/
  smoothStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasThreeManifoldSmoothStructure M
  /-- Smooth atlas construction from PL smoothing data. -/
  smoothAtlasConstruction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasConstruction M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
          (smoothStructure M)
  /-- Compatibility of the produced smooth atlas with the PL atlas. -/
  smoothAtlasPLCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasPLCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
          (smoothStructure M)
  /-- Maximality of the produced smooth atlas. -/
  smoothAtlasMaximality :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasMaximality M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
          (smoothStructure M)
  /-- Uniqueness/compatibility of the produced smooth atlas. -/
  smoothAtlasUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasUniqueness M (smoothStructure M)
  /-- Uniqueness of the smooth structure up to diffeomorphism. -/
  smoothStructureUniquenessUpToDiffeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothStructureUniquenessUpToDiffeomorphism M (smoothStructure M)
  /-- Smooth transition-map compatibility in the produced atlas. -/
  smoothTransitionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothTransitionCompatibility M (smoothStructure M)
  /-- Smoothness of transition maps in the produced atlas. -/
  smoothAtlasTransitionSmoothness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasTransitionSmoothness M
          (smoothStructure M)
          (smoothTransitionCompatibility M)
  /-- Derivation of the smooth structure from the named topological inputs. -/
  smoothStructureDerivation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothStructureDerivation M
          (moiseLocalCharts M)
          (moiseLocallyFiniteCoverRefinement M)
          (moiseSimplicialComplex M)
          (moiseCompatibleChartTriangulations M)
          (moiseTriangulation M)
          (moiseSimplicialApproximation M)
          (moiseStarNeighborhoodBasis M)
          (moiseBarycentricSubdivision M)
          (moiseRegularNeighborhoodCompatibility M)
          (moiseTriangulationLocalFiniteness M)
          (moiseLinkCompatibility M)
          (moisePLManifoldRecognition M)
          (moiseTriangulationHomeomorphism M)
          (moiseCompatibility M)
          (moiseTriangulationUniqueness M)
          (moiseHauptvermutungDimensionThree M)
          (plStructure M)
          (plTransitionCompatibility M)
          (plAtlas M)
          (plManifoldAtlas M)
          (plCollarNeighborhoodCompatibility M)
          (plHomeomorphismCompatibility M)
          (plAtlasMaximality M)
          (plSmoothingExistence M)
          (plSmoothingObstructionVanishing M)
          (plMicrobundleSmoothing M)
          (plSmoothing M)
          (plSmoothingCompatibility M)
          (plSmoothingUniqueness M)
          (plSmoothingLocalModelCompatibility M)
          (smoothStructure M)
          (smoothAtlasConstruction M)
          (smoothAtlasPLCompatibility M)
          (smoothAtlasMaximality M)
          (smoothAtlasUniqueness M)
          (smoothStructureUniquenessUpToDiffeomorphism M)
          (smoothTransitionCompatibility M)
          (smoothAtlasTransitionSmoothness M)
  /-- The smooth structure yields the exact `IsManifold` instance needed below. -/
  bridge : SmoothabilityBridgeStatement.{u}
  /--
  The produced smooth structure supplies the `C∞` manifold instance required by
  the canonical smooth Poincare statement.
  -/
  smoothManifold :
    SmoothabilitySmoothManifoldStatement.{u}
  /-- Derivation of the bridge from the constructed smooth atlas. -/
  bridgeDerivation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        let smoothDerivationStatement :=
          smooth_structure_derivation_statement_of_components M
            (moiseLocalCharts M) (moiseLocallyFiniteCoverRefinement M)
            (moiseSimplicialComplex M) (moiseCompatibleChartTriangulations M)
            (moiseTriangulation M) (moiseSimplicialApproximation M)
            (moiseStarNeighborhoodBasis M) (moiseBarycentricSubdivision M)
            (moiseRegularNeighborhoodCompatibility M)
            (moiseTriangulationLocalFiniteness M)
            (moiseLinkCompatibility M) (moisePLManifoldRecognition M)
            (moiseTriangulationHomeomorphism M) (moiseCompatibility M)
            (moiseTriangulationUniqueness M)
            (moiseHauptvermutungDimensionThree M)
            (plStructure M) (plTransitionCompatibility M) (plAtlas M)
            (plManifoldAtlas M) (plCollarNeighborhoodCompatibility M)
            (plHomeomorphismCompatibility M) (plAtlasMaximality M)
            (plSmoothingExistence M) (plSmoothingObstructionVanishing M)
            (plMicrobundleSmoothing M) (plSmoothing M)
            (plSmoothingCompatibility M) (plSmoothingUniqueness M)
            (plSmoothingLocalModelCompatibility M) (smoothStructure M)
            (smoothAtlasConstruction M) (smoothAtlasPLCompatibility M)
            (smoothAtlasMaximality M) (smoothAtlasUniqueness M)
            (smoothStructureUniquenessUpToDiffeomorphism M)
            (smoothTransitionCompatibility M)
            (smoothAtlasTransitionSmoothness M) (smoothStructureDerivation M)
        HasSmoothabilityBridgeDerivation M
          (smoothStructure M)
          smoothDerivationStatement
          (bridge M (smoothStructure M) smoothDerivationStatement)
  /-- Compatibility of the produced manifold instance with the target model. -/
  smoothModelCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        let smoothDerivationStatement :=
          smooth_structure_derivation_statement_of_components M
            (moiseLocalCharts M) (moiseLocallyFiniteCoverRefinement M)
            (moiseSimplicialComplex M) (moiseCompatibleChartTriangulations M)
            (moiseTriangulation M) (moiseSimplicialApproximation M)
            (moiseStarNeighborhoodBasis M) (moiseBarycentricSubdivision M)
            (moiseRegularNeighborhoodCompatibility M)
            (moiseTriangulationLocalFiniteness M)
            (moiseLinkCompatibility M) (moisePLManifoldRecognition M)
            (moiseTriangulationHomeomorphism M) (moiseCompatibility M)
            (moiseTriangulationUniqueness M)
            (moiseHauptvermutungDimensionThree M)
            (plStructure M) (plTransitionCompatibility M) (plAtlas M)
            (plManifoldAtlas M) (plCollarNeighborhoodCompatibility M)
            (plHomeomorphismCompatibility M) (plAtlasMaximality M)
            (plSmoothingExistence M) (plSmoothingObstructionVanishing M)
            (plMicrobundleSmoothing M) (plSmoothing M)
            (plSmoothingCompatibility M) (plSmoothingUniqueness M)
            (plSmoothingLocalModelCompatibility M) (smoothStructure M)
            (smoothAtlasConstruction M) (smoothAtlasPLCompatibility M)
            (smoothAtlasMaximality M) (smoothAtlasUniqueness M)
            (smoothStructureUniquenessUpToDiffeomorphism M)
            (smoothTransitionCompatibility M)
            (smoothAtlasTransitionSmoothness M) (smoothStructureDerivation M)
        HasSmoothManifoldModelCompatibility M
          (smoothStructure M)
          smoothDerivationStatement
          (bridge M (smoothStructure M) smoothDerivationStatement)
          (bridgeDerivation M)
  /-- Compatibility of the produced manifold evidence with the chart model. -/
  chartCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        let smoothDerivationStatement :=
          smooth_structure_derivation_statement_of_components M
            (moiseLocalCharts M) (moiseLocallyFiniteCoverRefinement M)
            (moiseSimplicialComplex M) (moiseCompatibleChartTriangulations M)
            (moiseTriangulation M) (moiseSimplicialApproximation M)
            (moiseStarNeighborhoodBasis M) (moiseBarycentricSubdivision M)
            (moiseRegularNeighborhoodCompatibility M)
            (moiseTriangulationLocalFiniteness M)
            (moiseLinkCompatibility M) (moisePLManifoldRecognition M)
            (moiseTriangulationHomeomorphism M) (moiseCompatibility M)
            (moiseTriangulationUniqueness M)
            (moiseHauptvermutungDimensionThree M)
            (plStructure M) (plTransitionCompatibility M) (plAtlas M)
            (plManifoldAtlas M) (plCollarNeighborhoodCompatibility M)
            (plHomeomorphismCompatibility M) (plAtlasMaximality M)
            (plSmoothingExistence M) (plSmoothingObstructionVanishing M)
            (plMicrobundleSmoothing M) (plSmoothing M)
            (plSmoothingCompatibility M) (plSmoothingUniqueness M)
            (plSmoothingLocalModelCompatibility M) (smoothStructure M)
            (smoothAtlasConstruction M) (smoothAtlasPLCompatibility M)
            (smoothAtlasMaximality M) (smoothAtlasUniqueness M)
            (smoothStructureUniquenessUpToDiffeomorphism M)
            (smoothTransitionCompatibility M)
            (smoothAtlasTransitionSmoothness M) (smoothStructureDerivation M)
        HasSmoothChartCompatibility M
          (smoothStructure M)
          smoothDerivationStatement
          (bridge M (smoothStructure M) smoothDerivationStatement)
          (bridgeDerivation M)
          (smoothModelCompatibility M)

/-- A completed smoothability package supplies local Moise chart evidence. -/
theorem moise_local_charts_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLocalTriangulationCharts M :=
  package.moiseLocalCharts M

/-- The named Moise local-chart projection is the stored package field. -/
theorem moise_local_charts_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_local_charts_of_smoothability_package package M =
      package.moiseLocalCharts M :=
  rfl

/-- A completed smoothability package supplies locally finite chart refinement. -/
theorem moise_locally_finite_cover_refinement_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLocallyFiniteCoverRefinement M
      (moise_local_charts_of_smoothability_package package M) :=
  package.moiseLocallyFiniteCoverRefinement M

/-- The named locally finite cover-refinement projection is the stored package field. -/
theorem moise_locally_finite_cover_refinement_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_locally_finite_cover_refinement_of_smoothability_package package M =
      package.moiseLocallyFiniteCoverRefinement M :=
  rfl

/-- A completed smoothability package supplies Moise simplicial-complex evidence. -/
theorem moise_simplicial_complex_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseSimplicialComplex M
      (moise_local_charts_of_smoothability_package package M) :=
  package.moiseSimplicialComplex M

/-- The named Moise simplicial-complex projection is the stored package field. -/
theorem moise_simplicial_complex_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_simplicial_complex_of_smoothability_package package M =
      package.moiseSimplicialComplex M :=
  rfl

/-- A completed smoothability package supplies compatible chart triangulations. -/
theorem moise_compatible_chart_triangulations_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseCompatibleChartTriangulations M
      (moise_local_charts_of_smoothability_package package M)
      (moise_simplicial_complex_of_smoothability_package package M) :=
  package.moiseCompatibleChartTriangulations M

/-- The named compatible chart-triangulations projection is the stored package field. -/
theorem moise_compatible_chart_triangulations_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_compatible_chart_triangulations_of_smoothability_package package M =
      package.moiseCompatibleChartTriangulations M :=
  rfl

/-- A completed smoothability package supplies Moise triangulation evidence. -/
theorem moise_triangulation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulation M :=
  package.moiseTriangulation M

/-- The named Moise triangulation projection is the stored package field. -/
theorem moise_triangulation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_of_smoothability_package package M =
      package.moiseTriangulation M :=
  rfl

/-- A completed smoothability package supplies simplicial-approximation evidence. -/
theorem moise_simplicial_approximation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseSimplicialApproximation M
      (moise_local_charts_of_smoothability_package package M)
      (moise_simplicial_complex_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseSimplicialApproximation M

/-- The named simplicial-approximation projection is the stored package field. -/
theorem moise_simplicial_approximation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_simplicial_approximation_of_smoothability_package package M =
      package.moiseSimplicialApproximation M :=
  rfl

/-- A completed smoothability package supplies a Moise star-neighborhood basis. -/
theorem moise_star_neighborhood_basis_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseStarNeighborhoodBasis M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseStarNeighborhoodBasis M

/-- The named star-neighborhood basis projection is the stored package field. -/
theorem moise_star_neighborhood_basis_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_star_neighborhood_basis_of_smoothability_package package M =
      package.moiseStarNeighborhoodBasis M :=
  rfl

/-- A completed smoothability package supplies barycentric subdivision control. -/
theorem moise_barycentric_subdivision_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseBarycentricSubdivisionControl M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseBarycentricSubdivision M

/-- The named barycentric subdivision projection is the stored package field. -/
theorem moise_barycentric_subdivision_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_barycentric_subdivision_of_smoothability_package package M =
      package.moiseBarycentricSubdivision M :=
  rfl

/-- A completed smoothability package supplies regular-neighborhood compatibility. -/
theorem moise_regular_neighborhood_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseRegularNeighborhoodCompatibility M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseRegularNeighborhoodCompatibility M

/-- The named regular-neighborhood compatibility projection is the stored package field. -/
theorem moise_regular_neighborhood_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_regular_neighborhood_compatibility_of_smoothability_package package M =
      package.moiseRegularNeighborhoodCompatibility M :=
  rfl

/-- A completed smoothability package supplies local-finiteness evidence. -/
theorem moise_triangulation_local_finiteness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationLocalFiniteness M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseTriangulationLocalFiniteness M

/-- The named triangulation local-finiteness projection is the stored package field. -/
theorem moise_triangulation_local_finiteness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_local_finiteness_of_smoothability_package package M =
      package.moiseTriangulationLocalFiniteness M :=
  rfl

/-- A completed smoothability package supplies the triangulation link condition. -/
theorem moise_link_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLinkCompatibility M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseLinkCompatibility M

/-- The named link-compatibility projection is the stored package field. -/
theorem moise_link_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_link_compatibility_of_smoothability_package package M =
      package.moiseLinkCompatibility M :=
  rfl

/-- A completed smoothability package recognizes the triangulation as a PL manifold. -/
theorem moise_pl_manifold_recognition_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoisePLManifoldRecognition M
      (moise_triangulation_of_smoothability_package package M)
      (moise_link_compatibility_of_smoothability_package package M) :=
  package.moisePLManifoldRecognition M

/-- The named PL-manifold recognition projection is the stored package field. -/
theorem moise_pl_manifold_recognition_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_pl_manifold_recognition_of_smoothability_package package M =
      package.moisePLManifoldRecognition M :=
  rfl

/-- A completed smoothability package supplies the triangulation homeomorphism. -/
theorem moise_triangulation_homeomorphism_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationHomeomorphism M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseTriangulationHomeomorphism M

/-- The named triangulation-homeomorphism projection is the stored package field. -/
theorem moise_triangulation_homeomorphism_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_homeomorphism_of_smoothability_package package M =
      package.moiseTriangulationHomeomorphism M :=
  rfl

/-- A completed smoothability package supplies Moise compatibility evidence. -/
theorem moise_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationCompatibility M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseCompatibility M

/-- The named Moise compatibility projection is the stored package field. -/
theorem moise_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_compatibility_of_smoothability_package package M =
      package.moiseCompatibility M :=
  rfl

/-- A completed smoothability package supplies Moise triangulation uniqueness. -/
theorem moise_triangulation_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationUniqueness M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseTriangulationUniqueness M

/-- The named Moise triangulation-uniqueness projection is the stored package field. -/
theorem moise_triangulation_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_uniqueness_of_smoothability_package package M =
      package.moiseTriangulationUniqueness M :=
  rfl

/-- A completed smoothability package supplies the dimension-three Hauptvermutung input. -/
theorem moise_hauptvermutung_dimension_three_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseHauptvermutungDimensionThree M
      (moise_triangulation_of_smoothability_package package M)
      (moise_triangulation_uniqueness_of_smoothability_package package M) :=
  package.moiseHauptvermutungDimensionThree M

/-- The named dimension-three Hauptvermutung projection is the stored package field. -/
theorem moise_hauptvermutung_dimension_three_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_hauptvermutung_dimension_three_of_smoothability_package package M =
      package.moiseHauptvermutungDimensionThree M :=
  rfl

/-- A completed smoothability package supplies compatible PL-structure evidence. -/
theorem pl_structure_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasCompatiblePLStructure M
      (moise_triangulation_of_smoothability_package package M) :=
  package.plStructure M

/-- The named compatible PL-structure projection is the stored package field. -/
theorem pl_structure_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_structure_of_smoothability_package package M =
      package.plStructure M :=
  rfl

/-- A completed smoothability package supplies PL transition compatibility. -/
theorem pl_transition_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLTransitionCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M) :=
  package.plTransitionCompatibility M

/-- The named PL transition-compatibility projection is the stored package field. -/
theorem pl_transition_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_transition_compatibility_of_smoothability_package package M =
      package.plTransitionCompatibility M :=
  rfl

/-- A completed smoothability package supplies compatible PL-atlas evidence. -/
theorem pl_atlas_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasCompatiblePLAtlas M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M) :=
  package.plAtlas M

/-- The named compatible PL-atlas projection is the stored package field. -/
theorem pl_atlas_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_atlas_of_smoothability_package package M =
      package.plAtlas M :=
  rfl

/-- A completed smoothability package supplies the PL-manifold atlas. -/
theorem pl_manifold_atlas_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLManifoldAtlas M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plManifoldAtlas M

/-- The named PL-manifold atlas projection is the stored package field. -/
theorem pl_manifold_atlas_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_manifold_atlas_of_smoothability_package package M =
      package.plManifoldAtlas M :=
  rfl

/-- A completed smoothability package supplies PL collar-neighborhood compatibility. -/
theorem pl_collar_neighborhood_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLCollarNeighborhoodCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plCollarNeighborhoodCompatibility M

/-- The named PL collar-neighborhood compatibility projection is the stored package field. -/
theorem pl_collar_neighborhood_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_collar_neighborhood_compatibility_of_smoothability_package package M =
      package.plCollarNeighborhoodCompatibility M :=
  rfl

/-- A completed smoothability package supplies Moise-to-PL compatibility. -/
theorem pl_homeomorphism_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLHomeomorphismCompatibility M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plHomeomorphismCompatibility M

/-- The named PL homeomorphism-compatibility projection is the stored package field. -/
theorem pl_homeomorphism_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_homeomorphism_compatibility_of_smoothability_package package M =
      package.plHomeomorphismCompatibility M :=
  rfl

/-- A completed smoothability package supplies PL atlas maximality. -/
theorem pl_atlas_maximality_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLAtlasMaximality M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plAtlasMaximality M

/-- The named PL-atlas maximality projection is the stored package field. -/
theorem pl_atlas_maximality_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_atlas_maximality_of_smoothability_package package M =
      package.plAtlasMaximality M :=
  rfl

/-- A completed smoothability package supplies PL smoothing existence. -/
theorem pl_smoothing_existence_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingExistence M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plSmoothingExistence M

/-- The named PL-smoothing existence projection is the stored package field. -/
theorem pl_smoothing_existence_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_existence_of_smoothability_package package M =
      package.plSmoothingExistence M :=
  rfl

/-- A completed smoothability package supplies PL-smoothing obstruction vanishing. -/
theorem pl_smoothing_obstruction_vanishing_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingObstructionVanishing M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plSmoothingObstructionVanishing M

/-- The named PL-smoothing obstruction-vanishing projection is the stored package field. -/
theorem pl_smoothing_obstruction_vanishing_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_obstruction_vanishing_of_smoothability_package package M =
      package.plSmoothingObstructionVanishing M :=
  rfl

/-- A completed smoothability package supplies PL microbundle smoothing evidence. -/
theorem pl_microbundle_smoothing_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLMicrobundleSmoothing M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_existence_of_smoothability_package package M)
      (pl_smoothing_obstruction_vanishing_of_smoothability_package package M) :=
  package.plMicrobundleSmoothing M

/-- The named PL microbundle-smoothing projection is the stored package field. -/
theorem pl_microbundle_smoothing_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_microbundle_smoothing_of_smoothability_package package M =
      package.plMicrobundleSmoothing M :=
  rfl

/-- A completed smoothability package supplies PL-smoothing theorem evidence. -/
theorem pl_smoothing_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingTheorem M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plSmoothing M

/-- The named PL-smoothing theorem projection is the stored package field. -/
theorem pl_smoothing_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_of_smoothability_package package M =
      package.plSmoothing M :=
  rfl

/-- A completed smoothability package supplies PL smoothing compatibility. -/
theorem pl_smoothing_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M) :=
  package.plSmoothingCompatibility M

/-- The named PL-smoothing compatibility projection is the stored package field. -/
theorem pl_smoothing_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_compatibility_of_smoothability_package package M =
      package.plSmoothingCompatibility M :=
  rfl

/-- A completed smoothability package supplies PL smoothing uniqueness. -/
theorem pl_smoothing_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingUniqueness M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M) :=
  package.plSmoothingUniqueness M

/-- The named PL-smoothing uniqueness projection is the stored package field. -/
theorem pl_smoothing_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_uniqueness_of_smoothability_package package M =
      package.plSmoothingUniqueness M :=
  rfl

/-- A completed smoothability package supplies PL-smoothing local-model compatibility. -/
theorem pl_smoothing_local_model_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingLocalModelCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M) :=
  package.plSmoothingLocalModelCompatibility M

/-- The named PL-smoothing local-model compatibility projection is the stored package field. -/
theorem pl_smoothing_local_model_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_local_model_compatibility_of_smoothability_package package M =
      package.plSmoothingLocalModelCompatibility M :=
  rfl

/-- A completed smoothability package supplies the raw smooth-structure input. -/
theorem smooth_structure_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasThreeManifoldSmoothStructure M :=
  package.smoothStructure M

/-- The named smooth-structure projection is the stored package field. -/
theorem smooth_structure_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_of_smoothability_package package M =
      package.smoothStructure M :=
  rfl

/-- A completed smoothability package supplies smooth atlas construction. -/
theorem smooth_atlas_construction_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasConstruction M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothAtlasConstruction M

/-- The named smooth-atlas construction projection is the stored package field. -/
theorem smooth_atlas_construction_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_construction_of_smoothability_package package M =
      package.smoothAtlasConstruction M :=
  rfl

/-- A completed smoothability package supplies smooth-atlas/PL-atlas compatibility. -/
theorem smooth_atlas_pl_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasPLCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothAtlasPLCompatibility M

/-- The named smooth-atlas/PL-atlas compatibility projection is the stored package field. -/
theorem smooth_atlas_pl_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_pl_compatibility_of_smoothability_package package M =
      package.smoothAtlasPLCompatibility M :=
  rfl

/-- A completed smoothability package supplies smooth atlas maximality. -/
theorem smooth_atlas_maximality_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasMaximality M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothAtlasMaximality M

/-- The named smooth-atlas maximality projection is the stored package field. -/
theorem smooth_atlas_maximality_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_maximality_of_smoothability_package package M =
      package.smoothAtlasMaximality M :=
  rfl

/-- A completed smoothability package supplies smooth atlas uniqueness evidence. -/
theorem smooth_atlas_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasUniqueness M
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothAtlasUniqueness M

/-- The named smooth-atlas uniqueness projection is the stored package field. -/
theorem smooth_atlas_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_uniqueness_of_smoothability_package package M =
      package.smoothAtlasUniqueness M :=
  rfl

/-- A completed smoothability package supplies smooth-structure uniqueness. -/
theorem smooth_structure_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothStructureUniquenessUpToDiffeomorphism M
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothStructureUniquenessUpToDiffeomorphism M

/-- The named smooth-structure uniqueness projection is the stored package field. -/
theorem smooth_structure_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_uniqueness_of_smoothability_package package M =
      package.smoothStructureUniquenessUpToDiffeomorphism M :=
  rfl

/-- A completed smoothability package supplies smooth transition compatibility. -/
theorem smooth_transition_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothTransitionCompatibility M
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothTransitionCompatibility M

/-- The named smooth-transition compatibility projection is the stored package field. -/
theorem smooth_transition_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_transition_compatibility_of_smoothability_package package M =
      package.smoothTransitionCompatibility M :=
  rfl

/-- A completed smoothability package supplies smooth transition-map smoothness. -/
theorem smooth_atlas_transition_smoothness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasTransitionSmoothness M
      (smooth_structure_of_smoothability_package package M)
      (smooth_transition_compatibility_of_smoothability_package package M) :=
  package.smoothAtlasTransitionSmoothness M

/-- The named smooth transition-map smoothness projection is the stored package field. -/
theorem smooth_atlas_transition_smoothness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_transition_smoothness_of_smoothability_package package M =
      package.smoothAtlasTransitionSmoothness M :=
  rfl

/--
A completed smoothability package supplies the derivation from triangulation and
PL structure to the smooth structure.
-/
theorem smooth_structure_derivation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothStructureDerivation M
      (moise_local_charts_of_smoothability_package package M)
      (moise_locally_finite_cover_refinement_of_smoothability_package package M)
      (moise_simplicial_complex_of_smoothability_package package M)
      (moise_compatible_chart_triangulations_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M)
      (moise_simplicial_approximation_of_smoothability_package package M)
      (moise_star_neighborhood_basis_of_smoothability_package package M)
      (moise_barycentric_subdivision_of_smoothability_package package M)
      (moise_regular_neighborhood_compatibility_of_smoothability_package package M)
      (moise_triangulation_local_finiteness_of_smoothability_package package M)
      (moise_link_compatibility_of_smoothability_package package M)
      (moise_pl_manifold_recognition_of_smoothability_package package M)
      (moise_triangulation_homeomorphism_of_smoothability_package package M)
      (moise_compatibility_of_smoothability_package package M)
      (moise_triangulation_uniqueness_of_smoothability_package package M)
      (moise_hauptvermutung_dimension_three_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_transition_compatibility_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_manifold_atlas_of_smoothability_package package M)
      (pl_collar_neighborhood_compatibility_of_smoothability_package package M)
      (pl_homeomorphism_compatibility_of_smoothability_package package M)
      (pl_atlas_maximality_of_smoothability_package package M)
      (pl_smoothing_existence_of_smoothability_package package M)
      (pl_smoothing_obstruction_vanishing_of_smoothability_package package M)
      (pl_microbundle_smoothing_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (pl_smoothing_compatibility_of_smoothability_package package M)
      (pl_smoothing_uniqueness_of_smoothability_package package M)
      (pl_smoothing_local_model_compatibility_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M)
      (smooth_atlas_construction_of_smoothability_package package M)
      (smooth_atlas_pl_compatibility_of_smoothability_package package M)
      (smooth_atlas_maximality_of_smoothability_package package M)
      (smooth_atlas_uniqueness_of_smoothability_package package M)
      (smooth_structure_uniqueness_of_smoothability_package package M)
      (smooth_transition_compatibility_of_smoothability_package package M)
      (smooth_atlas_transition_smoothness_of_smoothability_package package M) :=
  package.smoothStructureDerivation M

/-- The named smooth-structure derivation projection is the stored package field. -/
theorem smooth_structure_derivation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_derivation_of_smoothability_package package M =
      package.smoothStructureDerivation M :=
  rfl

/-- A completed smoothability package packages the smooth-structure derivation statement. -/
theorem smooth_structure_derivation_statement_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothStructureDerivationStatement M
      (smooth_structure_of_smoothability_package package M) :=
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

/--
The package-level smooth-structure derivation statement is exactly the component
assembler applied to the stored Moise, PL, smoothing, smooth-atlas, and
smooth-structure derivation fields.
-/
theorem smooth_structure_derivation_statement_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_derivation_statement_of_smoothability_package package M =
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
        (package.smoothStructureDerivation M) :=
  rfl

/--
A completed smoothability package exposes the component smooth-structure
derivation certificate together with the theorem-shaped derivation statement.
-/
theorem smoothability_smooth_structure_statement_payload_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation M
        (moise_local_charts_of_smoothability_package package M)
        (moise_locally_finite_cover_refinement_of_smoothability_package
          package M)
        (moise_simplicial_complex_of_smoothability_package package M)
        (moise_compatible_chart_triangulations_of_smoothability_package
          package M)
        (moise_triangulation_of_smoothability_package package M)
        (moise_simplicial_approximation_of_smoothability_package package M)
        (moise_star_neighborhood_basis_of_smoothability_package package M)
        (moise_barycentric_subdivision_of_smoothability_package package M)
        (moise_regular_neighborhood_compatibility_of_smoothability_package
          package M)
        (moise_triangulation_local_finiteness_of_smoothability_package
          package M)
        (moise_link_compatibility_of_smoothability_package package M)
        (moise_pl_manifold_recognition_of_smoothability_package package M)
        (moise_triangulation_homeomorphism_of_smoothability_package package M)
        (moise_compatibility_of_smoothability_package package M)
        (moise_triangulation_uniqueness_of_smoothability_package package M)
        (moise_hauptvermutung_dimension_three_of_smoothability_package
          package M)
        (pl_structure_of_smoothability_package package M)
        (pl_transition_compatibility_of_smoothability_package package M)
        (pl_atlas_of_smoothability_package package M)
        (pl_manifold_atlas_of_smoothability_package package M)
        (pl_collar_neighborhood_compatibility_of_smoothability_package
          package M)
        (pl_homeomorphism_compatibility_of_smoothability_package package M)
        (pl_atlas_maximality_of_smoothability_package package M)
        (pl_smoothing_existence_of_smoothability_package package M)
        (pl_smoothing_obstruction_vanishing_of_smoothability_package package M)
        (pl_microbundle_smoothing_of_smoothability_package package M)
        (pl_smoothing_of_smoothability_package package M)
        (pl_smoothing_compatibility_of_smoothability_package package M)
        (pl_smoothing_uniqueness_of_smoothability_package package M)
        (pl_smoothing_local_model_compatibility_of_smoothability_package
          package M)
        (smooth_structure_of_smoothability_package package M)
        (smooth_atlas_construction_of_smoothability_package package M)
        (smooth_atlas_pl_compatibility_of_smoothability_package package M)
        (smooth_atlas_maximality_of_smoothability_package package M)
        (smooth_atlas_uniqueness_of_smoothability_package package M)
        (smooth_structure_uniqueness_of_smoothability_package package M)
        (smooth_transition_compatibility_of_smoothability_package package M)
        (smooth_atlas_transition_smoothness_of_smoothability_package package M),
      SmoothStructureDerivationStatement M
        (smooth_structure_of_smoothability_package package M) := by
  exact ⟨smooth_structure_derivation_of_smoothability_package package M,
    smooth_structure_derivation_statement_of_smoothability_package package M⟩

/--
The smooth-structure statement payload is the projected derivation evidence
paired with the theorem-shaped derivation statement.
-/
theorem smoothability_smooth_structure_statement_payload_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_structure_statement_payload_of_smoothability_package
      package M =
      ⟨smooth_structure_derivation_of_smoothability_package package M,
        smooth_structure_derivation_statement_of_smoothability_package
          package M⟩ := by
  apply Subsingleton.elim

/-- A completed smoothability package supplies the bridge theorem interface. -/
theorem smoothability_bridge_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    SmoothabilityBridgeStatement.{u} :=
  package.bridge

/-- The named smoothability bridge projection is the stored package field. -/
theorem smoothability_bridge_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothability_bridge_of_smoothability_package package = package.bridge :=
  rfl

/--
A completed smoothability package supplies the theorem-shaped `C∞`
smooth-manifold statement.
-/
theorem smoothability_smooth_manifold_statement_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    SmoothabilitySmoothManifoldStatement.{u} :=
  package.smoothManifold

/-- The named `C∞` smooth-manifold projection is the stored package field. -/
theorem smoothability_smooth_manifold_statement_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothability_smooth_manifold_statement_of_smoothability_package package =
      package.smoothManifold :=
  rfl

/-- Apply the smoothability bridge to explicit smooth-structure evidence. -/
theorem is_manifold_of_smoothability_bridge
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure) :
    IsManifold ThreeManifoldModelWithCorners 1 M :=
  smoothability_bridge_of_smoothability_package package M smoothStructure
    smoothStructureDerivation

/--
The explicit bridge application is the stored bridge applied to the supplied
smooth-structure evidence.
-/
theorem is_manifold_of_smoothability_bridge_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure) :
    is_manifold_of_smoothability_bridge
      package M smoothStructure smoothStructureDerivation =
      package.bridge M smoothStructure smoothStructureDerivation :=
  rfl

/-- A completed smoothability package supplies the raw regularity bridge. -/
theorem smoothable_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        IsManifold ThreeManifoldModelWithCorners 1 M := by
  intro M _ _ _ _ _
  exact is_manifold_of_smoothability_bridge package M
    (smooth_structure_of_smoothability_package package M)
    (smooth_structure_derivation_statement_of_smoothability_package package M)

/--
The raw surgery-model smoothability projection is the stored bridge applied to
the package's smooth structure and derivation statement.
-/
theorem smoothable_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothable_of_smoothability_package package =
      fun (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M] =>
          package.bridge M
            (smooth_structure_of_smoothability_package package M)
            (smooth_structure_derivation_statement_of_smoothability_package
              package M) := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies the `C∞` manifold instance consumed by
the canonical smooth Poincare statement.
-/
theorem smooth_manifold_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        IsManifold (𝓡 3) ∞ M :=
  smoothability_smooth_manifold_statement_of_smoothability_package package

/-- The named canonical smooth-manifold projection is the stored package field. -/
theorem smooth_manifold_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smooth_manifold_of_smoothability_package package =
      package.smoothManifold := by
  apply Subsingleton.elim

/--
A completed smoothability package exposes both smoothability theorem outputs:
the C¹ surgery-model bridge and the separate `C∞` canonical smooth-manifold
statement.
-/
theorem smoothability_smooth_manifold_payload_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    SmoothabilityBridgeStatement.{u} ∧
      SmoothabilitySmoothManifoldStatement.{u} :=
  ⟨smoothability_bridge_of_smoothability_package package,
    smoothability_smooth_manifold_statement_of_smoothability_package package⟩

/--
The smooth-manifold payload is the pair of stored theorem-shaped smoothability
outputs.
-/
theorem smoothability_smooth_manifold_payload_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothability_smooth_manifold_payload_of_smoothability_package package =
      ⟨package.bridge, package.smoothManifold⟩ := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies derivation evidence for the bridge
applied to its projected smooth structure.
-/
theorem smoothability_bridge_derivation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothabilityBridgeDerivation M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      (smoothable_of_smoothability_package package M) :=
  package.bridgeDerivation M

/-- The named bridge-derivation projection is the stored package field. -/
theorem smoothability_bridge_derivation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_bridge_derivation_of_smoothability_package package M =
      package.bridgeDerivation M := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies compatibility of the produced
manifold instance with the target smooth model.
-/
theorem smooth_model_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothManifoldModelCompatibility M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      (smoothable_of_smoothability_package package M)
      (smoothability_bridge_derivation_of_smoothability_package package M) :=
  package.smoothModelCompatibility M

/-- The named model-compatibility projection is the stored package field. -/
theorem smooth_model_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_model_compatibility_of_smoothability_package package M =
      package.smoothModelCompatibility M := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies compatibility of the produced
manifold evidence with the surgery chart model.
-/
theorem smooth_chart_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothChartCompatibility M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      (smoothable_of_smoothability_package package M)
      (smoothability_bridge_derivation_of_smoothability_package package M)
      (smooth_model_compatibility_of_smoothability_package package M) :=
  package.chartCompatibility M

/-- The named chart-compatibility projection is the stored package field. -/
theorem smooth_chart_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_chart_compatibility_of_smoothability_package package M =
      package.chartCompatibility M := by
  apply Subsingleton.elim

/--
A completed smoothability package exposes the bridge output, compatibility
certificates, and full smoothability sub-obligation payload.
-/
theorem smoothability_bridge_payload_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ bridgeDerivation :
      HasSmoothabilityBridgeDerivation M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package
          package M)
        manifoldEvidence,
    ∃ modelCompatibility :
      HasSmoothManifoldModelCompatibility M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package
          package M)
        manifoldEvidence
        bridgeDerivation,
    ∃ _chartCompatibility :
      HasSmoothChartCompatibility M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package
          package M)
        manifoldEvidence
        bridgeDerivation
        modelCompatibility,
      SmoothabilitySubobligationsPayload M := by
  let manifoldEvidence := smoothable_of_smoothability_package package M
  let bridgeDerivation :=
    smoothability_bridge_derivation_of_smoothability_package package M
  let modelCompatibility :=
    smooth_model_compatibility_of_smoothability_package package M
  let chartCompatibility :=
    smooth_chart_compatibility_of_smoothability_package package M
  exact ⟨manifoldEvidence, bridgeDerivation, modelCompatibility,
    chartCompatibility,
    smoothability_subobligations_of_derivation_statement M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      manifoldEvidence bridgeDerivation modelCompatibility
      chartCompatibility⟩

/--
The bridge payload is the named manifold evidence, bridge derivation,
compatibility evidence, and sub-obligation payload assembled from them.
-/
theorem smoothability_bridge_payload_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_bridge_payload_of_smoothability_package package M =
      ⟨smoothable_of_smoothability_package package M,
        smoothability_bridge_derivation_of_smoothability_package package M,
        smooth_model_compatibility_of_smoothability_package package M,
        smooth_chart_compatibility_of_smoothability_package package M,
        smoothability_subobligations_of_derivation_statement M
          (smooth_structure_of_smoothability_package package M)
          (smooth_structure_derivation_statement_of_smoothability_package
            package M)
          (smoothable_of_smoothability_package package M)
          (smoothability_bridge_derivation_of_smoothability_package package M)
          (smooth_model_compatibility_of_smoothability_package package M)
          (smooth_chart_compatibility_of_smoothability_package package M)⟩ := by
  apply Subsingleton.elim

/--
A completed smoothability package directly exposes the named smoothability
sub-obligation payload for each topological three-manifold input.
-/
theorem smoothability_subobligations_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothabilitySubobligationsPayload M :=
  smoothability_subobligations_of_derivation_statement M
    (smooth_structure_of_smoothability_package package M)
    (smooth_structure_derivation_statement_of_smoothability_package package M)
    (smoothable_of_smoothability_package package M)
    (smoothability_bridge_derivation_of_smoothability_package package M)
    (smooth_model_compatibility_of_smoothability_package package M)
    (smooth_chart_compatibility_of_smoothability_package package M)

/--
The package-level smoothability sub-obligation bridge is exactly the derivation
statement bridge applied to the package projections.
-/
theorem smoothability_subobligations_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_of_smoothability_package package M =
      smoothability_subobligations_of_derivation_statement M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package package M)
        (smoothable_of_smoothability_package package M)
        (smoothability_bridge_derivation_of_smoothability_package package M)
        (smooth_model_compatibility_of_smoothability_package package M)
        (smooth_chart_compatibility_of_smoothability_package package M) := by
  apply Subsingleton.elim

end Poincare
